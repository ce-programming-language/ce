open Ce_compiler
open Ce_parser
open Ce_lexer
open Ce_parser.Ast
open Cmdliner
open Llvm_target

let read file = In_channel.with_open_text file In_channel.input_all

let parse filepath src =
  Ce_lexer.Lexer.reset_state ();
  let lexbuf = Lexing.from_string src in
  Lexing.set_filename lexbuf filepath;
  try Parser.prog Lexer.tokenize lexbuf
  with Parser.Error ->
    let pos = lexbuf.lex_curr_p in
    let line = pos.pos_lnum in
    let col = pos.pos_cnum - pos.pos_bol in
    let token = Lexing.lexeme lexbuf in
    raise
      (Failure
         (Printf.sprintf "Parse error at line %d, column %d, near token '%s'"
            line col token))

let remove_extension filename =
  match String.rindex_opt filename '.' with
  | Some dot_index -> String.sub filename 0 dot_index
  | None -> filename

let resolve_import path_list =
  let rel_path = String.concat "/" path_list ^ ".ce" in
  if Sys.file_exists rel_path then rel_path
  else
    let env_path =
      match Sys.getenv_opt "CE_STD_PATH" with
      | Some p -> Filename.concat p rel_path
      | None -> ""
    in
    if env_path <> "" && Sys.file_exists env_path then env_path
    else
      let local_std_path = Filename.concat "./std" rel_path in
      if Sys.file_exists local_std_path then local_std_path
      else
        let global_std_path = Filename.concat "/usr/lib/ce/std" rel_path in
        if Sys.file_exists global_std_path then global_std_path
        else failwith ("Module not found: " ^ String.concat "." path_list)

class namespacer prefix decls =
  object (self)
    inherit Ce_parser.Ast_mapper.mapper as super

    method apply_namespace name =
      match List.assoc_opt name decls with
      | Some is_pub ->
          if is_pub then prefix ^ "." ^ name else prefix ^ ".__priv_" ^ name
      | None -> name

    method! map_type t =
      match t with
      | TNamed name -> TNamed (self#apply_namespace name)
      | TGenericInst (name, args) ->
          TGenericInst (self#apply_namespace name, List.map self#map_type args)
      | _ -> super#map_type t

    method! map_expr e =
      match e.node with
      | Call (name, targs, args) ->
          super#map_expr
            { e with node = Call (self#apply_namespace name, targs, args) }
      | Struct (name, targs, fields) ->
          super#map_expr
            { e with node = Struct (self#apply_namespace name, targs, fields) }
      | _ -> super#map_expr e

    method! map_stmt s =
      match s.node with
      | DefFN (name, tparams, params, ty, body) ->
          super#map_stmt
            {
              s with
              node = DefFN (self#apply_namespace name, tparams, params, ty, body);
            }
      | DefStruct (name, params, fields) ->
          super#map_stmt
            {
              s with
              node = DefStruct (self#apply_namespace name, params, fields);
            }
      | DefInterface (name, sigs) ->
          super#map_stmt
            { s with node = DefInterface (self#apply_namespace name, sigs) }
      | ExternFN (alias, name, params, ret_ty) ->
          super#map_stmt
            {
              s with
              node = ExternFN (alias, self#apply_namespace name, params, ret_ty);
            }
      | Impl (name, params, methods) ->
          super#map_stmt
            { s with node = Impl (self#apply_namespace name, params, methods) }
      | _ -> super#map_stmt s
  end

let namespace_stmt prefix decls ast = (new namespacer prefix decls)#map_stmt ast

class module_tagger mod_name =
  object
    inherit Ce_parser.Ast_mapper.mapper as super

    method! map_stmt s =
      let s' = super#map_stmt s in
      { s' with Ce_parser.Ast.mod_name }
  end

let rec process_file_inner visited filepath namespace_prefix mod_name =
  let cache_key =
    filepath
    ^ (match namespace_prefix with Some p -> ":" ^ p | None -> ":none")
    ^ ":" ^ mod_name
  in
  if Hashtbl.mem visited cache_key then []
  else begin
    Hashtbl.add visited cache_key true;
    let src = read filepath in

    let tagger = new module_tagger mod_name in
    let ast = parse filepath src |> List.map tagger#map_stmt in

    let decls =
      List.fold_left
        (fun acc stmt ->
          let name_opt =
            match stmt.node with
            | DefFN (name, _, _, _, _) -> Some name
            | DefStruct (name, _, _) -> Some name
            | DefInterface (name, _) -> Some name
            | ExternFN (_, name, _, _) -> Some name
            | DefLet (name, _, _, _) -> Some name
            | _ -> None
          in
          match name_opt with
          | Some name -> (name, stmt.is_pub) :: acc
          | None -> acc)
        [] ast
    in

    let namespaced_ast =
      match namespace_prefix with
      | Some prefix -> List.map (namespace_stmt prefix decls) ast
      | None -> ast
    in

    let imports_ast =
      List.fold_left
        (fun acc stmt ->
          match stmt.node with
          | Import path_list ->
              let import_path = resolve_import path_list in
              let module_name = List.hd (List.rev path_list) in
              acc
              @ process_file_inner visited import_path (Some module_name)
                  module_name
          | ImportFrom (names, path_list) ->
              let import_path = resolve_import path_list in
              let module_name = List.hd (List.rev path_list) in

              let raw_ast =
                process_file_inner visited import_path None module_name
              in

              let filtered_ast =
                List.filter
                  (fun s ->
                    let is_match =
                      match s.node with
                      | DefFN (name, _, _, _, _) -> List.mem name names
                      | DefStruct (name, _, _) -> List.mem name names
                      | DefInterface (name, _) -> List.mem name names
                      | ExternFN (_, name, _, _) -> List.mem name names
                      | Impl (name, _, _) -> List.mem name names
                      | DefLet (name, _, _, _) -> List.mem name names
                      | _ -> false
                    in
                    let is_impl =
                      match s.node with Impl _ -> true | _ -> false
                    in
                    if is_match && (not s.is_pub) && not is_impl then
                      failwith
                        ("Error: Cannot import a private item from module "
                       ^ module_name);
                    is_match)
                  raw_ast
              in
              acc @ filtered_ast
          | _ -> acc)
        [] namespaced_ast
    in

    imports_ast @ namespaced_ast
  end

let process_file visited filepath =
  let prelude_ast =
    try
      let std_path =
        if Sys.file_exists "std/std.ce" then "std/std.ce"
        else resolve_import [ "std"; "std" ]
      in
      process_file_inner visited std_path None "std"
    with e ->
      Printf.eprintf "%s\n" (Printexc.to_string e);
      []
  in

  let main_ast = process_file_inner visited filepath None "main" in
  prelude_ast @ main_ast

let export binary_name the_modules =
  ignore (Llvm_all_backends.initialize ());
  let target_triple = Target.default_triple () in
  let target = Target.by_triple target_triple in
  let machine =
    TargetMachine.create ~triple:target_triple ~reloc_mode:RelocMode.PIC target
  in

  let obj_files =
    List.map
      (fun (mname, m) ->
        let safe_mname =
          String.map
            (fun c -> if c = '/' || c = '\\' || c = '.' then '_' else c)
            mname
        in
        let obj_filename = binary_name ^ "_" ^ safe_mname ^ ".o" in
        TargetMachine.emit_to_file m CodeGenFileType.ObjectFile obj_filename
          machine;
        obj_filename)
      the_modules
  in

  let objs_str = String.concat " " obj_files in
  let link_cmd = Printf.sprintf "cc %s -lgc -o %s" objs_str binary_name in
  match Sys.command link_cmd with
  | 0 ->
      List.iter (fun o -> if Sys.file_exists o then Sys.remove o) obj_files;
      ()
  | code ->
      Printf.eprintf "Linking failed with code %d\n" code;
      exit 1

let execute file =
  let visited = Hashtbl.create 10 in
  let binary_name = remove_extension file in
  let _ =
    file |> process_file visited |> Compiler.compile |> export binary_name
  in
  Printf.printf "Compiled and linked: %s\n" binary_name

let command =
  let doc = "Compile inserted ce-lang code file to binary executable" in
  let info = Cmd.info "build" ~doc in
  Cmd.v info Term.(const execute $ Command.file_arg)
