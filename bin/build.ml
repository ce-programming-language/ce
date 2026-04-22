open Ce_compiler
open Ce_parser
open Ce_lexer
open Ce_parser.Ast
open Cmdliner
open Llvm_target

let read file = In_channel.with_open_text file In_channel.input_all

let parse src =
  let lexbuf = Lexing.from_string src in
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
      if List.mem name decls then prefix ^ "." ^ name else name

    method! map_type t =
      match t with
      | TNamed name -> TNamed (self#apply_namespace name)
      | TGenericInst (name, args) ->
          TGenericInst (self#apply_namespace name, List.map self#map_type args)
      | _ -> super#map_type t

    method! map_expr e =
      match e.node with
      | Call (name, targs, args) ->
          Utils.mk_expr
          @@ Call
               ( self#apply_namespace name,
                 List.map self#map_type targs,
                 List.map self#map_expr args )
      | Struct (name, targs, fields) ->
          Utils.mk_expr
          @@ Struct
               ( self#apply_namespace name,
                 List.map self#map_type targs,
                 List.map (fun (n, expr) -> (n, self#map_expr expr)) fields )
      | _ -> super#map_expr e

    method! map_stmt s =
      match s.node with
      | DefFN (name, tparams, params, ty, body) ->
          super#map_stmt
            (Utils.mk_stmt
            @@ DefFN (self#apply_namespace name, tparams, params, ty, body))
      | DefStruct (name, params, fields) ->
          super#map_stmt
            (Utils.mk_stmt
            @@ DefStruct (self#apply_namespace name, params, fields))
      | DefInterface (name, sigs) ->
          super#map_stmt
            (Utils.mk_stmt @@ DefInterface (self#apply_namespace name, sigs))
      | ExternFN (alias, name, params, ret_ty) ->
          super#map_stmt
            (Utils.mk_stmt
            @@ ExternFN (alias, self#apply_namespace name, params, ret_ty))
      | Impl (name, params, methods) ->
          super#map_stmt
            (Utils.mk_stmt @@ Impl (self#apply_namespace name, params, methods))
      | _ -> super#map_stmt s
  end

let namespace_stmt prefix decls ast = (new namespacer prefix decls)#map_stmt ast

let rec process_file_inner visited filepath namespace_prefix =
  if Hashtbl.mem visited filepath then []
  else begin
    Hashtbl.add visited filepath true;
    let src = read filepath in
    let ast = parse src in
    let decls =
      List.fold_left
        (fun acc stmt ->
          match stmt.node with
          | DefFN (name, _, _, _, _) -> name :: acc
          | DefStruct (name, _, _) -> name :: acc
          | DefInterface (name, _) -> name :: acc
          | ExternFN (_, name, _, _) -> name :: acc
          | _ -> acc)
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
              acc @ process_file_inner visited import_path (Some module_name)
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
      process_file_inner visited std_path None
    with e ->
      Printf.eprintf "%s\n" (Printexc.to_string e);
      []
  in

  let main_ast = process_file_inner visited filepath None in
  prelude_ast @ main_ast

let export binary_name the_module =
  ignore (Llvm_all_backends.initialize ());
  let target_triple = Target.default_triple () in
  let target = Target.by_triple target_triple in
  let machine =
    TargetMachine.create ~triple:target_triple ~reloc_mode:RelocMode.PIC target
  in

  let obj_filename = binary_name ^ ".o" in
  TargetMachine.emit_to_file the_module CodeGenFileType.ObjectFile obj_filename
    machine;

  let link_cmd = Printf.sprintf "cc %s -lgc -o %s" obj_filename binary_name in
  match Sys.command link_cmd with
  | 0 ->
      if Sys.file_exists obj_filename then Sys.remove obj_filename;
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
