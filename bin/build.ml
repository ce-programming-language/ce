open Ce_compiler
open Ce_parser
open Ce_lexer
open Ce_parser.Ast
open Cmdliner

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

let rec namespace_type prefix decls = function
  | TNamed name ->
      if List.mem name decls then TNamed (prefix ^ "." ^ name) else TNamed name
  | TGenericInst (name, args) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      TGenericInst (new_name, List.map (namespace_type prefix decls) args)
  | TPointer ty -> TPointer (namespace_type prefix decls ty)
  | TArray (n, ty) -> TArray (n, namespace_type prefix decls ty)
  | TResult ty -> TResult (namespace_type prefix decls ty)
  | TTuple ts -> TTuple (List.map (namespace_type prefix decls) ts)
  | TFn (args, ret) ->
      TFn
        ( List.map (namespace_type prefix decls) args,
          namespace_type prefix decls ret )
  | t -> t

and namespace_expr prefix decls = function
  | Add (l, r) ->
      Add (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Sub (l, r) ->
      Sub (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Mul (l, r) ->
      Mul (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Div (l, r) ->
      Div (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Mod (l, r) ->
      Mod (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Eq (l, r) ->
      Eq (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Lt (l, r) ->
      Lt (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Lte (l, r) ->
      Lte (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Gt (l, r) ->
      Gt (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Gte (l, r) ->
      Gte (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | And (l, r) ->
      And (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Or (l, r) ->
      Or (namespace_expr prefix decls l, namespace_expr prefix decls r)
  | Neg e -> Neg (namespace_expr prefix decls e)
  | Not e -> Not (namespace_expr prefix decls e)
  | Ref e -> Ref (namespace_expr prefix decls e)
  | Deref e -> Deref (namespace_expr prefix decls e)
  | Call (name, targs, args) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      Call
        ( new_name,
          List.map (namespace_type prefix decls) targs,
          List.map (namespace_expr prefix decls) args )
  | Array (n, ty, elems) ->
      Array
        ( n,
          namespace_type prefix decls ty,
          List.map (namespace_expr prefix decls) elems )
  | If (cond, then_b, elifs, else_b) ->
      If
        ( namespace_expr prefix decls cond,
          List.map (namespace_stmt prefix decls) then_b,
          List.map
            (fun (c, b) ->
              ( namespace_expr prefix decls c,
                List.map (namespace_stmt prefix decls) b ))
            elifs,
          Option.map (List.map (namespace_stmt prefix decls)) else_b )
  | Catch (e, id, ty, stmts) ->
      Catch
        ( namespace_expr prefix decls e,
          id,
          ty,
          List.map (namespace_stmt prefix decls) stmts )
  | CatchExpr (e, handler) ->
      CatchExpr
        (namespace_expr prefix decls e, namespace_expr prefix decls handler)
  | Struct (name, targs, fields) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      Struct
        ( new_name,
          List.map (namespace_type prefix decls) targs,
          List.map (fun (n, e) -> (n, namespace_expr prefix decls e)) fields )
  | Tuple es -> Tuple (List.map (namespace_expr prefix decls) es)
  | AnonFN (params, ret_ty, body) ->
      let s_params =
        List.map
          (fun (p : param) -> { p with ty = namespace_type prefix decls p.ty })
          params
      in
      AnonFN
        ( s_params,
          namespace_type prefix decls ret_ty,
          List.map (namespace_stmt prefix decls) body )
  | e -> e

and namespace_stmt prefix decls = function
  | Expr e -> Expr (namespace_expr prefix decls e)
  | DefLet (name, is_mut, ty, e) ->
      let new_e =
        match e with
        | Some e -> Some (namespace_expr prefix decls e)
        | None -> None
      in
      DefLet (name, is_mut, namespace_type prefix decls ty, new_e)
  | Assign (name, e) -> Assign (name, namespace_expr prefix decls e)
  | ArrayAssign (name, idx, e) ->
      ArrayAssign
        (name, namespace_expr prefix decls idx, namespace_expr prefix decls e)
  | DerefAssign (ptr, e) ->
      DerefAssign
        (namespace_expr prefix decls ptr, namespace_expr prefix decls e)
  | Return e -> Return (namespace_expr prefix decls e)
  | Block stmts -> Block (List.map (namespace_stmt prefix decls) stmts)
  | For (init, cond, mut, stmts) ->
      For
        ( Option.map (namespace_stmt prefix decls) init,
          Option.map (namespace_expr prefix decls) cond,
          Option.map (namespace_stmt prefix decls) mut,
          List.map (namespace_stmt prefix decls) stmts )
  | Raise e -> Raise (namespace_expr prefix decls e)
  | DefFN (name, tparams, params, ty, body) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      let ns_tparams =
        List.map (fun (n, t) -> (n, namespace_type prefix decls t)) tparams
      in
      let ns_params =
        List.map
          (fun p ->
            { param_name = p.param_name; ty = namespace_type prefix decls p.ty })
          params
      in
      DefFN
        ( new_name,
          ns_tparams,
          ns_params,
          namespace_type prefix decls ty,
          List.map (namespace_stmt prefix decls) body )
  | DefStruct (name, params, fields) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      let ns_params =
        List.map (fun (n, t) -> (n, namespace_type prefix decls t)) params
      in
      let s_fields =
        List.map
          (fun f -> { f with ty = namespace_type prefix decls f.ty })
          fields
      in
      DefStruct (new_name, ns_params, s_fields)
  | DefInterface (name, sigs) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      DefInterface (new_name, sigs)
  | ExternFN (alias, name, params, ret_ty) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      let ns_params =
        List.map
          (fun p ->
            { param_name = p.param_name; ty = namespace_type prefix decls p.ty })
          params
      in
      ExternFN (alias, new_name, ns_params, namespace_type prefix decls ret_ty)
  | Impl (name, params, methods) ->
      let new_name =
        if List.mem name decls then prefix ^ "." ^ name else name
      in
      let ns_params =
        List.map (fun (n, t) -> (n, namespace_type prefix decls t)) params
      in
      let s_methods =
        List.map
          (fun (m_name, self_id, is_ptr, m_params, ret_ty, body) ->
            let s_params =
              List.map
                (fun p ->
                  {
                    param_name = p.param_name;
                    ty = namespace_type prefix decls p.ty;
                  })
                m_params
            in
            ( m_name,
              self_id,
              is_ptr,
              s_params,
              namespace_type prefix decls ret_ty,
              List.map (namespace_stmt prefix decls) body ))
          methods
      in
      Impl (new_name, ns_params, s_methods)
  | s -> s

let rec process_file_inner visited filepath namespace_prefix =
  if Hashtbl.mem visited filepath then []
  else begin
    Hashtbl.add visited filepath true;
    let src = read filepath in
    let ast = parse src in
    let decls =
      List.fold_left
        (fun acc stmt ->
          match stmt with
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
          match stmt with
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

let execute file =
  let binary_name = remove_extension file in
  let visited = Hashtbl.create 10 in

  let ast = process_file visited file in

  let _ = ast |> Compiler.compile |> Generator.export binary_name in
  Printf.printf "Compiled and linked: %s\n" binary_name

let command =
  let doc = "Compile inserted ce-lang code file to binary executable" in
  let info = Cmd.info "build" ~doc in
  Cmd.v info Term.(const execute $ Command.file_arg)
