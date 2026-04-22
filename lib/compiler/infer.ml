open Ce_parser.Ast
open State
open Substitue
open Utils

let rec infer_ast_type env (expr : expr) =
  match expr.node with
  | Int _ -> TInt (I32, Signed)
  | Float _ -> TFloat F64
  | Bool _ -> TBool
  | String _ -> TString
  | Char _ -> TChar
  | Array (n, ty, _) -> TArray (n, ty)
  | Catch (_, _, ty, _) -> ty
  | CatchExpr (e, _) -> (
      match infer_ast_type env e with TResult t -> t | t -> t)
  | Struct (name, targs, _) ->
      if targs = [] then TNamed name else TGenericInst (name, targs)
  | Add (l, _) | Sub (l, _) | Mul (l, _) | Div (l, _) | Mod (l, _) ->
      infer_ast_type env l
  | Eq _ | Lt _ | Lte _ | Gt _ | Gte _ | And _ | Or _ -> TBool
  | Neg e -> infer_ast_type env e
  | Not _ -> TBool
  | Ref e -> TPointer (infer_ast_type env e)
  | Deref e -> (
      match infer_ast_type env e with
      | TPointer t -> t
      | TString -> TChar
      | _ -> TUnknown)
  | Let name ->
      begin if not (String.contains name '.') then
        try
          let _, ty, _ = Hashtbl.find env.named_values name in
          ty
        with Not_found -> TUnknown
      else
        let parts = String.split_on_char '.' name in
        let base_name = List.hd parts in
        let props = List.tl parts in
        try
          let _, ast_ty, _ = Hashtbl.find env.named_values base_name in
          let rec resolve_props current_ty props =
            match props with
            | [] -> current_ty
            | prop :: rest -> (
                let actual_ty =
                  match current_ty with TPointer t -> t | t -> t
                in
                match actual_ty with
                | TTuple ts -> (
                    try
                      let idx = int_of_string prop in
                      let next_ty = List.nth ts idx in
                      resolve_props next_ty rest
                    with _ -> TUnknown)
                | _ -> (
                    try
                      let s_name = ast_base_type_name actual_ty in
                      let clean_name =
                        if String.starts_with ~prefix:"struct." s_name then
                          String.sub s_name 7 (String.length s_name - 7)
                        else s_name
                      in
                      match Hashtbl.find_opt env.struct_registry clean_name with
                      | Some (_, field_map) -> (
                          try
                            let _, _, _, next_ty =
                              List.find (fun (n, _, _, _) -> n = prop) field_map
                            in
                            resolve_props next_ty rest
                          with Not_found -> TUnknown)
                      | None -> TUnknown
                    with Not_found -> TUnknown))
          in
          resolve_props ast_ty props
        with Not_found -> TUnknown
      end
  | ArrayAccess (name, _) -> (
      try
        let _, ty, _ = Hashtbl.find env.named_values name in
        match ty with TArray (_, t) -> t | _ -> TUnknown
      with Not_found -> TUnknown)
  | Call (name, targs, _) -> (
      if String.ends_with ~suffix:".as" name && List.length targs = 1 then
        List.hd targs
      else if Hashtbl.mem env.fn_templates name then
        let tparams, _, ret_ty, _ = Hashtbl.find env.fn_templates name in
        if List.length tparams = List.length targs then
          let type_map =
            List.map2 (fun (p_name, _) arg_ty -> (p_name, arg_ty)) tparams targs
          in
          substitute_type type_map ret_ty
        else TUnknown
      else if String.contains name '.' then
        let last_dot = String.rindex name '.' in
        let base_path = String.sub name 0 last_dot in
        let method_name =
          String.sub name (last_dot + 1) (String.length name - last_dot - 1)
        in
        try
          let _, ast_ty, _ = Hashtbl.find env.named_values base_path in
          let actual_ty = match ast_ty with TPointer t -> t | t -> t in
          let s_name = ast_base_type_name actual_ty in
          let mangled_name = s_name ^ "::" ^ method_name in
          let _, ret_ty = Hashtbl.find env.function_types mangled_name in
          ret_ty
        with Not_found -> (
          try
            let _, ret_ty = Hashtbl.find env.function_types name in
            ret_ty
          with Not_found -> TUnknown)
      else
        try
          let _, ret_ty = Hashtbl.find env.function_types name in
          ret_ty
        with Not_found -> TUnknown)
  | Tuple es -> TTuple (List.map (infer_ast_type env) es)
  | AnonFN (params, ret_ty, _) ->
      TFn (List.map (fun (p : param) -> p.ty) params, ret_ty)
  | _ -> TUnknown
