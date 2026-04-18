open Ce_parser.Ast

let rec substitute_type type_map = function
  | TGenericParam name -> (
      try List.assoc name type_map with Not_found -> TGenericParam name)
  | TNamed name -> (
      try List.assoc name type_map with Not_found -> TNamed name)
  | TPointer ty -> TPointer (substitute_type type_map ty)
  | TArray (n, ty) -> TArray (n, substitute_type type_map ty)
  | TGenericInst (name, args) ->
      TGenericInst (name, List.map (substitute_type type_map) args)
  | TResult ty -> TResult (substitute_type type_map ty)
  | TTuple ts -> TTuple (List.map (substitute_type type_map) ts)
  | TFn (args, ret) ->
      TFn
        (List.map (substitute_type type_map) args, substitute_type type_map ret)
  | other -> other

and substitute_expr type_map = function
  | Array (n, ty, elems) ->
      Array
        ( n,
          substitute_type type_map ty,
          List.map (substitute_expr type_map) elems )
  | Struct (name, targs, fields) ->
      let new_targs = List.map (substitute_type type_map) targs in
      let new_fields =
        List.map (fun (n, e) -> (n, substitute_expr type_map e)) fields
      in
      Struct (name, new_targs, new_fields)
  | Add (l, r) -> Add (substitute_expr type_map l, substitute_expr type_map r)
  | Sub (l, r) -> Sub (substitute_expr type_map l, substitute_expr type_map r)
  | Mul (l, r) -> Mul (substitute_expr type_map l, substitute_expr type_map r)
  | Div (l, r) -> Div (substitute_expr type_map l, substitute_expr type_map r)
  | Mod (l, r) -> Mod (substitute_expr type_map l, substitute_expr type_map r)
  | Eq (l, r) -> Eq (substitute_expr type_map l, substitute_expr type_map r)
  | Lt (l, r) -> Lt (substitute_expr type_map l, substitute_expr type_map r)
  | Lte (l, r) -> Lte (substitute_expr type_map l, substitute_expr type_map r)
  | Gt (l, r) -> Gt (substitute_expr type_map l, substitute_expr type_map r)
  | Gte (l, r) -> Gte (substitute_expr type_map l, substitute_expr type_map r)
  | And (l, r) -> And (substitute_expr type_map l, substitute_expr type_map r)
  | Or (l, r) -> Or (substitute_expr type_map l, substitute_expr type_map r)
  | Neg e -> Neg (substitute_expr type_map e)
  | Not e -> Not (substitute_expr type_map e)
  | Ref e -> Ref (substitute_expr type_map e)
  | Deref e -> Deref (substitute_expr type_map e)
  | Call (name, targs, args) ->
      Call
        ( name,
          List.map (substitute_type type_map) targs,
          List.map (substitute_expr type_map) args )
  | ArrayAccess (name, idx) -> ArrayAccess (name, substitute_expr type_map idx)
  | If (cond, then_b, elifs, else_b) ->
      let s_cond = substitute_expr type_map cond in
      let s_then = List.map (substitute_stmt type_map) then_b in
      let s_elifs =
        List.map
          (fun (c, b) ->
            (substitute_expr type_map c, List.map (substitute_stmt type_map) b))
          elifs
      in
      let s_else =
        match else_b with
        | None -> None
        | Some b -> Some (List.map (substitute_stmt type_map) b)
      in
      If (s_cond, s_then, s_elifs, s_else)
  | Catch (e, id, ty, stmts) ->
      Catch
        ( substitute_expr type_map e,
          id,
          substitute_type type_map ty,
          List.map (substitute_stmt type_map) stmts )
  | CatchExpr (e, handler) ->
      CatchExpr (substitute_expr type_map e, substitute_expr type_map handler)
  | Tuple es -> Tuple (List.map (substitute_expr type_map) es)
  | AnonFN (params, ret_ty, body) ->
      let s_params =
        List.map
          (fun (p : param) -> { p with ty = substitute_type type_map p.ty })
          params
      in
      AnonFN
        ( s_params,
          substitute_type type_map ret_ty,
          List.map (substitute_stmt type_map) body )
  | e -> e

and substitute_stmt type_map = function
  | Expr e -> Expr (substitute_expr type_map e)
  | DefLet (name, is_mut, ty, e) ->
      let new_e =
        match e with
        | Some ee -> Some (substitute_expr type_map ee)
        | None -> None
      in
      DefLet (name, is_mut, substitute_type type_map ty, new_e)
  | Assign (name, e) -> Assign (name, substitute_expr type_map e)
  | ArrayAssign (name, idx, e) ->
      ArrayAssign
        (name, substitute_expr type_map idx, substitute_expr type_map e)
  | DerefAssign (ptr, e) ->
      DerefAssign (substitute_expr type_map ptr, substitute_expr type_map e)
  | Return e -> Return (substitute_expr type_map e)
  | Block stmts -> Block (List.map (substitute_stmt type_map) stmts)
  | For (init, cond, mut, stmts) ->
      For
        ( Option.map (substitute_stmt type_map) init,
          Option.map (substitute_expr type_map) cond,
          Option.map (substitute_stmt type_map) mut,
          List.map (substitute_stmt type_map) stmts )
  | DefFN (name, tparams, params, ret_ty, body) ->
      let s_params =
        List.map
          (fun p ->
            { param_name = p.param_name; ty = substitute_type type_map p.ty })
          params
      in
      DefFN
        ( name,
          tparams,
          s_params,
          substitute_type type_map ret_ty,
          List.map (substitute_stmt type_map) body )
  | Raise e -> Raise (substitute_expr type_map e)
  | DefInterface (name, sigs) ->
      let s_sigs =
        List.map
          (fun s ->
            {
              fn_name = s.fn_name;
              params =
                List.map
                  (fun p ->
                    {
                      param_name = p.param_name;
                      ty = substitute_type type_map p.ty;
                    })
                  s.params;
              ret_ty = substitute_type type_map s.ret_ty;
            })
          sigs
      in
      DefInterface (name, s_sigs)
  | ExternFN (alias_opt, name, params, ret_ty) ->
      let s_params =
        List.map
          (fun p ->
            { param_name = p.param_name; ty = substitute_type type_map p.ty })
          params
      in
      ExternFN (alias_opt, name, s_params, substitute_type type_map ret_ty)
  | s -> s
