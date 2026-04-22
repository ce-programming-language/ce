open Ast

class mapper =
  object (self)
    method map_type (t : types) : types =
      match t with
      | TPointer ty -> TPointer (self#map_type ty)
      | TArray (n, ty) -> TArray (n, self#map_type ty)
      | TGenericInst (n, args) -> TGenericInst (n, List.map self#map_type args)
      | TResult ty -> TResult (self#map_type ty)
      | TTuple ts -> TTuple (List.map self#map_type ts)
      | TFn (args, ret) -> TFn (List.map self#map_type args, self#map_type ret)
      | t -> t

    method map_expr (e : expr) : expr =
      let mapped =
        match e.node with
        | Ref expr -> Ref (self#map_expr expr)
        | Deref expr -> Deref (self#map_expr expr)
        | Neg expr -> Neg (self#map_expr expr)
        | Not expr -> Not (self#map_expr expr)
        | Add (l, r) -> Add (self#map_expr l, self#map_expr r)
        | Sub (l, r) -> Sub (self#map_expr l, self#map_expr r)
        | Mul (l, r) -> Mul (self#map_expr l, self#map_expr r)
        | Div (l, r) -> Div (self#map_expr l, self#map_expr r)
        | Mod (l, r) -> Mod (self#map_expr l, self#map_expr r)
        | Eq (l, r) -> Eq (self#map_expr l, self#map_expr r)
        | Lt (l, r) -> Lt (self#map_expr l, self#map_expr r)
        | Lte (l, r) -> Lte (self#map_expr l, self#map_expr r)
        | Gt (l, r) -> Gt (self#map_expr l, self#map_expr r)
        | Gte (l, r) -> Gte (self#map_expr l, self#map_expr r)
        | And (l, r) -> And (self#map_expr l, self#map_expr r)
        | Or (l, r) -> Or (self#map_expr l, self#map_expr r)
        | Call (name, targs, args) ->
            Call
              (name, List.map self#map_type targs, List.map self#map_expr args)
        | Array (n, ty, elems) ->
            Array (n, self#map_type ty, List.map self#map_expr elems)
        | ArrayAccess (name, idx) -> ArrayAccess (name, self#map_expr idx)
        | If (cond, then_b, elifs, else_b) ->
            let map_elif (c, b) = (self#map_expr c, List.map self#map_stmt b) in
            If
              ( self#map_expr cond,
                List.map self#map_stmt then_b,
                List.map map_elif elifs,
                Option.map (List.map self#map_stmt) else_b )
        | Struct (name, targs, fields) ->
            let map_field (n, expr) = (n, self#map_expr expr) in
            Struct
              (name, List.map self#map_type targs, List.map map_field fields)
        | Tuple elems -> Tuple (List.map self#map_expr elems)
        | AnonFN (params, ret_ty, body) ->
            let s_params =
              List.map
                (fun (p : param) -> { p with ty = self#map_type p.ty })
                params
            in
            AnonFN (s_params, self#map_type ret_ty, List.map self#map_stmt body)
        | Catch (expr, id, ty, body) ->
            Catch
              ( self#map_expr expr,
                id,
                self#map_type ty,
                List.map self#map_stmt body )
        | CatchExpr (expr, handler) ->
            CatchExpr (self#map_expr expr, self#map_expr handler)
        | e -> e
      in
      { e with node = mapped }

    method map_stmt (s : stmt) : stmt =
      let mapped =
        match s.node with
        | Expr e -> Expr (self#map_expr e)
        | DefLet (n, is_mut, ty, e_opt) ->
            DefLet (n, is_mut, self#map_type ty, Option.map self#map_expr e_opt)
        | DefType (n, ty) -> DefType (n, self#map_type ty)
        | DefStruct (name, tparams, fields) ->
            let map_tparam (n, ty) = (n, self#map_type ty) in
            let map_field (f : struct_field) =
              { f with ty = self#map_type f.ty }
            in
            DefStruct
              (name, List.map map_tparam tparams, List.map map_field fields)
        | Assign (name, e) -> Assign (name, self#map_expr e)
        | ArrayAssign (name, idx, e) ->
            ArrayAssign (name, self#map_expr idx, self#map_expr e)
        | DerefAssign (ptr, e) ->
            DerefAssign (self#map_expr ptr, self#map_expr e)
        | Return e -> Return (self#map_expr e)
        | Block stmts -> Block (List.map self#map_stmt stmts)
        | For (init, cond, mut, stmts) ->
            For
              ( Option.map self#map_stmt init,
                Option.map self#map_expr cond,
                Option.map self#map_stmt mut,
                List.map self#map_stmt stmts )
        | ForEach (idx, v, iter, stmts) ->
            ForEach (idx, v, self#map_expr iter, List.map self#map_stmt stmts)
        | Raise e -> Raise (self#map_expr e)
        | DefInterface (name, sigs) ->
            let map_sig (s : fn_signature) =
              {
                fn_name = s.fn_name;
                params =
                  List.map
                    (fun (p : param) -> { p with ty = self#map_type p.ty })
                    s.params;
                ret_ty = self#map_type s.ret_ty;
              }
            in
            DefInterface (name, List.map map_sig sigs)
        | ExternFN (alias, name, params, ret_ty) ->
            let s_params =
              List.map
                (fun (p : param) -> { p with ty = self#map_type p.ty })
                params
            in
            ExternFN (alias, name, s_params, self#map_type ret_ty)
        | DefFN (name, tparams, params, ret_ty, body) ->
            let map_tparam (n, ty) = (n, self#map_type ty) in
            let s_params =
              List.map
                (fun (p : param) -> { p with ty = self#map_type p.ty })
                params
            in
            DefFN
              ( name,
                List.map map_tparam tparams,
                s_params,
                self#map_type ret_ty,
                List.map self#map_stmt body )
        | Impl (name, tparams, methods) ->
            let map_tparam (n, ty) = (n, self#map_type ty) in
            let map_method (m_name, self_id, is_ptr, m_params, ret_ty, body) =
              let s_params =
                List.map
                  (fun (p : param) -> { p with ty = self#map_type p.ty })
                  m_params
              in
              ( m_name,
                self_id,
                is_ptr,
                s_params,
                self#map_type ret_ty,
                List.map self#map_stmt body )
            in
            Impl (name, List.map map_tparam tparams, List.map map_method methods)
        | s -> s
      in
      { s with node = mapped }
  end
