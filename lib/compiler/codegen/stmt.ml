open Llvm
open Ce_parser.Ast
open State
open Utils
open Infer
open Codegen

module Make (Types : TYPES) (Expr : EXPR) : STMT = struct
  exception Error of string

  let rec gen_block env stmts =
    List.iter
      (fun s ->
        if Option.is_none (block_terminator (insertion_block ce_builder)) then
          ignore (codegen env s))
      stmts

  and codegen (env : State.compiler_env) (s : stmt) =
    match s.node with
    | Expr e ->
        let v = Expr.codegen env codegen e in
        let ty = type_of v in
        let is_result =
          match classify_type ty with
          | TypeKind.Struct ->
              let elems = struct_element_types ty in
              Array.length elems = 3
              && elems.(0) = i1_type ce_ctx
              && elems.(2) = pointer_type ce_ctx
          | _ -> false
        in
        if is_result then
          ignore
            (Expr.coerce_value env s.loc
               (struct_element_types ty).(1)
               v false false);
        const_null (void_type ce_ctx)
    | DefLet (name, ismut, ty, expr_opt) ->
        let raw_val_opt, inferred_ty =
          match expr_opt with
          | Some e ->
              let raw_val = Expr.codegen env codegen e in
              let deduced_ty =
                if ty = TUnknown then
                  let inferred = infer_ast_type env e in
                  if inferred = TUnknown then
                    raise
                      (Utils.mk_error e.loc
                         ("Cannot infer type for variable '" ^ name
                        ^ "'. Please specify the type explicitly."))
                  else match inferred with TResult t -> t | _ -> inferred
                else ty
              in
              (Some raw_val, deduced_ty)
          | None ->
              if ty = TUnknown then
                raise
                  (Utils.mk_error s.loc
                     ("Cannot infer type for '" ^ name
                    ^ "' without initialization"));
              (None, ty)
        in

        let ll_ty = Types.llvm_type_of env inferred_ty in
        let init_val =
          match raw_val_opt with
          | Some raw_val ->
              let src_ty = infer_ast_type env (Option.get expr_opt) in
              let is_src_u = is_unsigned src_ty in
              Expr.coerce_value env s.loc ll_ty raw_val false is_src_u
          | None -> const_null ll_ty
        in
        let the_function = block_parent (insertion_block ce_builder) in
        let ce_builder_alloca =
          builder_at ce_ctx (instr_begin (entry_block the_function))
        in

        let alloca = build_alloca ll_ty name ce_builder_alloca in
        ignore (Utils.Stmt.gen_assignment ce_builder ll_ty alloca init_val);

        Hashtbl.add env.named_values name (alloca, inferred_ty, ismut);
        alloca
    | DefFN (name, tparams, params, ret_ty, body) ->
        if List.length tparams > 0 then begin
          Hashtbl.add env.fn_templates name (tparams, params, ret_ty, body);
          const_null (void_type ce_ctx)
        end
        else begin
          let actual_name = if name = "main" then "__ce_main" else name in

          let was_res = !(env.current_fn_is_res) in
          let was_ret_ty = !(env.current_fn_ret_ty) in

          (env.current_fn_is_res :=
             match ret_ty with TResult _ -> true | _ -> false);
          env.current_fn_ret_ty := Types.llvm_type_of env ret_ty;

          let param_types =
            Array.of_list
              (List.map (fun (p : param) -> Types.llvm_type_of env p.ty) params)
          in
          let ft = function_type (Types.llvm_type_of env ret_ty) param_types in
          Hashtbl.add env.function_types actual_name (ft, ret_ty);

          let f = declare_function actual_name ft ce_module in
          set_linkage Linkage.Internal f;

          let bb = append_block ce_ctx "entry" f in
          position_at_end bb ce_builder;

          let old_named_values = Hashtbl.copy env.named_values in
          Array.iteri
            (fun i a ->
              let n = (List.nth params i).param_name in
              let p_ty = (List.nth params i).ty in
              let llvm_p_ty = Types.llvm_type_of env p_ty in
              let alloca = build_alloca llvm_p_ty n ce_builder in
              ignore (build_store a alloca ce_builder);
              Hashtbl.add env.named_values n (alloca, p_ty, false))
            (Llvm.params f);

          gen_block env body;

          let current_bb = insertion_block ce_builder in
          (match block_terminator current_bb with
          | Some _ -> ()
          | None ->
              if ret_ty = TVoid || !(env.current_fn_is_res) then
                ignore
                  (Utils.Stmt.gen_return env ce_builder ce_ctx
                     (const_null (void_type ce_ctx)))
              else
                raise
                  (Utils.mk_error s.loc
                     ("Function '" ^ name ^ "' is missing a return statement")));

          Hashtbl.clear env.named_values;
          Hashtbl.iter
            (fun k v -> Hashtbl.add env.named_values k v)
            old_named_values;

          env.current_fn_is_res := was_res;
          env.current_fn_ret_ty := was_ret_ty;

          if name = "main" then begin
            let c_main_ty = function_type (i32_type ce_ctx) [||] in
            let c_main_f = declare_function "main" c_main_ty ce_module in
            let c_bb = append_block ce_ctx "entry" c_main_f in
            let c_builder = builder_at_end ce_ctx c_bb in

            let call_name = if ret_ty = TVoid then "" else "main_call" in
            let call_res = build_call ft f [||] call_name c_builder in

            if match ret_ty with TResult _ -> true | _ -> false then begin
              let is_err = build_extractvalue call_res 0 "is_err" c_builder in
              let[@warning "-8"] [ err_bb; ok_bb ] =
                Utils.create_blocks ce_ctx c_builder [ "err"; "ok" ]
              in

              ignore (build_cond_br is_err err_bb ok_bb c_builder);

              position_at_end err_bb c_builder;
              let err_msg = build_extractvalue call_res 2 "err_msg" c_builder in
              let printf_ty =
                var_arg_function_type (i32_type ce_ctx)
                  [| pointer_type ce_ctx |]
              in
              let printf_f =
                match Utils.lookup_function env "printf" ce_module with
                | Some f -> f
                | None -> declare_function "printf" printf_ty ce_module
              in
              let fmt_str =
                build_global_stringptr "Uncaught Error: %s\n" "err_fmt"
                  c_builder
              in
              ignore
                (build_call
                   (var_arg_function_type (i32_type ce_ctx)
                      [| pointer_type ce_ctx |])
                   printf_f [| fmt_str; err_msg |] "printf_call" c_builder);
              ignore (build_ret (const_int (i32_type ce_ctx) 1) c_builder);

              position_at_end ok_bb c_builder;
              ignore (build_ret (const_int (i32_type ce_ctx) 0) c_builder)
            end
            else begin
              ignore (build_ret (const_int (i32_type ce_ctx) 0) c_builder)
            end
          end;
          f
        end
    | DefType (name, underlying_ty) ->
        Hashtbl.add env.type_aliases name underlying_ty;
        const_null (void_type ce_ctx)
    | DefStruct (name, params, fields) ->
        if List.length params > 0 then begin
          Hashtbl.add env.struct_templates name (params, fields);
          const_null (void_type ce_ctx)
        end
        else begin
          let field_types =
            Array.of_list
              (List.map (fun f -> Types.llvm_type_of env f.ty) fields)
          in
          let struct_llty = named_struct_type ce_ctx name in
          struct_set_body struct_llty field_types false;

          let field_map =
            List.mapi (fun i f -> (f.field_name, i, f.is_mut, f.ty)) fields
          in
          Hashtbl.add env.struct_registry name (struct_llty, field_map);
          const_null (void_type ce_ctx)
        end
    | Assign (name, expr) ->
        let val_ = Expr.codegen env codegen expr in
        let var_ptr, expected_ll_ty, is_u =
          if String.contains name '.' then
            let parts = String.split_on_char '.' name in
            let base_name = List.hd parts in
            let v, ast_ty, _ = Hashtbl.find env.named_values base_name in

            let is_ptr, base_struct_ast_ty =
              match ast_ty with TPointer t -> (true, t) | t -> (false, t)
            in
            let base_struct_llty = Types.llvm_type_of env base_struct_ast_ty in

            let base_ptr =
              if is_ptr then
                build_load
                  (Types.llvm_type_of env ast_ty)
                  v "auto_deref_ptr" ce_builder
              else v
            in

            let rec resolve_assign ptr ty props =
              match props with
              | [] -> (ptr, ty)
              | prop :: rest -> (
                  match struct_name ty with
                  | Some s_name ->
                      let clean_name = clean_struct_name s_name in
                      let _, field_map =
                        Hashtbl.find env.struct_registry clean_name
                      in
                      let _, idx, is_mut, _ =
                        List.find (fun (n, _, _, _) -> n = prop) field_map
                      in
                      if rest = [] && not is_mut then
                        raise
                          (Utils.mk_error s.loc
                             ("Cannot assign to immutable field '" ^ prop
                            ^ "' on struct '" ^ clean_name ^ "'"));
                      let next_ptr =
                        build_struct_gep ty ptr idx "prop_ptr" ce_builder
                      in
                      let next_ty = (struct_element_types ty).(idx) in
                      resolve_assign next_ptr next_ty rest
                  | None ->
                      let idx = int_of_string prop in
                      let next_ptr =
                        build_struct_gep ty ptr idx "tuple_ptr" ce_builder
                      in
                      let next_ty = (struct_element_types ty).(idx) in
                      resolve_assign next_ptr next_ty rest)
            in

            let final_ptr, final_ty =
              resolve_assign base_ptr base_struct_llty (List.tl parts)
            in
            (final_ptr, final_ty, false)
          else
            let v, ast_ty, ismut =
              try Hashtbl.find env.named_values name
              with Not_found ->
                raise
                  (Utils.mk_error s.loc ("Unknown variable: '" ^ name ^ "'"))
            in
            if not ismut then
              raise
                (Utils.mk_error s.loc
                   ("Cannot assign to immutable variable '" ^ name ^ "'"));

            (v, Types.llvm_type_of env ast_ty, is_unsigned ast_ty)
        in
        let src_ty = infer_ast_type env expr in
        let is_src_u = is_unsigned src_ty in
        let val_to_store =
          Expr.coerce_value env s.loc expected_ll_ty val_ is_u is_src_u
        in
        Utils.Stmt.gen_assignment ce_builder expected_ll_ty var_ptr val_to_store
    | ArrayAssign (name, index_expr, val_expr) ->
        let array_ptr_val, array_ty =
          match Hashtbl.find_opt env.named_values name with
          | Some (v, ty, ismut) ->
              if not ismut then
                raise
                  (Utils.mk_error s.loc
                     ("Cannot assign to immutable array '" ^ name ^ "'"));
              (v, ty)
          | None ->
              raise
                (Utils.mk_error s.loc
                   ("Array '" ^ name ^ "' not found for assignment"))
        in

        let idx_val = Expr.codegen env codegen index_expr in
        let val_to_store = Expr.codegen env codegen val_expr in

        let zero = const_int (i32_type ce_ctx) 0 in
        let indices = [| zero; idx_val |] in
        let element_ptr =
          build_in_bounds_gep
            (Types.llvm_type_of env array_ty)
            array_ptr_val indices "arrayidx" ce_builder
        in
        let expected_ll_ty = element_type (Types.llvm_type_of env array_ty) in
        Utils.Stmt.gen_assignment ce_builder expected_ll_ty element_ptr
          val_to_store
    | DerefAssign (ptr_expr, val_expr) ->
        let actual_ptr = Expr.codegen env codegen ptr_expr in
        let ptr_ast_ty = infer_ast_type env ptr_expr in
        let expected_ast_ty =
          match ptr_ast_ty with
          | TPointer t -> t
          | TString -> TChar
          | _ ->
              raise
                (Utils.mk_error s.loc
                   "Left-hand side of dereference assignment must be a pointer")
        in

        let raw_val = Expr.codegen env codegen val_expr in
        let src_ty = infer_ast_type env val_expr in
        let is_src_u = is_unsigned src_ty in
        let expected_ll_ty = Types.llvm_type_of env expected_ast_ty in
        let val_to_store =
          Expr.coerce_value env s.loc
            (Types.llvm_type_of env expected_ast_ty)
            raw_val
            (is_unsigned expected_ast_ty)
            is_src_u
        in
        Utils.Stmt.gen_assignment ce_builder expected_ll_ty actual_ptr
          val_to_store
    | Block stmts ->
        gen_block env stmts;
        const_null (void_type ce_ctx)
    | For (init, cond, mut, stmts) ->
        let is_foreach =
          match (init, cond, mut) with
          | None, Some c, None -> (
              let c_ty = infer_ast_type env c in
              match c_ty with
              | TArray _ -> true
              | TGenericInst (n, _) when n = "Slice" -> true
              | _ -> false)
          | _ -> false
        in
        if is_foreach then
          codegen env
            (Utils.mk_stmt (ForEach (None, None, Option.get cond, stmts)))
        else begin
          let init_var_name =
            match init with
            | Some { node = DefLet (n, _, _, _) } -> Some n
            | _ -> None
          in
          (match init with Some s -> ignore (codegen env s) | None -> ());

          let[@warning "-8"] [ cond_bb; loop_bb; mut_bb; after_bb ] =
            Utils.create_blocks ce_ctx ce_builder
              [ "loop_cond"; "loop"; "loop_mut"; "afterloop" ]
          in

          ignore (build_br cond_bb ce_builder);

          position_at_end cond_bb ce_builder;
          (match cond with
          | Some c ->
              let cond_val = Expr.codegen env codegen c in
              ignore (build_cond_br cond_val loop_bb after_bb ce_builder)
          | None -> ignore (build_br loop_bb ce_builder));

          position_at_end loop_bb ce_builder;
          Stack.push after_bb env.loop_exit_blocks;

          gen_block env stmts;

          if Option.is_none (block_terminator (insertion_block ce_builder)) then
            ignore (build_br mut_bb ce_builder);

          position_at_end mut_bb ce_builder;
          (match mut with Some m -> ignore (codegen env m) | None -> ());

          ignore (build_br cond_bb ce_builder);

          ignore (Stack.pop env.loop_exit_blocks);
          position_at_end after_bb ce_builder;

          (match init_var_name with
          | Some n -> Hashtbl.remove env.named_values n
          | None -> ());

          const_null (void_type ce_ctx)
        end
    | ForEach (idx_name_opt, val_name_opt, iter_expr, stmts) ->
        let iter_val = Expr.codegen env codegen iter_expr in
        let iter_ast_ty = infer_ast_type env iter_expr in

        let[@warning "-8"] [ cond_bb; loop_bb; after_bb ] =
          Utils.create_blocks ce_ctx ce_builder
            [ "foreach_cond"; "foreach_loop"; "afterforeach" ]
        in

        let is_array = match iter_ast_ty with TArray _ -> true | _ -> false in

        let idx_alloc =
          build_alloca (i32_type ce_ctx) "foreach_idx" ce_builder
        in
        ignore
          (Utils.Stmt.gen_assignment ce_builder (i32_type ce_ctx) idx_alloc
             (const_int (i32_type ce_ctx) 0));

        ignore (build_br cond_bb ce_builder);
        position_at_end cond_bb ce_builder;
        let current_idx =
          build_load (i32_type ce_ctx) idx_alloc "curr_idx" ce_builder
        in

        let len_val =
          if is_array then
            match iter_ast_ty with
            | TArray (n, _) -> const_int (i32_type ce_ctx) n
            | _ -> failwith ""
          else build_extractvalue iter_val 1 "slice_len" ce_builder
        in
        let cmp =
          build_icmp Icmp.Slt current_idx len_val "foreach_cmp" ce_builder
        in
        ignore (build_cond_br cmp loop_bb after_bb ce_builder);

        position_at_end loop_bb ce_builder;
        Stack.push after_bb env.loop_exit_blocks;

        (match idx_name_opt with
        | Some idx_name ->
            Hashtbl.add env.named_values idx_name
              (idx_alloc, TInt (I32, Signed), false)
        | None -> ());

        (match val_name_opt with
        | Some val_name ->
            let elem_val =
              if is_array then begin
                let arr_tmp =
                  build_alloca
                    (Types.llvm_type_of env iter_ast_ty)
                    "arr_tmp" ce_builder
                in
                ignore (build_store iter_val arr_tmp ce_builder);
                let zero = const_int (i32_type ce_ctx) 0 in
                let gep =
                  build_in_bounds_gep
                    (Types.llvm_type_of env iter_ast_ty)
                    arr_tmp [| zero; current_idx |] "arr_gep" ce_builder
                in
                build_load
                  (element_type (Types.llvm_type_of env iter_ast_ty))
                  gep "arr_elem" ce_builder
              end
              else begin
                let slice_ptr =
                  build_extractvalue iter_val 0 "slice_ptr" ce_builder
                in
                let gep =
                  build_in_bounds_gep
                    (element_type (type_of slice_ptr))
                    slice_ptr [| current_idx |] "slice_gep" ce_builder
                in
                build_load
                  (element_type (type_of slice_ptr))
                  gep "slice_elem" ce_builder
              end
            in
            let elem_ast_ty =
              match iter_ast_ty with
              | TArray (_, t) -> t
              | TGenericInst (_, [ t ]) -> t
              | _ -> TUnknown
            in
            let val_alloc =
              build_alloca (type_of elem_val) val_name ce_builder
            in
            ignore (build_store elem_val val_alloc ce_builder);
            Hashtbl.add env.named_values val_name (val_alloc, elem_ast_ty, false)
        | None -> ());

        gen_block env stmts;

        (match idx_name_opt with
        | Some idx_name -> Hashtbl.remove env.named_values idx_name
        | None -> ());
        (match val_name_opt with
        | Some val_name -> Hashtbl.remove env.named_values val_name
        | None -> ());

        if Option.is_none (block_terminator (insertion_block ce_builder)) then begin
          let next_idx =
            build_add current_idx
              (const_int (i32_type ce_ctx) 1)
              "next_idx" ce_builder
          in
          ignore (build_store next_idx idx_alloc ce_builder);
          ignore (build_br cond_bb ce_builder)
        end;

        ignore (Stack.pop env.loop_exit_blocks);
        position_at_end after_bb ce_builder;

        const_null (void_type ce_ctx)
    | Break ->
        if Stack.is_empty env.loop_exit_blocks then
          raise (Utils.mk_error s.loc "Break outside of a loop");
        let exit_block = Stack.top env.loop_exit_blocks in
        ignore (build_br exit_block ce_builder);
        const_null (void_type ce_ctx)
    | Return e ->
        let v = Expr.codegen env codegen e in
        Utils.Stmt.gen_return env ce_builder ce_ctx v
    | Import _ -> const_null (void_type ce_ctx)
    | Impl (name, params, methods) ->
        if List.length params > 0 then begin
          Hashtbl.add env.impl_templates name (params, methods);
          const_null (void_type ce_ctx)
        end
        else begin
          List.iter
            (fun (method_name, self_id, is_ptr, m_params, ret_ty, body) ->
              let mangled_name = name ^ "::" ^ method_name in
              let base_ty =
                match name with
                | "int" -> TInt (I32, Signed)
                | "i8" -> TInt (I8, Signed)
                | "i16" -> TInt (I16, Signed)
                | "i64" -> TInt (I64, Signed)
                | "i128" -> TInt (I128, Signed)
                | "uint" -> TInt (I32, Unsigned)
                | "u8" -> TInt (I8, Unsigned)
                | "u16" -> TInt (I16, Unsigned)
                | "u64" -> TInt (I64, Unsigned)
                | "u128" -> TInt (I128, Unsigned)
                | "f32" -> TFloat F32
                | "float" -> TFloat F64
                | "string" -> TString
                | "bool" -> TBool
                | "char" -> TChar
                | _ -> TNamed name
              in

              let self_ty = if is_ptr then TPointer base_ty else base_ty in
              let self_param = { param_name = self_id; ty = self_ty } in
              let all_params = self_param :: m_params in
              ignore
                (codegen env
                   (Utils.mk_stmt
                      (DefFN (mangled_name, [], all_params, ret_ty, body)))))
            methods;
          const_null (void_type ce_ctx)
        end
    | Raise e ->
        let err_msg = Expr.codegen env codegen e in
        let ret_ty = !(env.current_fn_ret_ty) in
        let res_struct = gen_err_result ce_ctx ce_builder ret_ty err_msg in
        ignore (build_ret res_struct ce_builder);
        const_null (void_type ce_ctx)
    | DefInterface (name, sigs) ->
        Hashtbl.add env.interface_registry name sigs;
        const_null (void_type ce_ctx)
    | ExternFN (alias_opt, name, params, ret_ty) ->
        let c_name = match alias_opt with Some a -> a | None -> name in
        if c_name <> name then Hashtbl.add env.extern_aliases name c_name;

        let param_types =
          Array.of_list
            (List.map (fun (p : param) -> Types.llvm_type_of env p.ty) params)
        in
        let ft = function_type (Types.llvm_type_of env ret_ty) param_types in
        Hashtbl.add env.function_types name (ft, ret_ty);

        let _ =
          match Llvm.lookup_function c_name ce_module with
          | Some f -> f
          | None -> declare_function c_name ft ce_module
        in
        const_null (void_type ce_ctx)
end
