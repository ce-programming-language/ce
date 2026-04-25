open Llvm
open Ce_parser.Ast
open Ce_error
open State
open Utils
open Infer
open Codegen

module Make (Types : TYPES) : EXPR = struct
  let is_result_type ty =
    match classify_type ty with
    | TypeKind.Struct ->
        let elems = struct_element_types ty in
        Array.length elems = 3
        && elems.(0) = i1_type ce_ctx
        && elems.(2) = pointer_type ce_ctx
    | _ -> false

  let is_interface_type ty =
    match classify_type ty with
    | TypeKind.Struct ->
        let elems = struct_element_types ty in
        Array.length elems = 2
        && elems.(0) = pointer_type ce_ctx
        && elems.(1) = pointer_type ce_ctx
    | _ -> false

  let check_unsigned_bounds env loc is_unsigned_target is_unsigned_source raw_ty
      raw_val =
    if
      (not is_unsigned_target) || is_unsigned_source
      || classify_type raw_ty <> TypeKind.Integer
    then ()
    else
      let needs_runtime_check =
        match int64_of_const raw_val with
        | Some v ->
            let bw = integer_bitwidth raw_ty in
            if bw <= 64 then
              let sign_bit = Int64.shift_left 1L (bw - 1) in
              Int64.logand v sign_bit <> 0L
            else true
        | None -> true
      in
      if needs_runtime_check then begin
        let the_func = block_parent (insertion_block !ce_builder) in
        let ok_bb = append_block ce_ctx "uint_ok" the_func in
        let err_bb = append_block ce_ctx "uint_err" the_func in
        let zero = const_int raw_ty 0 in
        let is_neg = build_icmp Icmp.Slt raw_val zero "is_neg" !ce_builder in
        ignore (build_cond_br is_neg err_bb ok_bb !ce_builder);

        position_at_end err_bb !ce_builder;
        let printf_ty =
          var_arg_function_type (i32_type ce_ctx) [| pointer_type ce_ctx |]
        in
        let printf_fn =
          match Utils.lookup_function env "printf" !ce_module with
          | Some f -> f
          | None -> declare_function "printf" printf_ty !ce_module
        in
        let err_fmt =
          build_global_stringptr
            "Runtime Error: Cannot assign negative value to unsigned type\n"
            "err_fmt" !ce_builder
        in
        ignore (build_call printf_ty printf_fn [| err_fmt |] "p" !ce_builder);

        let exit_ty = function_type (void_type ce_ctx) [| i32_type ce_ctx |] in
        let exit_fn =
          match Utils.lookup_function env "exit" !ce_module with
          | Some f -> f
          | None -> declare_function "exit" exit_ty !ce_module
        in
        ignore
          (build_call exit_ty exit_fn
             [| const_int (i32_type ce_ctx) 1 |]
             "" !ce_builder);
        ignore (build_unreachable !ce_builder);
        position_at_end ok_bb !ce_builder
      end

  let autobox_interface env actual_ast_ty expected_ast_ty expected_ll_ty raw_val
      raw_ty =
    let actual_raw_val, actual_raw_ty =
      if classify_type raw_ty = TypeKind.Float then
        ( build_fpext raw_val (double_type ce_ctx) "box_fext" !ce_builder,
          double_type ce_ctx )
      else (raw_val, raw_ty)
    in
    let ptr_ty = pointer_type ce_ctx in
    let is_ptr = classify_type actual_raw_ty = TypeKind.Pointer in

    let data_ptr =
      if is_ptr then
        build_bitcast actual_raw_val ptr_ty "autobox_data" !ce_builder
      else begin
        let malloc_val =
          build_malloc actual_raw_ty "autobox_malloc" !ce_builder
        in
        ignore (build_store actual_raw_val malloc_val !ce_builder);
        build_bitcast malloc_val ptr_ty "autobox_data" !ce_builder
      end
    in
    let vtable_ptr =
      match expected_ast_ty with
      | TNamed trait_name
        when Hashtbl.mem env.interface_registry trait_name
             && trait_name <> "any" && trait_name <> "std.any" ->
          let sigs = Hashtbl.find env.interface_registry trait_name in
          let base_ast_ty =
            match actual_ast_ty with TPointer t -> t | t -> t
          in
          let clean_struct_name =
            try ast_base_type_name base_ast_ty with _ -> ""
          in
          let vtable_size = List.length sigs in
          let vtable_llty = array_type ptr_ty vtable_size in
          let gc_malloc_ty = function_type ptr_ty [| i64_type ce_ctx |] in
          let gc_malloc_fn =
            match Utils.lookup_function env "GC_malloc" !ce_module with
            | Some f -> f
            | None -> declare_function "GC_malloc" gc_malloc_ty !ce_module
          in
          let total_size =
            build_mul
              (const_int (i64_type ce_ctx) vtable_size)
              (size_of ptr_ty) "vtable_size" !ce_builder
          in
          let vtable_alloc_raw =
            build_call gc_malloc_ty gc_malloc_fn [| total_size |]
              "vtable_alloc_raw" !ce_builder
          in

          List.iteri
            (fun i method_sig ->
              let mangled_method =
                clean_struct_name ^ "::" ^ method_sig.fn_name
              in
              let func_ptr =
                match Utils.lookup_function env mangled_method !ce_module with
                | Some f -> build_bitcast f ptr_ty "fn_cast" !ce_builder
                | None -> const_null ptr_ty
              in
              let gep =
                build_in_bounds_gep vtable_llty vtable_alloc_raw
                  [|
                    const_int (i32_type ce_ctx) 0; const_int (i32_type ce_ctx) i;
                  |]
                  "vtable_gep" !ce_builder
              in
              ignore (build_store func_ptr gep !ce_builder))
            sigs;
          vtable_alloc_raw
      | _ ->
          let type_tag =
            let rec get_tag = function
              | TInt (1, Unsigned) -> 3
              | TInt (8, Unsigned) -> 5
              | TInt _ -> 1
              | TFloat _ -> 2
              | TString -> 4
              | TGenericInst ("slices.Slice", [ t ]) -> (
                  match get_tag t with
                  | 1 -> 6
                  | 2 -> 7
                  | 3 -> 8
                  | 4 -> 9
                  | 5 -> 10
                  | _ -> 0)
              | _ -> 0
            in
            let ast_tag = get_tag actual_ast_ty in
            if ast_tag <> 0 then ast_tag
            else
              match classify_type actual_raw_ty with
              | TypeKind.Integer ->
                  let bw = integer_bitwidth actual_raw_ty in
                  if bw = 1 then 3 else if bw = 8 then 5 else 1
              | TypeKind.Double -> 2
              | TypeKind.Pointer -> 4
              | _ -> 0
          in
          build_inttoptr
            (const_int (i64_type ce_ctx) type_tag)
            ptr_ty "autobox_tag" !ce_builder
    in
    let box_0 =
      build_insertvalue
        (const_null expected_ll_ty)
        data_ptr 0 "autobox_d" !ce_builder
    in
    build_insertvalue box_0 vtable_ptr 1 "autobox_v" !ce_builder

  let rec coerce_value env loc actual_ast_ty expected_ast_ty expected_ll_ty
      raw_val is_unsigned_target is_unsigned_source =
    let raw_ty = type_of raw_val in
    check_unsigned_bounds env loc is_unsigned_target is_unsigned_source raw_ty
      raw_val;
    let raw_kind = classify_type raw_ty in
    let exp_kind = classify_type expected_ll_ty in

    if raw_ty = expected_ll_ty then raw_val
    else if raw_kind = TypeKind.Integer && exp_kind = TypeKind.Integer then
      build_intcast raw_val expected_ll_ty "int_coerce" !ce_builder
    else if raw_ty = double_type ce_ctx && expected_ll_ty = float_type ce_ctx
    then build_fptrunc raw_val expected_ll_ty "float_trunc" !ce_builder
    else if raw_ty = float_type ce_ctx && expected_ll_ty = double_type ce_ctx
    then build_fpext raw_val expected_ll_ty "float_ext" !ce_builder
    else if is_result_type raw_ty then
      let actual_ok_ty = match actual_ast_ty with TResult t -> t | t -> t in
      unwrap_result env loc actual_ok_ty expected_ast_ty expected_ll_ty raw_val
        is_unsigned_target
    else if is_interface_type expected_ll_ty then
      autobox_interface env actual_ast_ty expected_ast_ty expected_ll_ty raw_val
        raw_ty
    else if exp_kind = TypeKind.Pointer && raw_kind = TypeKind.Pointer then
      build_bitcast raw_val expected_ll_ty "ptr_cast" !ce_builder
    else raise (Error.cant_implicitly_cast loc)

  and unwrap_result env loc actual_ast_ty expected_ast_ty expected_ll_ty raw_val
      is_unsigned_target =
    let is_err = build_extractvalue raw_val 0 "is_err" !ce_builder in
    let the_func = block_parent (insertion_block !ce_builder) in
    let err_bb = append_block ce_ctx "unwrap_err" the_func in
    let ok_bb = append_block ce_ctx "unwrap_ok" the_func in
    let merge_bb = append_block ce_ctx "unwrap_merge" the_func in

    ignore (build_cond_br is_err err_bb ok_bb !ce_builder);
    position_at_end err_bb !ce_builder;
    let err_msg = build_extractvalue raw_val 2 "err_msg" !ce_builder in
    Utils.gen_panic env ce_ctx !ce_module !ce_builder "Uncaught Error: %s\n"
      [ err_msg ];
    position_at_end ok_bb !ce_builder;
    let ok_val = build_extractvalue raw_val 1 "ok_val" !ce_builder in
    let final_val =
      coerce_value env loc actual_ast_ty expected_ast_ty expected_ll_ty ok_val
        is_unsigned_target false
    in
    let final_ok_bb = insertion_block !ce_builder in
    ignore (build_br merge_bb !ce_builder);
    position_at_end merge_bb !ce_builder;
    if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
    else build_phi [ (final_val, final_ok_bb) ] "unwrap_res" !ce_builder

  let rec extract_property env loc current_val current_ast_ty current_ty props =
    if List.length props = 0 then current_val
    else
      let prop = List.hd props in
      let rest = List.tl props in
      let kind = classify_type current_ty in

      if kind <> TypeKind.Struct then
        raise (Error.cant_access_prop_on_nonstruct ~loc prop);

      let clean_name =
        try ast_base_type_name current_ast_ty
        with _ -> (
          match struct_name current_ty with
          | Some s_name ->
              if String.starts_with ~prefix:"struct." s_name then
                String.sub s_name 7 (String.length s_name - 7)
              else s_name
          | None -> raise (Error.cant_access_prop_on_nonstruct ~loc prop))
      in
      begin match Hashtbl.find_opt env.struct_registry clean_name with
      | Some (_, field_map, def_mod) ->
          let field_opt =
            List.find_opt (fun (n, _, _, _, _) -> n = prop) field_map
          in
          if Option.is_none field_opt then
            raise (Error.unknown_prop loc prop clean_name);
          let _, idx, _, next_ast_ty, is_pub = Option.get field_opt in
          if (not is_pub) && !(env.current_module) <> def_mod then
            raise (Error.cant_access_private_on_struct ~loc prop clean_name);
          let next_val =
            build_extractvalue current_val idx "proptmp" !ce_builder
          in
          let next_ty = (struct_element_types current_ty).(idx) in
          extract_property env loc next_val next_ast_ty next_ty rest
      | None -> begin
          let idx = try int_of_string prop with Failure _ -> -1 in
          let elems = struct_element_types current_ty in
          if idx < 0 || idx >= Array.length elems then
            raise (Error.tuple_index_out_bounds loc prop);
          let next_val =
            build_extractvalue current_val idx "tupleelem" !ce_builder
          in
          let next_ty = elems.(idx) in
          let next_ast_ty =
            match current_ast_ty with
            | TTuple ts -> List.nth ts idx
            | _ -> TUnknown
          in
          extract_property env loc next_val next_ast_ty next_ty rest
        end
      end

  let rec codegen env compile_stmt_cb (e : expr) =
    match e.node with
    | Void -> const_null (void_type ce_ctx)
    | Nil -> const_null (pointer_type ce_ctx)
    | Int n -> const_int (i32_type ce_ctx) n
    | Float f -> const_float (double_type ce_ctx) f
    | Bool b -> const_int (i1_type ce_ctx) (if b then 1 else 0)
    | Char c -> const_int (i8_type ce_ctx) (Char.code c)
    | String s -> build_global_stringptr s "strtmp" !ce_builder
    | Let name -> gen_let env compile_stmt_cb e.loc name
    | Call (name, targs, args) ->
        gen_call env compile_stmt_cb e.loc name targs args
    | Struct (name, type_args, fields) ->
        gen_struct env compile_stmt_cb e.loc name type_args fields
    | Tuple elems -> gen_tuple env compile_stmt_cb elems
    | Array (n, ty, elems) -> gen_array env compile_stmt_cb n ty elems
    | ArrayAccess (name, index_expr) ->
        gen_array_access env compile_stmt_cb e.loc name index_expr
    | Slice (ty, elems) -> gen_slice env compile_stmt_cb e.loc ty elems
    | If (cond, then_body, elif_branches, else_body) ->
        gen_if env compile_stmt_cb cond then_body elif_branches else_body
    | AnonFN (params, ret_ty, body) ->
        gen_anon_fn env compile_stmt_cb e.loc params ret_ty body
    | Catch (expr, err_name, catch_ty, body) ->
        gen_catch env compile_stmt_cb expr err_name catch_ty body
    | CatchExpr (expr, handler) ->
        gen_catch_expr env compile_stmt_cb e.loc expr handler
    | Ref ref_e -> gen_ref env e.loc ref_e
    | Deref deref_e -> gen_deref env compile_stmt_cb e.loc deref_e
    | Add (l, r) -> gen_binop env compile_stmt_cb `Add l r
    | Sub (l, r) -> gen_binop env compile_stmt_cb `Sub l r
    | Mul (l, r) -> gen_binop env compile_stmt_cb `Mul l r
    | Div (l, r) -> gen_binop env compile_stmt_cb `Div l r
    | Mod (l, r) -> gen_binop env compile_stmt_cb `Mod l r
    | Eq (l, r) -> gen_binop env compile_stmt_cb `Eq l r
    | Lt (l, r) -> gen_binop env compile_stmt_cb `Lt l r
    | Lte (l, r) -> gen_binop env compile_stmt_cb `Lte l r
    | Gt (l, r) -> gen_binop env compile_stmt_cb `Gt l r
    | Gte (l, r) -> gen_binop env compile_stmt_cb `Gte l r
    | And (l, r) -> gen_binop env compile_stmt_cb `And l r
    | Or (l, r) -> gen_binop env compile_stmt_cb `Or l r
    | Neg ex ->
        let v = codegen env compile_stmt_cb ex in
        if type_of v = double_type ce_ctx then
          build_fneg v "fnegtmp" !ce_builder
        else build_neg v "negtmp" !ce_builder
    | Not ex ->
        let v = codegen env compile_stmt_cb ex in
        if type_of v = i1_type ce_ctx then build_not v "nottmp" !ce_builder
        else raise (Error.cant_apply_operator e.loc "NOT (!)")

  and gen_let env compile_stmt_cb loc name =
    let builder_module =
      global_parent (block_parent (insertion_block !ce_builder))
    in
    match Hashtbl.find_opt env.named_values name with
    | Some (v, ast_ty, _) ->
        let actual_v =
          Utils.resolve_cross_module v builder_module
            (Types.llvm_type_of env ast_ty)
            name
        in
        build_load (Types.llvm_type_of env ast_ty) actual_v name !ce_builder
    | None -> (
        match Utils.lookup_function env name !ce_module with
        | Some f -> f
        | None ->
            if String.contains name '.' then
              let parts = String.split_on_char '.' name in
              let base_name = List.hd parts in
              let props = List.tl parts in
              let base_val, base_ast_ty =
                match Hashtbl.find_opt env.named_values base_name with
                | Some (v, ast_ty, _) ->
                    let actual_v =
                      Utils.resolve_cross_module v builder_module
                        (Types.llvm_type_of env ast_ty)
                        base_name
                    in
                    (actual_v, ast_ty)
                | None -> raise (Error.unknown_var_fn ~loc base_name)
              in
              let is_ptr =
                match base_ast_ty with TPointer _ -> true | _ -> false
              in
              let base_struct_ast_ty =
                match base_ast_ty with TPointer t -> t | t -> t
              in
              let base_val_loaded =
                build_load
                  (Types.llvm_type_of env base_ast_ty)
                  base_val base_name !ce_builder
              in
              let base_struct_val, base_struct_llty =
                if is_ptr then
                  let ll_struct_ty =
                    Types.llvm_type_of env base_struct_ast_ty
                  in
                  ( build_load ll_struct_ty base_val_loaded "auto_deref"
                      !ce_builder,
                    ll_struct_ty )
                else (base_val_loaded, Types.llvm_type_of env base_struct_ast_ty)
              in
              extract_property env loc base_struct_val base_struct_ast_ty
                base_struct_llty props
            else raise (Error.unknown_var_fn ~loc name))

  and process_args env compile_stmt_cb e_loc expected_tys param_ast_tys args
      offset_ll offset_ast n_reg_args =
    let is_variadic, var_ty =
      if List.length param_ast_tys > 0 then
        match List.nth param_ast_tys (List.length param_ast_tys - 1) with
        | TVariadic t -> (true, t)
        | _ -> (false, TUnknown)
      else (false, TUnknown)
    in
    if is_variadic then
      let reg_args = List.filteri (fun i _ -> i < n_reg_args) args in
      let var_args = List.filteri (fun i _ -> i >= n_reg_args) args in
      let reg_vals =
        List.mapi
          (fun i arg ->
            coerce_value env e_loc (infer_ast_type env arg)
              (List.nth param_ast_tys (i + offset_ast))
              expected_tys.(i + offset_ll)
              (codegen env compile_stmt_cb arg)
              false false)
          reg_args
      in
      let var_len = List.length var_args in
      let ll_elem_ty = Types.llvm_type_of env var_ty in

      let array_ptr =
        if var_len > 0 then begin
          let ptr_ty = pointer_type ce_ctx in
          let gc_malloc_ty = function_type ptr_ty [| i64_type ce_ctx |] in
          let gc_malloc_fn =
            match Utils.lookup_function env "GC_malloc" !ce_module with
            | Some f -> f
            | None -> declare_function "GC_malloc" gc_malloc_ty !ce_module
          in
          let size_val = size_of ll_elem_ty in
          let total_size =
            build_mul
              (const_int (i64_type ce_ctx) var_len)
              size_val "alloc_size" !ce_builder
          in
          let ptr_raw =
            build_call gc_malloc_ty gc_malloc_fn [| total_size |] "vararg_alloc"
              !ce_builder
          in
          let ptr = build_bitcast ptr_raw ptr_ty "vararg_ptr" !ce_builder in

          List.iteri
            (fun i arg_expr ->
              let arg_val = codegen env compile_stmt_cb arg_expr in
              let coerced =
                coerce_value env e_loc
                  (infer_ast_type env arg_expr)
                  var_ty ll_elem_ty arg_val false false
              in
              let gep =
                build_in_bounds_gep ll_elem_ty ptr
                  [| const_int (i32_type ce_ctx) i |]
                  "vararg_gep" !ce_builder
              in
              ignore (build_store coerced gep !ce_builder))
            var_args;
          ptr
        end
        else const_null (pointer_type ce_ctx)
      in
      let slice_ast_ty = TGenericInst ("slices.Slice", [ var_ty ]) in
      let slice_ll_ty = Types.llvm_type_of env slice_ast_ty in
      let s0 = const_null slice_ll_ty in
      let s1 = build_insertvalue s0 array_ptr 0 "slice_ptr" !ce_builder in
      let s2 =
        build_insertvalue s1
          (const_int (i32_type ce_ctx) var_len)
          1 "slice_len" !ce_builder
      in
      let slice_val =
        build_insertvalue s2
          (const_int (i32_type ce_ctx) var_len)
          2 "slice_cap" !ce_builder
      in
      reg_vals @ [ slice_val ]
    else
      List.mapi
        (fun i arg ->
          coerce_value env e_loc (infer_ast_type env arg)
            (List.nth param_ast_tys (i + offset_ast))
            expected_tys.(i + offset_ll)
            (codegen env compile_stmt_cb arg)
            false false)
        args

  and gen_call env compile_stmt_cb loc name targs args =
    let target_name =
      if targs = [] then name
      else if Hashtbl.mem env.fn_templates name then
        Types.instantiate_generic_fn env name targs
      else name
    in
    let builtin_opt = Builtin.get name in
    let direct_callee = Utils.lookup_function env name !ce_module in
    let generic_callee = Utils.lookup_function env target_name !ce_module in

    let is_fn_var =
      try
        match Infer.infer_ast_type env (Utils.mk_expr @@ Let name) with
        | TFn _ -> true
        | _ -> false
      with _ -> false
    in
    let is_method = String.contains name '.' in

    if Option.is_some builtin_opt then
      let builtin_fn = Option.get builtin_opt in
      let arg_vals = List.map (codegen env compile_stmt_cb) args in
      let targ_lltypes = List.map (Types.llvm_type_of env) targs in
      let arg_asts = List.map (Infer.infer_ast_type env) args in
      builtin_fn ce_ctx !ce_module !ce_builder name arg_vals targ_lltypes
        arg_asts targs
        (codegen env compile_stmt_cb)
        (Types.llvm_type_of env) (Infer.infer_ast_type env)
    else if Option.is_some direct_callee then
      let callee = Option.get direct_callee in
      let ft, param_ast_tys, _ = Hashtbl.find env.function_types name in
      let arg_vals =
        process_args env compile_stmt_cb loc (param_types ft) param_ast_tys args
          0 0
          (List.length param_ast_tys - 1)
      in
      let call_name =
        if return_type ft = void_type ce_ctx then "" else "calltmp"
      in
      let builder_module =
        global_parent (block_parent (insertion_block !ce_builder))
      in
      let actual_callee =
        Utils.resolve_cross_module callee builder_module ft (value_name callee)
      in
      build_call ft actual_callee (Array.of_list arg_vals) call_name !ce_builder
    else if Option.is_some generic_callee then
      let callee = Option.get generic_callee in
      let ft, param_ast_tys, _ = Hashtbl.find env.function_types target_name in
      let arg_vals =
        process_args env compile_stmt_cb loc (param_types ft) param_ast_tys args
          0 0
          (List.length param_ast_tys - 1)
      in
      let call_name =
        if return_type ft = void_type ce_ctx then "" else "calltmp"
      in
      let builder_module =
        global_parent (block_parent (insertion_block !ce_builder))
      in
      let actual_callee =
        Utils.resolve_cross_module callee builder_module ft (value_name callee)
      in
      build_call ft actual_callee (Array.of_list arg_vals) call_name !ce_builder
    else if is_fn_var then
      let fn_val = codegen env compile_stmt_cb (Utils.mk_expr @@ Let name) in
      match Infer.infer_ast_type env (Utils.mk_expr @@ Let name) with
      | TFn (param_tys, ret_ty) ->
          let expected_tys =
            Array.of_list
              (pointer_type ce_ctx
              :: List.map (Types.llvm_type_of env) param_tys)
          in
          let ft = function_type (Types.llvm_type_of env ret_ty) expected_tys in
          let fn_ptr_raw =
            build_extractvalue fn_val 0 "fn_ptr_raw" !ce_builder
          in
          let env_ptr = build_extractvalue fn_val 1 "env_ptr" !ce_builder in
          let arg_vals =
            process_args env compile_stmt_cb loc expected_tys param_tys args 1 0
              (List.length param_tys - 1)
          in
          let call_name = if ret_ty = TVoid then "" else "fnptr_calltmp" in
          build_call ft fn_ptr_raw
            (Array.of_list (env_ptr :: arg_vals))
            call_name !ce_builder
      | _ -> raise (Error.unknown_var_fn ~loc "<unnamed>")
    else if Hashtbl.mem env.fn_templates name then
      raise (Error.generic_requires_type ~loc name)
    else if is_method then
      gen_method_call env compile_stmt_cb loc name targs args
    else raise (Error.unknown_var_fn ~loc name)

  and gen_method_call env compile_stmt_cb loc name targs args =
    let last_dot_idx = String.rindex name '.' in
    let base_path = String.sub name 0 last_dot_idx in
    let method_name =
      String.sub name (last_dot_idx + 1) (String.length name - last_dot_idx - 1)
    in

    if
      Hashtbl.mem env.struct_registry base_path
      || Hashtbl.mem env.struct_templates base_path
    then (
      let is_struct_generic = Hashtbl.mem env.struct_templates base_path in
      let actual_base_path, method_targs =
        if is_struct_generic then
          let params, _, _ = Hashtbl.find env.struct_templates base_path in
          let n_params = List.length params in
          if n_params > 0 && List.length targs >= n_params then (
            let rec split_at n xs =
              if n = 0 then ([], xs)
              else
                match xs with
                | [] -> ([], [])
                | y :: ys ->
                    let l1, l2 = split_at (n - 1) ys in
                    (y :: l1, l2)
            in
            let struct_targs, remaining_targs = split_at n_params targs in
            ignore
              (Types.llvm_type_of env (TGenericInst (base_path, struct_targs)));

            (match !(env.process_pending_cb) with
            | Some cb -> cb ()
            | None -> ());

            let instantiated_name =
              base_path ^ "_"
              ^ String.concat "_" (List.map show_types struct_targs)
            in
            (instantiated_name, remaining_targs))
          else if n_params = 0 then (base_path, targs)
          else raise (Error.generic_requires_type base_path)
        else (base_path, targs)
      in

      let mangled_name = actual_base_path ^ "::" ^ method_name in
      (match Hashtbl.find_opt env.method_registry mangled_name with
      | Some (is_pub, def_mod) ->
          if (not is_pub) && !(env.current_module) <> def_mod then
            raise
              (Error.cant_access_private_on_struct ~loc method_name
                 actual_base_path)
      | None -> ());

      let target_name =
        if method_targs = [] then mangled_name
        else Types.instantiate_generic_fn env mangled_name method_targs
      in

      let callee =
        match Utils.lookup_function env target_name !ce_module with
        | Some c -> c
        | None -> raise (Error.unknown_method loc method_name actual_base_path)
      in
      let ft, param_ast_tys, _ =
        try Hashtbl.find env.function_types target_name
        with Not_found ->
          raise (Error.unknown_method loc method_name actual_base_path)
      in
      let arg_vals =
        process_args env compile_stmt_cb loc (param_types ft) param_ast_tys args
          0 0
          (List.length param_ast_tys - 1)
      in
      let call_name =
        if return_type ft = void_type ce_ctx then "" else "staticcalltmp"
      in
      let builder_module =
        global_parent (block_parent (insertion_block !ce_builder))
      in
      let actual_callee =
        Utils.resolve_cross_module callee builder_module ft (value_name callee)
      in
      build_call ft actual_callee (Array.of_list arg_vals) call_name !ce_builder)
    else
      let self_val =
        try codegen env compile_stmt_cb (Utils.mk_expr @@ Let base_path)
        with Error.Error _ -> raise (Error.unknown_fn loc name)
      in
      let self_ast_ty = infer_ast_type env (Utils.mk_expr @@ Let base_path) in
      let actual_ast_ty = match self_ast_ty with TPointer t -> t | t -> t in
      let actual_struct_ty = Types.llvm_type_of env actual_ast_ty in
      let is_self_ptr =
        match self_ast_ty with TPointer _ -> true | _ -> false
      in
      let clean_name =
        try ast_base_type_name actual_ast_ty
        with Not_found ->
          raise (Error.cant_access_prop_on_nonstruct ~loc method_name)
      in
      if Hashtbl.mem env.interface_registry clean_name then begin
        let sigs = Hashtbl.find env.interface_registry clean_name in
        let method_idx =
          let rec find_idx i = function
            | [] -> raise (Error.unknown_method loc method_name clean_name)
            | s :: rest ->
                if s.fn_name = method_name then i else find_idx (i + 1) rest
          in
          find_idx 0 sigs
        in
        let method_sig = List.nth sigs method_idx in

        let data_ptr = build_extractvalue self_val 0 "data_ptr" !ce_builder in
        let vtable_ptr =
          build_extractvalue self_val 1 "vtable_ptr" !ce_builder
        in

        let func_ptr_ptr =
          build_in_bounds_gep (pointer_type ce_ctx) vtable_ptr
            [| const_int (i32_type ce_ctx) method_idx |]
            "func_ptr_ptr" !ce_builder
        in
        let func_ptr =
          build_load (pointer_type ce_ctx) func_ptr_ptr "func_ptr" !ce_builder
        in

        let param_ast_tys =
          List.map (fun (p : param) -> p.ty) method_sig.params
        in
        let param_types_arr =
          Array.of_list
            (pointer_type ce_ctx
            :: List.map (Types.llvm_type_of env) param_ast_tys)
        in
        let ft =
          function_type
            (Types.llvm_type_of env method_sig.ret_ty)
            param_types_arr
        in

        let arg_vals =
          process_args env compile_stmt_cb loc param_types_arr param_ast_tys
            args 1 0
            (List.length param_ast_tys)
        in

        let all_args = Array.of_list (data_ptr :: arg_vals) in
        let call_name =
          if method_sig.ret_ty = TVoid then "" else "iface_call"
        in
        build_call ft func_ptr all_args call_name !ce_builder
      end
      else begin
        let mangled_name = clean_name ^ "::" ^ method_name in
        (match Hashtbl.find_opt env.method_registry mangled_name with
        | Some (is_pub, def_mod) ->
            if (not is_pub) && !(env.current_module) <> def_mod then
              raise
                (Error.cant_call_private_on_struct ~loc method_name clean_name)
        | None -> ());

        let target_name =
          if targs = [] then mangled_name
          else Types.instantiate_generic_fn env mangled_name targs
        in

        let callee =
          match Utils.lookup_function env target_name !ce_module with
          | Some c -> c
          | None -> raise (Error.unknown_method loc method_name clean_name)
        in
        let ft, param_ast_tys, _ =
          try Hashtbl.find env.function_types target_name
          with Not_found ->
            raise (Error.unknown_method loc method_name clean_name)
        in
        let expected_tys = param_types ft in
        let expected_self_ty = expected_tys.(0) in
        let expected_self_ast_ty = List.hd param_ast_tys in

        let get_ptr_to_name path =
          let builder_module =
            global_parent (block_parent (insertion_block !ce_builder))
          in
          match Hashtbl.find_opt env.named_values path with
          | Some (v, ast_ty, _) ->
              Utils.resolve_cross_module v builder_module
                (Types.llvm_type_of env ast_ty)
                path
          | None ->
              if String.contains path '.' then
                let parts = String.split_on_char '.' path in
                let base_name = List.hd parts in
                let v, ast_ty, _ =
                  try Hashtbl.find env.named_values base_name
                  with Not_found ->
                    raise (Error.unknown_var_fn ~loc base_name)
                in
                let is_ptr, base_struct_ast_ty =
                  match ast_ty with TPointer t -> (true, t) | t -> (false, t)
                in
                let actual_v =
                  Utils.resolve_cross_module v builder_module
                    (Types.llvm_type_of env ast_ty)
                    base_name
                in
                let base_ptr =
                  if is_ptr then
                    build_load (pointer_type ce_ctx) actual_v "auto_deref_ptr"
                      !ce_builder
                  else actual_v
                in
                resolve_property_ptr env Types.llvm_type_of base_ptr
                  (Types.llvm_type_of env base_struct_ast_ty)
                  base_struct_ast_ty (List.tl parts)
              else raise (Error.unknown_var_fn ~loc path)
        in

        let expects_ptr =
          match expected_self_ast_ty with TPointer _ -> true | _ -> false
        in
        let coerced_self =
          if expects_ptr then
            if is_self_ptr then self_val else get_ptr_to_name base_path
          else if is_self_ptr then
            build_load actual_struct_ty self_val "deref_self" !ce_builder
          else
            coerce_value env loc self_ast_ty expected_self_ast_ty
              expected_self_ty self_val false false
        in
        let arg_vals =
          process_args env compile_stmt_cb loc expected_tys param_ast_tys args 1
            1
            (List.length param_ast_tys - 2)
        in
        let all_args = Array.of_list (coerced_self :: arg_vals) in
        let call_name =
          if return_type ft = void_type ce_ctx then "" else "methodcalltmp"
        in
        let builder_module =
          global_parent (block_parent (insertion_block !ce_builder))
        in
        let actual_callee =
          Utils.resolve_cross_module callee builder_module ft
            (value_name callee)
        in
        build_call ft actual_callee all_args call_name !ce_builder
      end

  and gen_struct env compile_stmt_cb loc name type_args fields =
    if type_args <> [] then
      ignore (Types.llvm_type_of env (TGenericInst (name, type_args)));
    let mangled_name =
      if type_args = [] then name
      else name ^ "_" ^ String.concat "_" (List.map show_types type_args)
    in
    let llty, field_map, def_mod =
      try Hashtbl.find env.struct_registry mangled_name
      with Not_found -> raise (Error.cant_find_struct ~loc name)
    in
    let alloc = build_alloca llty "structtmp" !ce_builder in
    ignore (build_store (const_null llty) alloc !ce_builder);
    List.iter
      (fun (fname, fexpr) ->
        let name, fidx, _, f_ast_ty, is_pub =
          try List.find (fun (n, _, _, _, _) -> n = fname) field_map
          with Not_found -> raise (Error.unknown_prop loc fname mangled_name)
        in
        if (not is_pub) && !(env.current_module) <> def_mod then
          raise (Error.cant_access_private_on_struct ~loc fname name);

        let fptr = build_struct_gep llty alloc fidx "fieldptr" !ce_builder in
        let expected_ty = (struct_element_types llty).(fidx) in
        let raw_val = codegen env compile_stmt_cb fexpr in
        let val_to_store =
          coerce_value env loc (infer_ast_type env fexpr) f_ast_ty expected_ty
            raw_val false false
        in
        ignore (build_store val_to_store fptr !ce_builder))
      fields;
    build_load llty alloc "structload" !ce_builder

  and gen_tuple env compile_stmt_cb elems =
    let lltypes =
      List.map (fun e -> type_of (codegen env compile_stmt_cb e)) elems
    in
    let struct_ty = struct_type ce_ctx (Array.of_list lltypes) in
    let alloc = build_alloca struct_ty "tupletmp" !ce_builder in
    List.iteri
      (fun i e ->
        ignore
          (build_store
             (codegen env compile_stmt_cb e)
             (build_struct_gep struct_ty alloc i "tupleelem" !ce_builder)
             !ce_builder))
      elems;
    build_load struct_ty alloc "tupleload" !ce_builder

  and gen_array env compile_stmt_cb n ty elems =
    let arr_ty = array_type (Types.llvm_type_of env ty) n in
    let alloc = build_alloca arr_ty "arrtmp" !ce_builder in
    List.iteri
      (fun i e ->
        let ptr =
          build_gep arr_ty alloc
            [| const_int (i32_type ce_ctx) 0; const_int (i32_type ce_ctx) i |]
            "elemtmp" !ce_builder
        in
        ignore (build_store (codegen env compile_stmt_cb e) ptr !ce_builder))
      elems;
    build_load arr_ty alloc "arrload" !ce_builder

  and gen_array_access env compile_stmt_cb loc name index_expr =
    let array_ptr_val, array_ty =
      match Hashtbl.find_opt env.named_values name with
      | Some (v, ty, _) -> (v, ty)
      | None -> raise (Error.unknown_var_fn ~loc name)
    in
    let idx_val = codegen env compile_stmt_cb index_expr in
    match array_ty with
    | TArray _ ->
        let llvm_array_ty = Types.llvm_type_of env array_ty in
        let element_ptr =
          build_in_bounds_gep llvm_array_ty array_ptr_val
            [| const_int (i32_type ce_ctx) 0; idx_val |]
            "arrayidx" !ce_builder
        in
        build_load
          (element_type llvm_array_ty)
          element_ptr "loadtmp" !ce_builder
    | TGenericInst ("slices.Slice", [ elem_ast_ty ]) ->
        let slice_val =
          build_load
            (Types.llvm_type_of env array_ty)
            array_ptr_val "sliceload" !ce_builder
        in
        let data_ptr = build_extractvalue slice_val 0 "slice_ptr" !ce_builder in
        let elem_ll_ty = Types.llvm_type_of env elem_ast_ty in
        let element_ptr =
          build_in_bounds_gep elem_ll_ty data_ptr [| idx_val |] "sliceidx"
            !ce_builder
        in
        build_load elem_ll_ty element_ptr "loadtmp" !ce_builder
    | _ -> raise (Error.Error "Cannot index non-array and non-slice type")

  and gen_slice env compile_stmt_cb loc ty elems =
    let len = List.length elems in
    let slice_ast_ty = TGenericInst ("slices.Slice", [ ty ]) in
    let slice_ll_ty = Types.llvm_type_of env slice_ast_ty in
    let elem_ll_ty = Types.llvm_type_of env ty in

    let ptr_ty = pointer_type ce_ctx in

    let array_ptr =
      if len > 0 then begin
        let gc_malloc_ty = function_type ptr_ty [| i64_type ce_ctx |] in
        let gc_malloc_fn =
          match Utils.lookup_function env "GC_malloc" !ce_module with
          | Some f -> f
          | None -> declare_function "GC_malloc" gc_malloc_ty !ce_module
        in
        let size_val = size_of elem_ll_ty in
        let total_size =
          build_mul
            (const_int (i64_type ce_ctx) len)
            size_val "alloc_size" !ce_builder
        in
        let ptr_raw =
          build_call gc_malloc_ty gc_malloc_fn [| total_size |] "slice_alloc"
            !ce_builder
        in
        build_bitcast ptr_raw ptr_ty "slice_ptr" !ce_builder
      end
      else const_null ptr_ty
    in

    List.iteri
      (fun i arg_expr ->
        let arg_val = codegen env compile_stmt_cb arg_expr in
        let coerced =
          coerce_value env loc
            (infer_ast_type env arg_expr)
            ty elem_ll_ty arg_val false false
        in
        let gep =
          build_in_bounds_gep elem_ll_ty array_ptr
            [| const_int (i32_type ce_ctx) i |]
            "slice_gep" !ce_builder
        in
        ignore (build_store coerced gep !ce_builder))
      elems;

    let s0 = const_null slice_ll_ty in
    let s1 = build_insertvalue s0 array_ptr 0 "slice_ptr" !ce_builder in
    let s2 =
      build_insertvalue s1
        (const_int (i32_type ce_ctx) len)
        1 "slice_len" !ce_builder
    in
    build_insertvalue s2
      (const_int (i32_type ce_ctx) len)
      2 "slice_cap" !ce_builder

  and cb_yield env compile_stmt_cb stmts =
    let rec aux = function
      | [] -> const_null (void_type ce_ctx)
      | [ { node = Expr e; _ } ] -> codegen env compile_stmt_cb e
      | s :: rest ->
          ignore (compile_stmt_cb env s);
          aux rest
    in
    aux stmts

  and build_if_chain env compile_stmt_cb merge_bb incoming cond then_body
      elif_branches else_body =
    let cond_val = codegen env compile_stmt_cb cond in
    let[@warning "-8"] [ then_bb; next_bb ] =
      Utils.create_blocks ce_ctx !ce_builder [ "then"; "else_or_elif" ]
    in
    ignore (build_cond_br cond_val then_bb next_bb !ce_builder);

    position_at_end then_bb !ce_builder;
    let then_val = cb_yield env compile_stmt_cb then_body in
    let then_bb_end = insertion_block !ce_builder in
    if Option.is_none (block_terminator then_bb_end) then begin
      ignore (build_br merge_bb !ce_builder);
      incoming := (then_val, then_bb_end) :: !incoming
    end;

    position_at_end next_bb !ce_builder;
    if List.length elif_branches > 0 then
      let elif_c, elif_body = List.hd elif_branches in
      build_if_chain env compile_stmt_cb merge_bb incoming elif_c elif_body
        (List.tl elif_branches) else_body
    else
      let else_val =
        match else_body with
        | Some stmts -> cb_yield env compile_stmt_cb stmts
        | None -> const_null (void_type ce_ctx)
      in
      let else_bb_end = insertion_block !ce_builder in
      if Option.is_none (block_terminator else_bb_end) then begin
        ignore (build_br merge_bb !ce_builder);
        incoming := (else_val, else_bb_end) :: !incoming
      end

  and gen_if env compile_stmt_cb cond then_body elif_branches else_body =
    let the_function = block_parent (insertion_block !ce_builder) in
    let merge_bb = append_block ce_ctx "ifcont" the_function in
    let incoming = ref [] in

    build_if_chain env compile_stmt_cb merge_bb incoming cond then_body
      elif_branches else_body;

    position_at_end merge_bb !ce_builder;
    let incoming_list = List.rev !incoming in
    if incoming_list = [] then const_null (void_type ce_ctx)
    else
      let first_val, _ = List.hd incoming_list in
      if type_of first_val = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_phi incoming_list "iftmp" !ce_builder

  and gen_catch env compile_stmt_cb expr err_name catch_ty body =
    let res_val = codegen env compile_stmt_cb expr in
    let is_err = build_extractvalue res_val 0 "is_err" !ce_builder in
    let[@warning "-8"] [ err_bb; ok_bb; merge_bb ] =
      Utils.create_blocks ce_ctx !ce_builder
        [ "catch_err"; "catch_ok"; "catch_merge" ]
    in

    ignore (build_cond_br is_err err_bb ok_bb !ce_builder);

    position_at_end err_bb !ce_builder;
    let err_str = build_extractvalue res_val 2 "err_str" !ce_builder in
    let err_alloc = build_alloca (pointer_type ce_ctx) err_name !ce_builder in
    ignore (build_store err_str err_alloc !ce_builder);
    let old_val_opt = Hashtbl.find_opt env.named_values err_name in
    Hashtbl.add env.named_values err_name (err_alloc, TString, false);

    let catch_val_raw = cb_yield env compile_stmt_cb body in

    Hashtbl.remove env.named_values err_name;
    (match old_val_opt with
    | Some v -> Hashtbl.add env.named_values err_name v
    | None -> ());

    let catch_ty_ll = Types.llvm_type_of env catch_ty in

    let err_end_bb = insertion_block !ce_builder in
    let err_has_term =
      match block_terminator err_end_bb with None -> false | Some _ -> true
    in
    let catch_val =
      if err_has_term then const_null catch_ty_ll
      else if type_of catch_val_raw = void_type ce_ctx then
        const_null catch_ty_ll
      else
        coerce_value env expr.loc catch_ty catch_ty catch_ty_ll catch_val_raw
          false false
    in
    if not err_has_term then ignore (build_br merge_bb !ce_builder);

    position_at_end ok_bb !ce_builder;
    let ok_val =
      if catch_ty_ll = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_extractvalue res_val 1 "ok_val" !ce_builder
    in
    let ok_end_bb = insertion_block !ce_builder in
    ignore (build_br merge_bb !ce_builder);

    position_at_end merge_bb !ce_builder;
    if catch_ty_ll = void_type ce_ctx then const_null (void_type ce_ctx)
    else if not err_has_term then
      build_phi
        [ (catch_val, err_end_bb); (ok_val, ok_end_bb) ]
        "catch_res" !ce_builder
    else ok_val

  and gen_catch_expr env compile_stmt_cb loc expr handler =
    let res_val = codegen env compile_stmt_cb expr in
    let is_err = build_extractvalue res_val 0 "is_err" !ce_builder in
    let expected_ast_ty =
      match infer_ast_type env expr with TResult t -> t | t -> t
    in
    let expected_ll_ty = Types.llvm_type_of env expected_ast_ty in
    let the_func = block_parent (insertion_block !ce_builder) in
    let err_bb = append_block ce_ctx "catch_expr_err" the_func in
    let ok_bb = append_block ce_ctx "catch_expr_ok" the_func in
    let merge_bb = append_block ce_ctx "catch_expr_merge" the_func in

    ignore (build_cond_br is_err err_bb ok_bb !ce_builder);
    position_at_end err_bb !ce_builder;

    let err_str = build_extractvalue res_val 2 "err_str" !ce_builder in
    let handler_val = codegen env compile_stmt_cb handler in
    let is_direct_fn =
      match handler.node with
      | Let name ->
          Hashtbl.mem env.function_types name
          && not (Hashtbl.mem env.named_values name)
      | _ -> false
    in

    let catch_val_raw =
      if is_direct_fn then
        let name = match handler.node with Let n -> n | _ -> "" in
        let ft, _, _ = Hashtbl.find env.function_types name in
        let call_name =
          if expected_ll_ty = void_type ce_ctx then "" else "catch_call_tmp"
        in
        build_call ft handler_val [| err_str |] call_name !ce_builder
      else
        let is_anon_fn =
          match infer_ast_type env handler with TFn _ -> true | _ -> false
        in
        if is_anon_fn then
          let env_ptr =
            build_extractvalue handler_val 1 "env_ptr" !ce_builder
          in
          let fn_ptr_raw =
            build_extractvalue handler_val 0 "fn_ptr_raw" !ce_builder
          in
          let param_tys =
            match infer_ast_type env handler with TFn (p, _) -> p | _ -> []
          in
          let ret_ty =
            match infer_ast_type env handler with TFn (_, r) -> r | _ -> TVoid
          in
          let expected_tys =
            Array.of_list
              (pointer_type ce_ctx
              :: List.map (Types.llvm_type_of env) param_tys)
          in
          let ft = function_type (Types.llvm_type_of env ret_ty) expected_tys in
          let call_name =
            if expected_ll_ty = void_type ce_ctx then "" else "catch_call_tmp"
          in
          build_call ft fn_ptr_raw [| env_ptr; err_str |] call_name !ce_builder
        else raise (Error.catch_handler_must_fn loc)
    in
    let catch_val =
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else
        let actual_handler_ty =
          match infer_ast_type env handler with TFn (_, r) -> r | t -> t
        in
        coerce_value env loc actual_handler_ty expected_ast_ty expected_ll_ty
          catch_val_raw false false
    in
    let err_end_bb = insertion_block !ce_builder in
    ignore (build_br merge_bb !ce_builder);

    position_at_end ok_bb !ce_builder;
    let ok_val =
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_extractvalue res_val 1 "ok_val" !ce_builder
    in
    let ok_end_bb = insertion_block !ce_builder in
    ignore (build_br merge_bb !ce_builder);

    position_at_end merge_bb !ce_builder;
    if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
    else
      build_phi
        [ (catch_val, err_end_bb); (ok_val, ok_end_bb) ]
        "catch_expr_res" !ce_builder

  and gen_anon_fn env compile_stmt_cb loc params ret_ty body =
    let anon_id = Oo.id object end in
    let actual_name = Printf.sprintf "__anon_fn_%d" anon_id in
    let was_res = !(env.current_fn_is_res) in
    let was_ret_ty = !(env.current_fn_ret_ty) in
    let old_bb = insertion_block !ce_builder in

    (env.current_fn_is_res := match ret_ty with TResult _ -> true | _ -> false);
    env.current_fn_ret_ty := Types.llvm_type_of env ret_ty;

    let live_vars =
      Hashtbl.fold
        (fun k (v, ty, is_mut) acc -> (k, v, ty, is_mut) :: acc)
        env.named_values []
    in
    let env_types =
      Array.of_list
        (List.map (fun (_, _, ty, _) -> Types.llvm_type_of env ty) live_vars)
    in
    let env_struct_ty = struct_type ce_ctx env_types in

    let gc_malloc_ty =
      function_type (pointer_type ce_ctx) [| i64_type ce_ctx |]
    in
    let gc_malloc_fn =
      match Utils.lookup_function env "GC_malloc" !ce_module with
      | Some f -> f
      | None -> declare_function "GC_malloc" gc_malloc_ty !ce_module
    in
    let env_ptr_raw =
      build_call gc_malloc_ty gc_malloc_fn
        [| size_of env_struct_ty |]
        "env_alloc" !ce_builder
    in
    let env_ptr =
      build_bitcast env_ptr_raw (pointer_type ce_ctx) "env_ptr" !ce_builder
    in

    let builder_module =
      global_parent (block_parent (insertion_block !ce_builder))
    in
    List.iteri
      (fun i (k, v, ty, _) ->
        let gep =
          build_struct_gep env_struct_ty env_ptr i "env_gep" !ce_builder
        in
        let actual_v =
          Utils.resolve_cross_module v builder_module
            (Types.llvm_type_of env ty)
            k
        in
        let loaded_val =
          build_load
            (Types.llvm_type_of env ty)
            actual_v "capture_load" !ce_builder
        in
        ignore (build_store loaded_val gep !ce_builder))
      live_vars;

    let param_types =
      Array.of_list
        (pointer_type ce_ctx
        :: List.map (fun (p : param) -> Types.llvm_type_of env p.ty) params)
    in
    let ft = function_type (Types.llvm_type_of env ret_ty) param_types in
    Hashtbl.replace env.function_types actual_name
      (ft, List.map (fun (p : param) -> p.ty) params, ret_ty);

    let f = declare_function actual_name ft !ce_module in
    set_linkage Linkage.Internal f;
    let bb = append_block ce_ctx "entry" f in
    position_at_end bb !ce_builder;

    let old_named_values = Hashtbl.copy env.named_values in
    Hashtbl.clear env.named_values;
    let inner_env_ptr =
      build_bitcast (param f 0) (pointer_type ce_ctx) "inner_env" !ce_builder
    in

    List.iteri
      (fun i (k, _, ty, is_mut) ->
        let val_ty = Types.llvm_type_of env ty in
        let gep =
          build_struct_gep env_struct_ty inner_env_ptr i "env_gep" !ce_builder
        in
        let loaded_val = build_load val_ty gep "env_load" !ce_builder in
        let local_alloca = build_alloca val_ty k !ce_builder in
        ignore (build_store loaded_val local_alloca !ce_builder);
        Hashtbl.add env.named_values k (local_alloca, ty, is_mut))
      live_vars;

    Array.iteri
      (fun i a ->
        if i > 0 then begin
          let real_i = i - 1 in
          let n = (List.nth params real_i).param_name in
          let p_ty = (List.nth params real_i).ty in
          let alloca =
            build_alloca (Types.llvm_type_of env p_ty) n !ce_builder
          in
          ignore (build_store a alloca !ce_builder);
          Hashtbl.add env.named_values n (alloca, p_ty, false)
        end)
      (Llvm.params f);

    List.iter
      (fun s ->
        if Option.is_none (block_terminator (insertion_block !ce_builder)) then
          ignore (compile_stmt_cb env s))
      body;

    let current_bb = insertion_block !ce_builder in
    (match block_terminator current_bb with
    | Some _ -> ()
    | None ->
        if ret_ty = TVoid || !(env.current_fn_is_res) then
          ignore
            (Utils.Stmt.gen_return env !ce_builder ce_ctx
               (const_null (void_type ce_ctx)))
        else raise (Error.function_missing_return loc "<unnamed>"));

    Hashtbl.clear env.named_values;
    Hashtbl.iter (fun k v -> Hashtbl.add env.named_values k v) old_named_values;
    env.current_fn_is_res := was_res;
    env.current_fn_ret_ty := was_ret_ty;
    position_at_end old_bb !ce_builder;

    let closure_struct_ty =
      struct_type ce_ctx [| pointer_type ce_ctx; pointer_type ce_ctx |]
    in
    let closure_val0 =
      build_insertvalue
        (const_null closure_struct_ty)
        (build_bitcast f (pointer_type ce_ctx) "fn_cast" !ce_builder)
        0 "closure0" !ce_builder
    in
    build_insertvalue closure_val0 env_ptr 1 "closure" !ce_builder

  and gen_ref env loc ref_e =
    match ref_e.node with
    | Let name -> (
        let builder_module =
          global_parent (block_parent (insertion_block !ce_builder))
        in
        match Hashtbl.find_opt env.named_values name with
        | Some (v, ast_ty, _) ->
            Utils.resolve_cross_module v builder_module
              (Types.llvm_type_of env ast_ty)
              name
        | None ->
            if String.contains name '.' then
              let parts = String.split_on_char '.' name in
              let base_name = List.hd parts in
              let v, ast_ty, _ =
                try Hashtbl.find env.named_values base_name
                with Not_found -> raise (Error.unknown_var_fn ~loc base_name)
              in
              let is_ptr, base_struct_ast_ty =
                match ast_ty with TPointer t -> (true, t) | t -> (false, t)
              in
              let actual_v =
                Utils.resolve_cross_module v builder_module
                  (Types.llvm_type_of env ast_ty)
                  base_name
              in
              let base_ptr =
                if is_ptr then
                  build_load
                    (Types.llvm_type_of env ast_ty)
                    actual_v "auto_deref_ptr" !ce_builder
                else actual_v
              in
              resolve_property_ptr env Types.llvm_type_of base_ptr
                (Types.llvm_type_of env base_struct_ast_ty)
                base_struct_ast_ty (List.tl parts)
            else raise (Error.unknown_var_fn ~loc name))
    | _ -> raise (Error.cant_reference_nonvar loc)

  and gen_deref env compile_stmt_cb loc deref_e =
    let ptr_val = codegen env compile_stmt_cb deref_e in
    let ptr_ast_ty = infer_ast_type env deref_e in
    let inner_ty =
      match ptr_ast_ty with
      | TPointer t -> t
      | TString -> TInt (8, Unsigned)
      | _ -> raise (Error.cant_dereference_nonpointer loc)
    in
    build_load (Types.llvm_type_of env inner_ty) ptr_val "dereftmp" !ce_builder

  and gen_binop env compile_stmt_cb op l r =
    let lv, rv =
      (codegen env compile_stmt_cb l, codegen env compile_stmt_cb r)
    in
    Utils.Expr.gen_binary_op op lv rv (infer_ast_type env l)
end
