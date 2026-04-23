open Llvm
open Ce_parser.Ast
open State
open Utils
open Infer
open Codegen

module Make (Types : TYPES) : EXPR = struct
  exception Error of string

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
      is_unsigned_target && (not is_unsigned_source)
      && classify_type raw_ty = TypeKind.Integer
    then
      let needs_runtime_check =
        match int64_of_const raw_val with
        | Some v ->
            let bw = integer_bitwidth raw_ty in
            if bw <= 64 then
              let sign_bit = Int64.shift_left 1L (bw - 1) in
              if Int64.logand v sign_bit <> 0L then
                raise
                  (Utils.mk_error loc
                     "Cannot assign negative value to unsigned type")
              else false
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

  let autobox_interface expected_ll_ty raw_val raw_ty =
    let actual_raw_val, actual_raw_ty =
      if classify_type raw_ty = TypeKind.Float then
        ( build_fpext raw_val (double_type ce_ctx) "box_fext" !ce_builder,
          double_type ce_ctx )
      else (raw_val, raw_ty)
    in
    let malloc_val = build_malloc actual_raw_ty "autobox_malloc" !ce_builder in
    ignore (build_store actual_raw_val malloc_val !ce_builder);
    let ptr_ty = pointer_type ce_ctx in
    let data_ptr = build_bitcast malloc_val ptr_ty "autobox_data" !ce_builder in
    let type_tag =
      match classify_type actual_raw_ty with
      | TypeKind.Integer ->
          let bw = integer_bitwidth actual_raw_ty in
          if bw = 1 then 3 else if bw = 8 then 5 else 1
      | TypeKind.Double -> 2
      | TypeKind.Pointer -> 4
      | _ -> 0
    in
    let vtable_ptr =
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

  let rec coerce_value env loc expected_ll_ty raw_val is_unsigned_target
      is_unsigned_source =
    let raw_ty = type_of raw_val in
    check_unsigned_bounds env loc is_unsigned_target is_unsigned_source raw_ty
      raw_val;

    if raw_ty = expected_ll_ty then raw_val
    else if
      classify_type raw_ty = TypeKind.Integer
      && classify_type expected_ll_ty = TypeKind.Integer
    then build_intcast raw_val expected_ll_ty "int_coerce" !ce_builder
    else if raw_ty = double_type ce_ctx && expected_ll_ty = float_type ce_ctx
    then build_fptrunc raw_val expected_ll_ty "float_trunc" !ce_builder
    else if raw_ty = float_type ce_ctx && expected_ll_ty = double_type ce_ctx
    then build_fpext raw_val expected_ll_ty "float_ext" !ce_builder
    else if is_result_type raw_ty then
      unwrap_result env loc expected_ll_ty raw_val is_unsigned_target
    else if is_interface_type expected_ll_ty then
      autobox_interface expected_ll_ty raw_val raw_ty
    else if
      classify_type expected_ll_ty = TypeKind.Pointer
      && classify_type raw_ty = TypeKind.Pointer
    then build_bitcast raw_val expected_ll_ty "ptr_cast" !ce_builder
    else
      raise
        (Utils.mk_error loc
           "Type mismatch: Could not implicitly cast value to expected type")

  and unwrap_result env loc expected_ll_ty raw_val is_unsigned_target =
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
      coerce_value env loc expected_ll_ty ok_val is_unsigned_target false
    in
    let final_ok_bb = insertion_block !ce_builder in
    ignore (build_br merge_bb !ce_builder);

    position_at_end merge_bb !ce_builder;
    if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
    else build_phi [ (final_val, final_ok_bb) ] "unwrap_res" !ce_builder

  let rec extract_property env loc current_val current_ty props =
    match props with
    | [] -> current_val
    | prop :: rest -> (
        match classify_type current_ty with
        | TypeKind.Struct -> (
            let struct_name_opt = struct_name current_ty in
            match struct_name_opt with
            | Some s_name -> (
                let clean_name =
                  if String.starts_with ~prefix:"struct." s_name then
                    String.sub s_name 7 (String.length s_name - 7)
                  else s_name
                in
                match Hashtbl.find_opt env.struct_registry clean_name with
                | Some (_, field_map, def_mod) -> (
                    try
                      let _, idx, _, _, is_pub =
                        List.find (fun (n, _, _, _, _) -> n = prop) field_map
                      in
                      if (not is_pub) && !(env.current_module) <> def_mod then
                        raise
                          (Utils.mk_error loc
                             ("Cannot access private property '" ^ prop
                            ^ "' on struct '" ^ clean_name ^ "'"));

                      let next_val =
                        build_extractvalue current_val idx "proptmp" !ce_builder
                      in
                      let next_ty = (struct_element_types current_ty).(idx) in
                      extract_property env loc next_val next_ty rest
                    with Not_found ->
                      raise
                        (Utils.mk_error loc
                           ("Unknown property '" ^ prop ^ "' on struct '"
                          ^ clean_name ^ "'")))
                | None ->
                    raise
                      (Utils.mk_error loc
                         ("Could not find struct definition for '" ^ clean_name
                        ^ "'")))
            | None -> (
                try
                  let idx = int_of_string prop in
                  let elems = struct_element_types current_ty in
                  if idx < 0 || idx >= Array.length elems then
                    raise
                      (Utils.mk_error loc
                         ("Tuple index out of bounds: " ^ prop));
                  let next_val =
                    build_extractvalue current_val idx "tupleelem" !ce_builder
                  in
                  let next_ty = elems.(idx) in
                  extract_property env loc next_val next_ty rest
                with Failure _ ->
                  raise
                    (Utils.mk_error loc
                       ("Cannot access non-integer property '" ^ prop
                      ^ "' on a tuple"))))
        | _ ->
            raise
              (Utils.mk_error loc
                 ("Cannot access property '" ^ prop ^ "' on non-struct type")))

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
        else
          raise
            (Utils.mk_error e.loc
               "NOT operator (!) can only be applied to boolean values")

  and gen_let env _compile_stmt_cb loc name =
    if String.contains name '.' then
      let parts = String.split_on_char '.' name in
      let base_name = List.hd parts in
      let props = List.tl parts in
      match Hashtbl.find_opt env.named_values base_name with
      | Some (v, ast_ty, _) ->
          let is_ptr, base_struct_ast_ty =
            match ast_ty with TPointer t -> (true, t) | t -> (false, t)
          in
          let base_val_loaded =
            build_load (Types.llvm_type_of env ast_ty) v base_name !ce_builder
          in
          let base_struct_val, base_struct_llty =
            if is_ptr then
              let ll_struct_ty = Types.llvm_type_of env base_struct_ast_ty in
              ( build_load ll_struct_ty base_val_loaded "auto_deref" !ce_builder,
                ll_struct_ty )
            else (base_val_loaded, Types.llvm_type_of env base_struct_ast_ty)
          in
          extract_property env loc base_struct_val base_struct_llty props
      | None -> (
          match lookup_function env name !ce_module with
          | Some f -> f
          | None ->
              raise
                (Utils.mk_error loc ("Unknown variable or function: " ^ name)))
    else
      match Hashtbl.find_opt env.named_values name with
      | Some (v, ast_ty, _) ->
          build_load (Types.llvm_type_of env ast_ty) v name !ce_builder
      | None -> (
          match lookup_function env name !ce_module with
          | Some f -> f
          | None ->
              raise
                (Utils.mk_error loc ("Unknown variable or function: " ^ name)))

  and process_args env compile_stmt_cb e_loc expected_tys param_ast_tys args
      offset_ll n_reg_args =
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
            coerce_value env e_loc
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
            match lookup_function env "GC_malloc" !ce_module with
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
                coerce_value env e_loc ll_elem_ty arg_val false false
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
          coerce_value env e_loc
            expected_tys.(i + offset_ll)
            (codegen env compile_stmt_cb arg)
            false false)
        args

  and gen_call env compile_stmt_cb loc name targs args =
    match Builtin.get name with
    | Some builtin_fn ->
        let arg_vals = List.map (codegen env compile_stmt_cb) args in
        let targ_lltypes = List.map (Types.llvm_type_of env) targs in
        let arg_asts = List.map (Infer.infer_ast_type env) args in
        builtin_fn ce_ctx !ce_module !ce_builder name arg_vals targ_lltypes
          arg_asts targs
          (codegen env compile_stmt_cb)
          (Types.llvm_type_of env) (Infer.infer_ast_type env)
    | None -> (
        let target_name =
          if targs = [] then name
          else Types.instantiate_generic_fn env name targs
        in

        match lookup_function env name !ce_module with
        | Some callee ->
            let ft, param_ast_tys, _ = Hashtbl.find env.function_types name in
            let expected_tys = param_types ft in
            let arg_vals =
              process_args env compile_stmt_cb loc expected_tys param_ast_tys
                args 0
                (List.length param_ast_tys - 1)
            in
            let call_name =
              if return_type ft = void_type ce_ctx then "" else "calltmp"
            in
            build_call ft callee (Array.of_list arg_vals) call_name !ce_builder
        | None -> (
            match lookup_function env target_name !ce_module with
            | Some callee ->
                let ft, param_ast_tys, _ =
                  Hashtbl.find env.function_types target_name
                in
                let expected_tys = param_types ft in
                let arg_vals =
                  process_args env compile_stmt_cb loc expected_tys
                    param_ast_tys args 0
                    (List.length param_ast_tys - 1)
                in
                let call_name =
                  if return_type ft = void_type ce_ctx then "" else "calltmp"
                in
                build_call ft callee (Array.of_list arg_vals) call_name
                  !ce_builder
            | None ->
                let is_fn_var =
                  try
                    match infer_ast_type env (Utils.mk_expr @@ Let name) with
                    | TFn _ -> true
                    | _ -> false
                  with _ -> false
                in
                if is_fn_var then
                  let fn_val =
                    codegen env compile_stmt_cb (Utils.mk_expr @@ Let name)
                  in
                  match
                    Infer.infer_ast_type env (Utils.mk_expr @@ Let name)
                  with
                  | TFn (param_tys, ret_ty) ->
                      let expected_tys =
                        Array.of_list
                          (pointer_type ce_ctx
                          :: List.map (Types.llvm_type_of env) param_tys)
                      in
                      let ft =
                        function_type
                          (Types.llvm_type_of env ret_ty)
                          expected_tys
                      in
                      let fn_ptr_raw =
                        build_extractvalue fn_val 0 "fn_ptr_raw" !ce_builder
                      in
                      let env_ptr =
                        build_extractvalue fn_val 1 "env_ptr" !ce_builder
                      in
                      let arg_vals =
                        process_args env compile_stmt_cb loc expected_tys
                          param_tys args 1
                          (List.length param_tys - 1)
                      in
                      let call_name =
                        if ret_ty = TVoid then "" else "fnptr_calltmp"
                      in
                      build_call ft fn_ptr_raw
                        (Array.of_list (env_ptr :: arg_vals))
                        call_name !ce_builder
                  | _ -> raise (Utils.mk_error loc "Unreachable")
                else if Hashtbl.mem env.fn_templates name then
                  raise
                    (Utils.mk_error loc
                       ("Function '" ^ name
                      ^ "' is generic and requires type arguments"))
                else if String.contains name '.' then (
                  let last_dot_idx = String.rindex name '.' in
                  let base_path = String.sub name 0 last_dot_idx in
                  let method_name =
                    String.sub name (last_dot_idx + 1)
                      (String.length name - last_dot_idx - 1)
                  in

                  if Hashtbl.mem env.struct_registry base_path then (
                    let mangled_name = base_path ^ "::" ^ method_name in
                    (match
                       Hashtbl.find_opt env.method_registry mangled_name
                     with
                    | Some (is_pub, def_mod) ->
                        if (not is_pub) && !(env.current_module) <> def_mod then
                          raise
                            (Utils.mk_error loc
                               ("Cannot call private method '" ^ method_name
                              ^ "' on struct '" ^ base_path ^ "'"))
                    | None -> ());

                    let callee =
                      match lookup_function env mangled_name !ce_module with
                      | Some c -> c
                      | None ->
                          raise
                            (Utils.mk_error loc
                               ("Unknown method '" ^ method_name
                              ^ "' on struct '" ^ base_path ^ "'"))
                    in
                    let ft, param_ast_tys, _ =
                      Hashtbl.find env.function_types mangled_name
                    in
                    let expected_tys = param_types ft in
                    let arg_vals =
                      process_args env compile_stmt_cb loc expected_tys
                        param_ast_tys args 0
                        (List.length param_ast_tys - 1)
                    in
                    let call_name =
                      if return_type ft = void_type ce_ctx then ""
                      else "staticcalltmp"
                    in
                    build_call ft callee (Array.of_list arg_vals) call_name
                      !ce_builder)
                  else
                    let self_val =
                      try
                        codegen env compile_stmt_cb
                          (Utils.mk_expr @@ Let base_path)
                      with Error _ ->
                        raise
                          (Utils.mk_error loc
                             ("Unknown function or method: '" ^ name ^ "'"))
                    in
                    let self_ty_llvm = type_of self_val in
                    let actual_struct_ty, is_self_ptr =
                      if classify_type self_ty_llvm = TypeKind.Pointer then
                        (element_type self_ty_llvm, true)
                      else (self_ty_llvm, false)
                    in
                    let self_ast_ty =
                      infer_ast_type env (Utils.mk_expr @@ Let base_path)
                    in
                    let actual_ast_ty =
                      match self_ast_ty with TPointer t -> t | t -> t
                    in
                    let clean_name =
                      try ast_base_type_name actual_ast_ty
                      with Not_found -> (
                        match struct_name actual_struct_ty with
                        | Some s_name ->
                            if String.starts_with ~prefix:"struct." s_name then
                              String.sub s_name 7 (String.length s_name - 7)
                            else s_name
                        | None ->
                            raise
                              (Utils.mk_error loc
                                 ("Cannot call method '" ^ method_name
                                ^ "' on a non-struct type")))
                    in
                    let mangled_name = clean_name ^ "::" ^ method_name in
                    (match
                       Hashtbl.find_opt env.method_registry mangled_name
                     with
                    | Some (is_pub, def_mod) ->
                        if (not is_pub) && !(env.current_module) <> def_mod then
                          raise
                            (Utils.mk_error loc
                               ("Cannot call private method '" ^ method_name
                              ^ "' on type '" ^ clean_name ^ "'"))
                    | None -> ());

                    let callee =
                      match lookup_function env mangled_name !ce_module with
                      | Some c -> c
                      | None ->
                          raise
                            (Utils.mk_error loc
                               ("Unknown method '" ^ method_name ^ "' on type '"
                              ^ clean_name ^ "'"))
                    in
                    let ft, param_ast_tys, _ =
                      Hashtbl.find env.function_types mangled_name
                    in
                    let expected_tys = param_types ft in
                    let expected_self_ty = expected_tys.(0) in

                    let coerced_self =
                      if classify_type expected_self_ty = TypeKind.Pointer then
                        if is_self_ptr then self_val
                        else
                          let get_ptr_to_name path =
                            if String.contains path '.' then
                              let parts = String.split_on_char '.' path in
                              let base_name = List.hd parts in
                              let v, ast_ty, _ =
                                Hashtbl.find env.named_values base_name
                              in
                              let is_ptr, base_struct_ast_ty =
                                match ast_ty with
                                | TPointer t -> (true, t)
                                | t -> (false, t)
                              in
                              let base_ptr =
                                if is_ptr then
                                  build_load
                                    (Types.llvm_type_of env ast_ty)
                                    v "auto_deref_ptr" !ce_builder
                                else v
                              in
                              resolve_property_ptr env base_ptr
                                (Types.llvm_type_of env base_struct_ast_ty)
                                (List.tl parts)
                            else
                              let v, _, _ =
                                Hashtbl.find env.named_values path
                              in
                              v
                          in
                          get_ptr_to_name base_path
                      else if is_self_ptr then
                        build_load actual_struct_ty self_val "deref_self"
                          !ce_builder
                      else
                        coerce_value env loc expected_self_ty self_val false
                          false
                    in
                    let arg_vals =
                      process_args env compile_stmt_cb loc expected_tys
                        param_ast_tys args 1
                        (List.length param_ast_tys - 2)
                    in
                    let all_args = Array.of_list (coerced_self :: arg_vals) in
                    let call_name =
                      if return_type ft = void_type ce_ctx then ""
                      else "methodcalltmp"
                    in
                    build_call ft callee all_args call_name !ce_builder)
                else raise (Utils.mk_error loc ("Unknown function: " ^ name))))

  and gen_struct env compile_stmt_cb loc name type_args fields =
    if type_args <> [] then
      ignore (Types.llvm_type_of env (TGenericInst (name, type_args)));
    let mangled_name =
      if type_args = [] then name
      else name ^ "_" ^ String.concat "_" (List.map show_types type_args)
    in
    let llty, field_map, def_mod =
      try Hashtbl.find env.struct_registry mangled_name
      with Not_found ->
        raise
          (Utils.mk_error loc
             ("Cannot find struct '" ^ name ^ "' for instantiation"))
    in
    let alloc = build_alloca llty "structtmp" !ce_builder in
    ignore (build_store (const_null llty) alloc !ce_builder);
    List.iter
      (fun (fname, fexpr) ->
        let _, fidx, _, _, is_pub =
          List.find (fun (n, _, _, _, _) -> n = fname) field_map
        in
        if (not is_pub) && !(env.current_module) <> def_mod then
          raise
            (Utils.mk_error loc
               ("Cannot initialize private property '" ^ fname ^ "' on struct"));

        let fptr = build_struct_gep llty alloc fidx "fieldptr" !ce_builder in
        let expected_ty = (struct_element_types llty).(fidx) in
        let raw_val = codegen env compile_stmt_cb fexpr in
        let val_to_store =
          coerce_value env loc expected_ty raw_val false false
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
      | None -> raise (Utils.mk_error loc ("Array '" ^ name ^ "' not found"))
    in
    let llvm_array_ty = Types.llvm_type_of env array_ty in
    let idx_val = codegen env compile_stmt_cb index_expr in
    let element_ptr =
      build_in_bounds_gep llvm_array_ty array_ptr_val
        [| const_int (i32_type ce_ctx) 0; idx_val |]
        "arrayidx" !ce_builder
    in
    build_load (element_type llvm_array_ty) element_ptr "loadtmp" !ce_builder

  and gen_if env compile_stmt_cb cond then_body elif_branches else_body =
    let the_function = block_parent (insertion_block !ce_builder) in
    let merge_bb = append_block ce_ctx "ifcont" the_function in
    let cb_yield stmts =
      let rec aux = function
        | [] -> const_null (void_type ce_ctx)
        | [ { node = Expr e; _ } ] -> codegen env compile_stmt_cb e
        | s :: rest ->
            ignore (compile_stmt_cb env s);
            aux rest
      in
      aux stmts
    in
    let phi_incoming = ref [] in
    let rec build_if c body rest_elifs else_b =
      let cond_val = codegen env compile_stmt_cb c in
      let[@warning "-8"] [ then_bb; next_bb ] =
        Utils.create_blocks ce_ctx !ce_builder [ "then"; "else_or_elif" ]
      in
      ignore (build_cond_br cond_val then_bb next_bb !ce_builder);

      position_at_end then_bb !ce_builder;
      let then_val = cb_yield body in
      let then_bb_end = insertion_block !ce_builder in
      (match block_terminator then_bb_end with
      | None ->
          ignore (build_br merge_bb !ce_builder);
          phi_incoming := (then_val, then_bb_end) :: !phi_incoming
      | Some _ -> ());

      position_at_end next_bb !ce_builder;
      match rest_elifs with
      | (elif_c, elif_body) :: rest -> build_if elif_c elif_body rest else_b
      | [] -> (
          let else_val =
            match else_b with
            | Some stmts -> cb_yield stmts
            | None -> const_null (void_type ce_ctx)
          in
          let else_bb_end = insertion_block !ce_builder in
          match block_terminator else_bb_end with
          | None ->
              ignore (build_br merge_bb !ce_builder);
              phi_incoming := (else_val, else_bb_end) :: !phi_incoming
          | Some _ -> ())
    in
    build_if cond then_body elif_branches else_body;
    position_at_end merge_bb !ce_builder;
    let incoming = List.rev !phi_incoming in
    if incoming = [] then const_null (void_type ce_ctx)
    else
      let first_val, _ = List.hd incoming in
      if type_of first_val = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_phi incoming "iftmp" !ce_builder

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

    let catch_ty_ll = Types.llvm_type_of env catch_ty in
    let catch_val = ref (const_null catch_ty_ll) in
    List.iter
      (function
        | { node = Return e } -> catch_val := codegen env compile_stmt_cb e
        | s -> ignore (compile_stmt_cb env s))
      body;

    Hashtbl.remove env.named_values err_name;
    (match old_val_opt with
    | Some v -> Hashtbl.add env.named_values err_name v
    | None -> ());

    let err_end_bb = insertion_block !ce_builder in
    let err_has_term =
      match block_terminator err_end_bb with None -> false | Some _ -> true
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
        [ (!catch_val, err_end_bb); (ok_val, ok_end_bb) ]
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
    let catch_val_raw =
      match handler with
      | { node = Let name }
        when Hashtbl.mem env.function_types name
             && not (Hashtbl.mem env.named_values name) ->
          let ft, _, _ = Hashtbl.find env.function_types name in
          let call_name =
            if expected_ll_ty = void_type ce_ctx then "" else "catch_call_tmp"
          in
          build_call ft handler_val [| err_str |] call_name !ce_builder
      | _ -> (
          match infer_ast_type env handler with
          | TFn (param_tys, ret_ty) ->
              let env_ptr =
                build_extractvalue handler_val 1 "env_ptr" !ce_builder
              in
              let fn_ptr_raw =
                build_extractvalue handler_val 0 "fn_ptr_raw" !ce_builder
              in
              let expected_tys =
                Array.of_list
                  (pointer_type ce_ctx
                  :: List.map (Types.llvm_type_of env) param_tys)
              in
              let ft =
                function_type (Types.llvm_type_of env ret_ty) expected_tys
              in
              let call_name =
                if expected_ll_ty = void_type ce_ctx then ""
                else "catch_call_tmp"
              in
              build_call ft fn_ptr_raw [| env_ptr; err_str |] call_name
                !ce_builder
          | _ -> raise (Utils.mk_error loc "Catch handler must be a function"))
    in
    let catch_val =
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else coerce_value env loc expected_ll_ty catch_val_raw false false
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

    List.iteri
      (fun i (_, v, ty, _) ->
        let gep =
          build_struct_gep env_struct_ty env_ptr i "env_gep" !ce_builder
        in
        let loaded_val =
          build_load (Types.llvm_type_of env ty) v "capture_load" !ce_builder
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
        else
          raise
            (Utils.mk_error loc "Anonymous function missing a return statement"));

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
        if String.contains name '.' then
          let parts = String.split_on_char '.' name in
          let base_name = List.hd parts in
          let v, ast_ty, _ =
            try Hashtbl.find env.named_values base_name
            with Not_found ->
              raise
                (Utils.mk_error loc
                   ("Cannot reference unknown variable: '" ^ base_name ^ "'"))
          in
          let is_ptr, base_struct_ast_ty =
            match ast_ty with TPointer t -> (true, t) | t -> (false, t)
          in
          let base_ptr =
            if is_ptr then
              build_load
                (Types.llvm_type_of env ast_ty)
                v "auto_deref_ptr" !ce_builder
            else v
          in
          resolve_property_ptr env base_ptr
            (Types.llvm_type_of env base_struct_ast_ty)
            (List.tl parts)
        else
          try
            let ptr_val, _, _ = Hashtbl.find env.named_values name in
            ptr_val
          with Not_found ->
            raise
              (Utils.mk_error loc
                 ("Cannot reference unknown variable: '" ^ name ^ "'")))
    | _ -> raise (Utils.mk_error loc "Can only reference variables (e.g., &a)")

  and gen_deref env compile_stmt_cb loc deref_e =
    let ptr_val = codegen env compile_stmt_cb deref_e in
    let ptr_ast_ty = infer_ast_type env deref_e in
    let inner_ty =
      match ptr_ast_ty with
      | TPointer t -> t
      | TString -> TChar
      | _ ->
          raise (Utils.mk_error loc "Cannot dereference non-pointer expression")
    in
    build_load (Types.llvm_type_of env inner_ty) ptr_val "dereftmp" !ce_builder

  and gen_binop env compile_stmt_cb op l r =
    let lv, rv =
      (codegen env compile_stmt_cb l, codegen env compile_stmt_cb r)
    in
    Utils.Expr.gen_binary_op op lv rv (infer_ast_type env l)
end
