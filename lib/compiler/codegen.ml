open Ce_parser.Ast
open State
open Llvm
open Utils
open Infer

let lookup_function name m =
  let real_name =
    try Hashtbl.find extern_aliases name with Not_found -> name
  in
  Llvm.lookup_function real_name m

module Expr = struct
  let gen_array_access llvm_type_of codegen_expr name index_expr =
    let array_ptr_val, array_ty =
      match Hashtbl.find_opt named_values name with
      | Some (v, ty, _) -> (v, ty)
      | None -> raise (Error ("Array '" ^ name ^ "' not found"))
    in
    let llvm_array_ty = llvm_type_of array_ty in

    let idx_val = codegen_expr index_expr in
    let zero = const_int (i32_type ce_ctx) 0 in
    let indices = [| zero; idx_val |] in
    let element_ptr =
      build_in_bounds_gep llvm_array_ty array_ptr_val indices "arrayidx"
        ce_builder
    in
    let elem_ty = element_type llvm_array_ty in
    build_load elem_ty element_ptr "loadtmp" ce_builder

  and gen_let llvm_type_of codegen_expr name =
    if String.contains name '.' then
      let parts = String.split_on_char '.' name in
      let base_name = List.hd parts in
      let props = List.tl parts in

      match Hashtbl.find_opt named_values base_name with
      | Some (v, ast_ty, _) ->
          let is_ptr, base_struct_ast_ty =
            match ast_ty with TPointer t -> (true, t) | t -> (false, t)
          in
          let base_val_loaded =
            build_load (llvm_type_of ast_ty) v base_name ce_builder
          in

          let base_struct_val, base_struct_llty =
            if is_ptr then
              let ll_struct_ty = llvm_type_of base_struct_ast_ty in
              ( build_load ll_struct_ty base_val_loaded "auto_deref" ce_builder,
                ll_struct_ty )
            else (base_val_loaded, llvm_type_of base_struct_ast_ty)
          in

          let rec extract current_val current_ty props =
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
                        match Hashtbl.find_opt struct_registry clean_name with
                        | Some (_, field_map) -> (
                            try
                              let _, idx, _ =
                                List.find (fun (n, _, _) -> n = prop) field_map
                              in
                              let next_val =
                                build_extractvalue current_val idx "proptmp"
                                  ce_builder
                              in
                              let next_ty =
                                (struct_element_types current_ty).(idx)
                              in
                              extract next_val next_ty rest
                            with Not_found ->
                              raise
                                (Error
                                   ("Unknown property '" ^ prop
                                  ^ "' on struct '" ^ clean_name ^ "'")))
                        | None ->
                            raise
                              (Error
                                 ("Could not find struct definition for '"
                                ^ clean_name ^ "'")))
                    | None -> (
                        try
                          let idx = int_of_string prop in
                          let elems = struct_element_types current_ty in
                          if idx < 0 || idx >= Array.length elems then
                            raise (Error ("Tuple index out of bounds: " ^ prop));
                          let next_val =
                            build_extractvalue current_val idx "tupleelem"
                              ce_builder
                          in
                          let next_ty = elems.(idx) in
                          extract next_val next_ty rest
                        with Failure _ ->
                          raise
                            (Error
                               ("Cannot access non-integer property '" ^ prop
                              ^ "' on a tuple"))))
                | _ ->
                    raise
                      (Error
                         ("Cannot access property '" ^ prop
                        ^ "' on non-struct type")))
          in
          extract base_struct_val base_struct_llty props
      | None -> (
          match lookup_function name ce_module with
          | Some f -> f
          | None -> raise (Error ("Unknown variable or function: " ^ name)))
    else
      match Hashtbl.find_opt named_values name with
      | Some (v, ast_ty, _) ->
          build_load (llvm_type_of ast_ty) v name ce_builder
      | None -> (
          match lookup_function name ce_module with
          | Some f -> f
          | None -> raise (Error ("Unknown variable or function: " ^ name)))

  and gen_call llvm_type_of codegen_expr coerce_value instantiate_generic_fn
      name targs args =
    if String.ends_with ~suffix:".as" name && List.length targs = 1 then begin
      let base_path = String.sub name 0 (String.length name - 3) in
      let target_ast_ty = List.hd targs in
      let target_ll_ty = llvm_type_of target_ast_ty in
      let result_ast_ty = TResult target_ast_ty in
      let result_ll_ty = llvm_type_of result_ast_ty in

      let self_val = codegen_expr (Let base_path) in
      let self_ll_ty = type_of self_val in

      let the_func = block_parent (insertion_block ce_builder) in
      let ok_bb = append_block ce_ctx "cast_ok" the_func in
      let err_bb = append_block ce_ctx "cast_err" the_func in
      let merge_bb = append_block ce_ctx "cast_merge" the_func in
      let is_interface =
        match classify_type self_ll_ty with
        | TypeKind.Struct ->
            let elems = struct_element_types self_ll_ty in
            Array.length elems = 2
            && elems.(0) = pointer_type ce_ctx
            && elems.(1) = pointer_type ce_ctx
        | _ -> false
      in

      if is_interface then begin
        let tag_ptr = build_extractvalue self_val 1 "tag_ptr" ce_builder in
        let tag_val =
          build_ptrtoint tag_ptr (i64_type ce_ctx) "tag_val" ce_builder
        in

        let expected_tag =
          match target_ast_ty with
          | TBool -> 3
          | TChar | TI8 | TU8 -> 5
          | TInt | TI16 | TI32 | TI64 | TI128 | TUInt | TU16 | TU32 | TU64
          | TU128 ->
              1
          | TFloat | TF32 | TF64 -> 2
          | TString | TPointer _ -> 4
          | _ -> 0
        in

        let is_match =
          build_icmp Icmp.Eq tag_val
            (const_int (i64_type ce_ctx) expected_tag)
            "is_match" ce_builder
        in
        ignore (build_cond_br is_match ok_bb err_bb ce_builder);

        position_at_end ok_bb ce_builder;
        let data_ptr = build_extractvalue self_val 0 "data_ptr" ce_builder in
        let loaded_val =
          build_load target_ll_ty data_ptr "loaded_val" ce_builder
        in

        let res_ok_0 =
          build_insertvalue (const_null result_ll_ty)
            (const_int (i1_type ce_ctx) 0)
            0 "res_ok0" ce_builder
        in
        let res_ok_1 =
          build_insertvalue res_ok_0 loaded_val 1 "res_ok1" ce_builder
        in
        let ok_end_bb = insertion_block ce_builder in
        ignore (build_br merge_bb ce_builder);

        position_at_end err_bb ce_builder;
        let err_msg =
          build_global_stringptr "Type cast failed" "err_msg" ce_builder
        in
        let res_err_0 =
          build_insertvalue (const_null result_ll_ty)
            (const_int (i1_type ce_ctx) 1)
            0 "res_err0" ce_builder
        in
        let res_err_1 =
          build_insertvalue res_err_0 err_msg 2 "res_err1" ce_builder
        in
        let err_end_bb = insertion_block ce_builder in
        ignore (build_br merge_bb ce_builder);

        position_at_end merge_bb ce_builder;
        build_phi
          [ (res_ok_1, ok_end_bb); (res_err_1, err_end_bb) ]
          "cast_res" ce_builder
      end
      else begin
        let casted_val =
          if self_ll_ty = target_ll_ty then self_val
          else if
            classify_type self_ll_ty = TypeKind.Integer
            && classify_type target_ll_ty = TypeKind.Integer
          then build_intcast self_val target_ll_ty "cast" ce_builder
          else if
            classify_type self_ll_ty = TypeKind.Double
            && target_ll_ty = float_type ce_ctx
          then build_fptrunc self_val target_ll_ty "cast" ce_builder
          else if
            classify_type self_ll_ty = TypeKind.Float
            && target_ll_ty = double_type ce_ctx
          then build_fpext self_val target_ll_ty "cast" ce_builder
          else if
            classify_type self_ll_ty = TypeKind.Integer
            && (classify_type target_ll_ty = TypeKind.Double
               || classify_type target_ll_ty = TypeKind.Float)
          then build_sitofp self_val target_ll_ty "cast" ce_builder
          else if
            (classify_type self_ll_ty = TypeKind.Double
            || classify_type self_ll_ty = TypeKind.Float)
            && classify_type target_ll_ty = TypeKind.Integer
          then build_fptosi self_val target_ll_ty "cast" ce_builder
          else self_val
        in
        let res_ok_0 =
          build_insertvalue (const_null result_ll_ty)
            (const_int (i1_type ce_ctx) 0)
            0 "res_ok0" ce_builder
        in
        let res_ok_1 =
          build_insertvalue res_ok_0 casted_val 1 "res_ok1" ce_builder
        in
        res_ok_1
      end
    end
    else
      match Builtin.get name with
      | Some builtin_fn ->
          let arg_vals = List.map codegen_expr args in
          let targ_lltypes = List.map llvm_type_of targs in
          let arg_asts = List.map infer_ast_type args in
          builtin_fn ce_ctx ce_module ce_builder name arg_vals targ_lltypes
            arg_asts
      | None -> (
          let target_name =
            if targs = [] then name else instantiate_generic_fn name targs
          in
          match lookup_function name ce_module with
          | Some callee ->
              let ft, _ = Hashtbl.find function_types name in
              let expected_tys = param_types ft in
              let arg_vals =
                List.mapi
                  (fun i arg ->
                    (coerce_value expected_tys.(i) (codegen_expr arg))
                      false false)
                  args
              in
              let args_val = Array.of_list arg_vals in
              let call_name =
                if return_type ft = void_type ce_ctx then "" else "calltmp"
              in
              build_call ft callee args_val call_name ce_builder
          | None -> (
              match lookup_function target_name ce_module with
              | Some callee ->
                  let ft, _ = Hashtbl.find function_types target_name in
                  let expected_tys = param_types ft in
                  let arg_vals =
                    List.mapi
                      (fun i arg ->
                        (coerce_value expected_tys.(i) (codegen_expr arg))
                          false false)
                      args
                  in
                  let args_val = Array.of_list arg_vals in
                  let call_name =
                    if return_type ft = void_type ce_ctx then "" else "calltmp"
                  in
                  build_call ft callee args_val call_name ce_builder
              | None ->
                  let is_fn_var =
                    try
                      match infer_ast_type (Let name) with
                      | TFn _ -> true
                      | _ -> false
                    with _ -> false
                  in

                  if is_fn_var then
                    let fn_val = codegen_expr (Let name) in
                    let fn_ast_ty = infer_ast_type (Let name) in
                    match fn_ast_ty with
                    | TFn (param_tys, ret_ty) ->
                        let expected_tys =
                          Array.of_list (List.map llvm_type_of param_tys)
                        in
                        let ft =
                          function_type (llvm_type_of ret_ty) expected_tys
                        in
                        let fn_ptr_raw =
                          build_extractvalue fn_val 0 "fn_ptr_raw" ce_builder
                        in
                        let env_ptr =
                          build_extractvalue fn_val 1 "env_ptr" ce_builder
                        in
                        let arg_vals =
                          List.mapi
                            (fun i arg ->
                              (coerce_value expected_tys.(i) (codegen_expr arg))
                                false false)
                            args
                        in
                        let all_args = Array.of_list (env_ptr :: arg_vals) in
                        let call_name =
                          if ret_ty = TVoid then "" else "fnptr_calltmp"
                        in
                        build_call ft fn_ptr_raw all_args call_name ce_builder
                    | _ -> raise (Error "Unreachable")
                  else if Hashtbl.mem fn_templates name then
                    raise
                      (Error
                         ("Function '" ^ name
                        ^ "' is generic and requires type arguments (e.g., "
                        ^ name ^ "[int]())"))
                  else if String.contains name '.' then
                    let last_dot_idx = String.rindex name '.' in
                    let base_path = String.sub name 0 last_dot_idx in
                    let method_name =
                      String.sub name (last_dot_idx + 1)
                        (String.length name - last_dot_idx - 1)
                    in

                    if Hashtbl.mem struct_registry base_path then
                      let mangled_name = base_path ^ "::" ^ method_name in
                      let callee =
                        match lookup_function mangled_name ce_module with
                        | Some c -> c
                        | None ->
                            raise
                              (Error
                                 ("Unknown method '" ^ method_name
                                ^ "' on struct '" ^ base_path ^ "'"))
                      in
                      let ft, _ = Hashtbl.find function_types mangled_name in
                      let expected_tys = param_types ft in
                      let arg_vals =
                        List.mapi
                          (fun i arg ->
                            (coerce_value expected_tys.(i) (codegen_expr arg))
                              false false)
                          args
                      in
                      let args_val = Array.of_list arg_vals in
                      let call_name =
                        if return_type ft = void_type ce_ctx then ""
                        else "staticcalltmp"
                      in
                      build_call ft callee args_val call_name ce_builder
                    else
                      let self_val =
                        try codegen_expr (Let base_path)
                        with Error _ ->
                          raise
                            (Error ("Unknown function or method: '" ^ name ^ "'"))
                      in
                      let self_ty_llvm = type_of self_val in

                      let actual_struct_ty, is_self_ptr =
                        if classify_type self_ty_llvm = TypeKind.Pointer then
                          (element_type self_ty_llvm, true)
                        else (self_ty_llvm, false)
                      in

                      let self_ast_ty = infer_ast_type (Let base_path) in
                      let actual_ast_ty =
                        match self_ast_ty with TPointer t -> t | t -> t
                      in

                      let clean_name =
                        try ast_base_type_name actual_ast_ty
                        with Not_found -> (
                          match struct_name actual_struct_ty with
                          | Some s_name ->
                              if String.starts_with ~prefix:"struct." s_name
                              then String.sub s_name 7 (String.length s_name - 7)
                              else s_name
                          | None ->
                              raise
                                (Error
                                   ("Cannot call method '" ^ method_name
                                  ^ "' on a non-struct type")))
                      in

                      let mangled_name = clean_name ^ "::" ^ method_name in
                      let callee =
                        match lookup_function mangled_name ce_module with
                        | Some c -> c
                        | None ->
                            raise
                              (Error
                                 ("Unknown method '" ^ method_name
                                ^ "' on type '" ^ clean_name ^ "'"))
                      in
                      let ft, _ = Hashtbl.find function_types mangled_name in
                      let expected_tys = param_types ft in

                      let expected_self_ty = expected_tys.(0) in
                      let coerced_self =
                        if classify_type expected_self_ty = TypeKind.Pointer
                        then
                          if is_self_ptr then self_val
                          else
                            let get_ptr_to_name path =
                              if String.contains path '.' then
                                let parts = String.split_on_char '.' path in
                                let base_name = List.hd parts in
                                let v, ast_ty, _ =
                                  Hashtbl.find named_values base_name
                                in
                                let is_ptr, base_struct_ast_ty =
                                  match ast_ty with
                                  | TPointer t -> (true, t)
                                  | t -> (false, t)
                                in
                                let base_ptr =
                                  if is_ptr then
                                    build_load (llvm_type_of ast_ty) v
                                      "auto_deref_ptr" ce_builder
                                  else v
                                in
                                resolve_property_ptr base_ptr
                                  (llvm_type_of base_struct_ast_ty)
                                  (List.tl parts)
                              else
                                let v, _, _ = Hashtbl.find named_values path in
                                v
                            in
                            get_ptr_to_name base_path
                        else if is_self_ptr then
                          build_load actual_struct_ty self_val "deref_self"
                            ce_builder
                        else coerce_value expected_self_ty self_val false false
                      in
                      let arg_vals =
                        List.mapi
                          (fun i arg ->
                            (coerce_value
                               expected_tys.(i + 1)
                               (codegen_expr arg))
                              false false)
                          args
                      in
                      let all_args = Array.of_list (coerced_self :: arg_vals) in
                      let call_name =
                        if return_type ft = void_type ce_ctx then ""
                        else "methodcalltmp"
                      in
                      build_call ft callee all_args call_name ce_builder
                  else raise (Error ("Unknown function: " ^ name))))

  and gen_if codegen_expr codegen_stmt cond then_body elif_branches else_body =
    let the_function = block_parent (insertion_block ce_builder) in
    let merge_bb = append_block ce_ctx "ifcont" the_function in
    let cb_yield stmts =
      let rec aux = function
        | [] -> const_null (void_type ce_ctx)
        | [ Expr e ] -> codegen_expr e
        | s :: rest ->
            ignore (codegen_stmt s);
            aux rest
      in
      aux stmts
    in

    let phi_incoming = ref [] in
    let rec build_if c body rest_elifs else_b =
      let cond_val = codegen_expr c in
      let then_bb = append_block ce_ctx "then" the_function in
      let next_bb = append_block ce_ctx "else_or_elif" the_function in

      ignore (build_cond_br cond_val then_bb next_bb ce_builder);
      position_at_end then_bb ce_builder;

      let then_val = cb_yield body in
      let then_bb_end = insertion_block ce_builder in
      (match block_terminator then_bb_end with
      | None ->
          ignore (build_br merge_bb ce_builder);
          phi_incoming := (then_val, then_bb_end) :: !phi_incoming
      | Some _ -> ());
      position_at_end next_bb ce_builder;
      match rest_elifs with
      | (elif_c, elif_body) :: rest -> build_if elif_c elif_body rest else_b
      | [] -> (
          let else_val =
            match else_b with
            | Some stmts -> cb_yield stmts
            | None -> const_null (void_type ce_ctx)
          in
          let else_bb_end = insertion_block ce_builder in

          match block_terminator else_bb_end with
          | None ->
              ignore (build_br merge_bb ce_builder);
              phi_incoming := (else_val, else_bb_end) :: !phi_incoming
          | Some _ -> ())
    in
    build_if cond then_body elif_branches else_body;
    position_at_end merge_bb ce_builder;

    let incoming = List.rev !phi_incoming in
    if incoming = [] then const_null (void_type ce_ctx)
    else
      let first_val, _ = List.hd incoming in
      let ty = type_of first_val in
      if ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_phi incoming "iftmp" ce_builder

  and gen_catch llvm_type_of codegen_expr codegen_stmt expr err_name catch_ty
      body =
    let res_val = codegen_expr expr in
    let is_err = build_extractvalue res_val 0 "is_err" ce_builder in

    let the_func = block_parent (insertion_block ce_builder) in
    let err_bb = append_block ce_ctx "catch_err" the_func in
    let ok_bb = append_block ce_ctx "catch_ok" the_func in
    let merge_bb = append_block ce_ctx "catch_merge" the_func in

    ignore (build_cond_br is_err err_bb ok_bb ce_builder);

    position_at_end err_bb ce_builder;
    let err_str = build_extractvalue res_val 2 "err_str" ce_builder in
    let err_alloc = build_alloca (pointer_type ce_ctx) err_name ce_builder in
    ignore (build_store err_str err_alloc ce_builder);

    let old_val_opt = Hashtbl.find_opt named_values err_name in
    Hashtbl.add named_values err_name (err_alloc, TString, false);

    let catch_ty_ll = llvm_type_of catch_ty in
    let catch_val = ref (const_null catch_ty_ll) in

    List.iter
      (function
        | Return e -> catch_val := codegen_expr e | s -> ignore (codegen_stmt s))
      body;

    Hashtbl.remove named_values err_name;
    (match old_val_opt with
    | Some v -> Hashtbl.add named_values err_name v
    | None -> ());

    let err_end_bb = insertion_block ce_builder in
    let err_has_term =
      match block_terminator err_end_bb with None -> false | Some _ -> true
    in
    if not err_has_term then ignore (build_br merge_bb ce_builder);

    position_at_end ok_bb ce_builder;
    let ok_val =
      if catch_ty_ll = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_extractvalue res_val 1 "ok_val" ce_builder
    in
    let ok_end_bb = insertion_block ce_builder in
    ignore (build_br merge_bb ce_builder);

    position_at_end merge_bb ce_builder;
    if catch_ty_ll = void_type ce_ctx then const_null (void_type ce_ctx)
    else if not err_has_term then
      build_phi
        [ (!catch_val, err_end_bb); (ok_val, ok_end_bb) ]
        "catch_res" ce_builder
    else ok_val

  and gen_catch_expr llvm_type_of codegen_expr coerce_value expr handler =
    let res_val = codegen_expr expr in
    let is_err = build_extractvalue res_val 0 "is_err" ce_builder in

    let expected_ast_ty =
      match infer_ast_type expr with TResult t -> t | t -> t
    in
    let expected_ll_ty = llvm_type_of expected_ast_ty in

    let the_func = block_parent (insertion_block ce_builder) in
    let err_bb = append_block ce_ctx "catch_expr_err" the_func in
    let ok_bb = append_block ce_ctx "catch_expr_ok" the_func in
    let merge_bb = append_block ce_ctx "catch_expr_merge" the_func in

    ignore (build_cond_br is_err err_bb ok_bb ce_builder);
    position_at_end err_bb ce_builder;

    let err_str = build_extractvalue res_val 2 "err_str" ce_builder in
    let handler_val = codegen_expr handler in

    let catch_val_raw =
      match handler with
      | Let name
        when Hashtbl.mem function_types name
             && not (Hashtbl.mem named_values name) ->
          let ft, _ = Hashtbl.find function_types name in
          let call_name =
            if expected_ll_ty = void_type ce_ctx then "" else "catch_call_tmp"
          in
          build_call ft handler_val [| err_str |] call_name ce_builder
      | _ -> (
          let handler_ast_ty = infer_ast_type handler in
          match handler_ast_ty with
          | TFn (param_tys, ret_ty) ->
              let env_ptr =
                build_extractvalue handler_val 1 "env_ptr" ce_builder
              in
              let fn_ptr_raw =
                build_extractvalue handler_val 0 "fn_ptr_raw" ce_builder
              in
              let expected_tys =
                Array.of_list
                  (pointer_type ce_ctx :: List.map llvm_type_of param_tys)
              in
              let ft = function_type (llvm_type_of ret_ty) expected_tys in
              let call_name =
                if expected_ll_ty = void_type ce_ctx then ""
                else "catch_call_tmp"
              in
              build_call ft fn_ptr_raw [| env_ptr; err_str |] call_name
                ce_builder
          | _ -> raise (Error "Catch handler must be a function"))
    in

    let catch_val =
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else coerce_value expected_ll_ty catch_val_raw false false
    in

    let err_end_bb = insertion_block ce_builder in
    ignore (build_br merge_bb ce_builder);

    position_at_end ok_bb ce_builder;
    let ok_val =
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_extractvalue res_val 1 "ok_val" ce_builder
    in
    let ok_end_bb = insertion_block ce_builder in
    ignore (build_br merge_bb ce_builder);

    position_at_end merge_bb ce_builder;
    if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
    else
      build_phi
        [ (catch_val, err_end_bb); (ok_val, ok_end_bb) ]
        "catch_expr_res" ce_builder

  and gen_anon_fn llvm_type_of codegen_block params ret_ty body =
    let anon_id = Oo.id object end in
    let actual_name = Printf.sprintf "__anon_fn_%d" anon_id in

    let was_res = !current_fn_is_res in
    let was_ret_ty = !current_fn_ret_ty in
    let old_bb = insertion_block ce_builder in

    (current_fn_is_res := match ret_ty with TResult _ -> true | _ -> false);
    current_fn_ret_ty := llvm_type_of ret_ty;

    let live_vars =
      Hashtbl.fold
        (fun k (v, ty, is_mut) acc -> (k, v, ty, is_mut) :: acc)
        named_values []
    in
    let env_types =
      Array.of_list (List.map (fun (_, _, ty, _) -> llvm_type_of ty) live_vars)
    in
    let env_struct_ty = struct_type ce_ctx env_types in

    let env_size = size_of env_struct_ty in
    let gc_malloc_ty =
      function_type (pointer_type ce_ctx) [| i64_type ce_ctx |]
    in
    let gc_malloc_fn =
      match lookup_function "GC_malloc" ce_module with
      | Some f -> f
      | None -> declare_function "GC_malloc" gc_malloc_ty ce_module
    in
    let env_ptr_raw =
      build_call gc_malloc_ty gc_malloc_fn [| env_size |] "env_alloc" ce_builder
    in
    let env_ptr =
      build_bitcast env_ptr_raw (pointer_type ce_ctx) "env_ptr" ce_builder
    in

    List.iteri
      (fun i (_, v, ty, _) ->
        let val_ty = llvm_type_of ty in
        let gep =
          build_struct_gep env_struct_ty env_ptr i "env_gep" ce_builder
        in
        let loaded_val = build_load val_ty v "capture_load" ce_builder in
        ignore (build_store loaded_val gep ce_builder))
      live_vars;

    let param_types =
      Array.of_list
        (pointer_type ce_ctx
        :: List.map (fun (p : param) -> llvm_type_of p.ty) params)
    in
    let ft = function_type (llvm_type_of ret_ty) param_types in
    Hashtbl.add function_types actual_name (ft, ret_ty);
    let f = declare_function actual_name ft ce_module in
    set_linkage Linkage.Internal f;
    let bb = append_block ce_ctx "entry" f in
    position_at_end bb ce_builder;

    let old_named_values = Hashtbl.copy named_values in
    Hashtbl.clear named_values;

    let inner_env_ptr_raw = param f 0 in
    let inner_env_ptr =
      build_bitcast inner_env_ptr_raw (pointer_type ce_ctx) "inner_env"
        ce_builder
    in

    List.iteri
      (fun i (k, _, ty, is_mut) ->
        let val_ty = llvm_type_of ty in
        let gep =
          build_struct_gep env_struct_ty inner_env_ptr i "env_gep" ce_builder
        in
        let loaded_val = build_load val_ty gep "env_load" ce_builder in
        let local_alloca = build_alloca val_ty k ce_builder in
        ignore (build_store loaded_val local_alloca ce_builder);
        Hashtbl.add named_values k (local_alloca, ty, is_mut))
      live_vars;

    Array.iteri
      (fun i a ->
        if i > 0 then begin
          let real_i = i - 1 in
          let n = (List.nth params real_i).param_name in
          let p_ty = (List.nth params real_i).ty in
          let llvm_p_ty = llvm_type_of p_ty in
          let alloca = build_alloca llvm_p_ty n ce_builder in
          ignore (build_store a alloca ce_builder);
          Hashtbl.add named_values n (alloca, p_ty, false)
        end)
      (Llvm.params f);

    codegen_block body;

    let current_bb = insertion_block ce_builder in
    (match block_terminator current_bb with
    | Some _ -> ()
    | None ->
        if ret_ty = TVoid then ignore (build_ret_void ce_builder)
        else if !current_fn_is_res then begin
          let r_ty = !current_fn_ret_ty in
          let s1 =
            build_insertvalue (const_null r_ty)
              (const_int (i1_type ce_ctx) 0)
              0 "res_ok" ce_builder
          in
          ignore (build_ret s1 ce_builder)
        end
        else raise (Error "Anonymous function missing a return statement"));

    Hashtbl.clear named_values;
    Hashtbl.iter (fun k v -> Hashtbl.add named_values k v) old_named_values;

    current_fn_is_res := was_res;
    current_fn_ret_ty := was_ret_ty;
    position_at_end old_bb ce_builder;

    let closure_struct_ty =
      struct_type ce_ctx [| pointer_type ce_ctx; pointer_type ce_ctx |]
    in
    let closure_val0 =
      build_insertvalue
        (const_null closure_struct_ty)
        (build_bitcast f (pointer_type ce_ctx) "fn_cast" ce_builder)
        0 "closure0" ce_builder
    in
    build_insertvalue closure_val0 env_ptr 1 "closure" ce_builder
end

module Stmt = struct
  let gen_def_let llvm_type_of codegen_expr coerce_value name ismut ty expr_opt
      =
    let raw_val_opt, inferred_ty =
      match expr_opt with
      | Some expr ->
          let raw_val = codegen_expr expr in
          let deduced_ty =
            if ty = TUnknown then
              let inferred = infer_ast_type expr in
              if inferred = TUnknown then
                raise
                  (Error
                     ("Cannot infer type for variable '" ^ name
                    ^ "'. Please specify the type explicitly."))
              else match inferred with TResult t -> t | _ -> inferred
            else ty
          in
          (Some raw_val, deduced_ty)
      | None ->
          if ty = TUnknown then
            raise
              (Error
                 ("Cannot infer type for '" ^ name ^ "' without initialization"));
          (None, ty)
    in

    let ll_ty = llvm_type_of inferred_ty in
    let init_val =
      match raw_val_opt with
      | Some raw_val ->
          let src_ty = infer_ast_type (Option.get expr_opt) in
          let is_src_u = is_unsigned src_ty in
          coerce_value ll_ty raw_val false is_src_u
      | None -> const_null ll_ty
    in
    let the_function = block_parent (insertion_block ce_builder) in
    let ce_builder_alloca =
      builder_at ce_ctx (instr_begin (entry_block the_function))
    in

    let alloca = build_alloca ll_ty name ce_builder_alloca in

    ignore (build_store init_val alloca ce_builder);
    Hashtbl.add named_values name (alloca, inferred_ty, ismut);
    alloca

  and gen_def_fn llvm_type_of codegen_block name tparams params ret_ty body =
    if List.length tparams > 0 then begin
      Hashtbl.add fn_templates name (tparams, params, ret_ty, body);
      const_null (void_type ce_ctx)
    end
    else begin
      let actual_name = if name = "main" then "__ce_main" else name in

      let was_res = !current_fn_is_res in
      let was_ret_ty = !current_fn_ret_ty in

      (current_fn_is_res := match ret_ty with TResult _ -> true | _ -> false);
      current_fn_ret_ty := llvm_type_of ret_ty;

      let param_types =
        Array.of_list (List.map (fun (p : param) -> llvm_type_of p.ty) params)
      in
      let ft = function_type (llvm_type_of ret_ty) param_types in
      Hashtbl.add function_types actual_name (ft, ret_ty);

      let f = declare_function actual_name ft ce_module in
      set_linkage Linkage.Internal f;

      let bb = append_block ce_ctx "entry" f in
      position_at_end bb ce_builder;

      let old_named_values = Hashtbl.copy named_values in
      Array.iteri
        (fun i a ->
          let n = (List.nth params i).param_name in
          let p_ty = (List.nth params i).ty in
          let llvm_p_ty = llvm_type_of p_ty in
          let alloca = build_alloca llvm_p_ty n ce_builder in
          ignore (build_store a alloca ce_builder);
          Hashtbl.add named_values n (alloca, p_ty, false))
        (Llvm.params f);

      codegen_block body;

      let current_bb = insertion_block ce_builder in
      (match block_terminator current_bb with
      | Some _ -> ()
      | None ->
          if ret_ty = TVoid then ignore (build_ret_void ce_builder)
          else if !current_fn_is_res then begin
            let r_ty = !current_fn_ret_ty in
            let s1 =
              build_insertvalue (const_null r_ty)
                (const_int (i1_type ce_ctx) 0)
                0 "res_ok" ce_builder
            in
            ignore (build_ret s1 ce_builder)
          end
          else
            raise
              (Error ("Function '" ^ name ^ "' is missing a return statement")));

      Hashtbl.clear named_values;
      Hashtbl.iter (fun k v -> Hashtbl.add named_values k v) old_named_values;

      current_fn_is_res := was_res;
      current_fn_ret_ty := was_ret_ty;

      if name = "main" then begin
        let c_main_ty = function_type (i32_type ce_ctx) [||] in
        let c_main_f = declare_function "main" c_main_ty ce_module in
        let c_bb = append_block ce_ctx "entry" c_main_f in
        let c_builder = builder_at_end ce_ctx c_bb in

        let call_name = if ret_ty = TVoid then "" else "main_call" in
        let call_res = build_call ft f [||] call_name c_builder in

        if match ret_ty with TResult _ -> true | _ -> false then begin
          let is_err = build_extractvalue call_res 0 "is_err" c_builder in
          let err_bb = append_block ce_ctx "err" c_main_f in
          let ok_bb = append_block ce_ctx "ok" c_main_f in

          ignore (build_cond_br is_err err_bb ok_bb c_builder);

          position_at_end err_bb c_builder;
          let err_msg = build_extractvalue call_res 2 "err_msg" c_builder in
          let printf_f = Builtin.get_printf ce_ctx ce_module in
          let fmt_str =
            build_global_stringptr "Uncaught Error: %s\n" "err_fmt" c_builder
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
end
