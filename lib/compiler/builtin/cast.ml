open Llvm
open Ce_parser.Ast
open Codegen

exception Error of string

let register context the_module builder registry =
  let as_fn =
   fun (context : llcontext) (the_module : llmodule) (builder : llbuilder)
       (fn_name : string) (arg_vals : llvalue list) (targ_lltypes : lltype list)
       (arg_asts : types list) (targs : types list)
       (codegen_expr : expr -> llvalue) (llvm_type_of : types -> lltype)
       (infer_ast_type : expr -> types) ->
    if List.length targs <> 1 then
      raise (Error "The .as method expects exactly 1 type argument");

    let base_path = String.sub fn_name 0 (String.length fn_name - 3) in
    let target_ast_ty = List.hd targs in
    let target_ll_ty = llvm_type_of target_ast_ty in
    let result_ast_ty = TResult target_ast_ty in
    let result_ll_ty = llvm_type_of result_ast_ty in
    let self_val = codegen_expr (Utils.mk_expr (Let base_path)) in
    let self_ll_ty = type_of self_val in
    let self_ast_ty = infer_ast_type (Utils.mk_expr (Let base_path)) in

    let is_str_to_int =
      self_ast_ty = TString
      && match target_ast_ty with TInt _ -> true | _ -> false
    in

    let is_str_to_float =
      self_ast_ty = TString
      && match target_ast_ty with TFloat _ -> true | _ -> false
    in

    if is_str_to_int then begin
      let the_func = block_parent (insertion_block builder) in
      let ok_bb = append_block context "cast_ok" the_func in
      let err_bb = append_block context "cast_err" the_func in
      let merge_bb = append_block context "cast_merge" the_func in
      let strtoll_ty =
        function_type (i64_type context)
          [| pointer_type context; pointer_type context; i32_type context |]
      in
      let strtoll_fn =
        match lookup_function "strtoll" the_module with
        | Some f -> f
        | None -> declare_function "strtoll" strtoll_ty the_module
      in

      let endptr_alloc =
        build_alloca (pointer_type context) "endptr_alloc" builder
      in
      let base_val = const_int (i32_type context) 10 in
      let c_val_i64 =
        build_call strtoll_ty strtoll_fn
          [| self_val; endptr_alloc; base_val |]
          "strtoll_call" builder
      in
      let endptr =
        build_load (pointer_type context) endptr_alloc "endptr" builder
      in
      let endchar = build_load (i8_type context) endptr "endchar" builder in

      let is_null =
        build_icmp Icmp.Eq endchar
          (const_int (i8_type context) 0)
          "is_null" builder
      in
      let is_empty = build_icmp Icmp.Eq self_val endptr "is_empty" builder in
      let not_empty = build_not is_empty "not_empty" builder in
      let is_valid = build_and is_null not_empty "is_valid" builder in

      ignore (build_cond_br is_valid ok_bb err_bb builder);

      position_at_end ok_bb builder;
      let casted_val =
        if target_ll_ty = i64_type context then c_val_i64
        else build_intcast c_val_i64 target_ll_ty "cast_trunc" builder
      in
      let res_ok_0 =
        build_insertvalue (const_null result_ll_ty)
          (const_int (i1_type context) 0)
          0 "res_ok0" builder
      in
      let res_ok_1 =
        build_insertvalue res_ok_0 casted_val 1 "res_ok1" builder
      in
      let ok_end_bb = insertion_block builder in
      ignore (build_br merge_bb builder);

      position_at_end err_bb builder;
      let err_msg =
        build_global_stringptr "Invalid integer format" "err_msg" builder
      in
      let res_err_0 =
        build_insertvalue (const_null result_ll_ty)
          (const_int (i1_type context) 1)
          0 "res_err0" builder
      in
      let res_err_1 =
        build_insertvalue res_err_0 err_msg 2 "res_err1" builder
      in
      let err_end_bb = insertion_block builder in
      ignore (build_br merge_bb builder);

      position_at_end merge_bb builder;
      build_phi
        [ (res_ok_1, ok_end_bb); (res_err_1, err_end_bb) ]
        "cast_res" builder
    end
    else if is_str_to_float then begin
      let the_func = block_parent (insertion_block builder) in
      let ok_bb = append_block context "cast_ok" the_func in
      let err_bb = append_block context "cast_err" the_func in
      let merge_bb = append_block context "cast_merge" the_func in

      let strtod_ty =
        function_type (double_type context)
          [| pointer_type context; pointer_type context |]
      in
      let strtod_fn =
        match lookup_function "strtod" the_module with
        | Some f -> f
        | None -> declare_function "strtod" strtod_ty the_module
      in
      let endptr_alloc =
        build_alloca (pointer_type context) "endptr_alloc" builder
      in

      let c_val_f64 =
        build_call strtod_ty strtod_fn
          [| self_val; endptr_alloc |]
          "strtod_call" builder
      in
      let endptr =
        build_load (pointer_type context) endptr_alloc "endptr" builder
      in
      let endchar = build_load (i8_type context) endptr "endchar" builder in

      let is_null =
        build_icmp Icmp.Eq endchar
          (const_int (i8_type context) 0)
          "is_null" builder
      in
      let is_empty = build_icmp Icmp.Eq self_val endptr "is_empty" builder in
      let not_empty = build_not is_empty "not_empty" builder in
      let is_valid = build_and is_null not_empty "is_valid" builder in

      ignore (build_cond_br is_valid ok_bb err_bb builder);

      position_at_end ok_bb builder;
      let casted_val =
        if target_ll_ty = double_type context then c_val_f64
        else build_fptrunc c_val_f64 target_ll_ty "cast_trunc" builder
      in
      let res_ok_0 =
        build_insertvalue (const_null result_ll_ty)
          (const_int (i1_type context) 0)
          0 "res_ok0" builder
      in
      let res_ok_1 =
        build_insertvalue res_ok_0 casted_val 1 "res_ok1" builder
      in
      let ok_end_bb = insertion_block builder in
      ignore (build_br merge_bb builder);

      position_at_end err_bb builder;
      let err_msg =
        build_global_stringptr "Invalid float format" "err_msg" builder
      in
      let res_err_0 =
        build_insertvalue (const_null result_ll_ty)
          (const_int (i1_type context) 1)
          0 "res_err0" builder
      in
      let res_err_1 =
        build_insertvalue res_err_0 err_msg 2 "res_err1" builder
      in
      let err_end_bb = insertion_block builder in
      ignore (build_br merge_bb builder);

      position_at_end merge_bb builder;
      build_phi
        [ (res_ok_1, ok_end_bb); (res_err_1, err_end_bb) ]
        "cast_res" builder
    end
    else begin
      let casted_val =
        if self_ll_ty = target_ll_ty then self_val
        else if
          classify_type self_ll_ty = TypeKind.Integer
          && classify_type target_ll_ty = TypeKind.Integer
        then build_intcast self_val target_ll_ty "cast" builder
        else if
          classify_type self_ll_ty = TypeKind.Double
          && target_ll_ty = float_type context
        then build_fptrunc self_val target_ll_ty "cast" builder
        else if
          classify_type self_ll_ty = TypeKind.Float
          && target_ll_ty = double_type context
        then build_fpext self_val target_ll_ty "cast" builder
        else if
          classify_type self_ll_ty = TypeKind.Integer
          && (classify_type target_ll_ty = TypeKind.Double
             || classify_type target_ll_ty = TypeKind.Float)
        then build_sitofp self_val target_ll_ty "cast" builder
        else if
          (classify_type self_ll_ty = TypeKind.Double
          || classify_type self_ll_ty = TypeKind.Float)
          && classify_type target_ll_ty = TypeKind.Integer
        then build_fptosi self_val target_ll_ty "cast" builder
        else self_val
      in
      let res_ok_0 =
        build_insertvalue (const_null result_ll_ty)
          (const_int (i1_type context) 0)
          0 "res_ok0" builder
      in
      let res_ok_1 =
        build_insertvalue res_ok_0 casted_val 1 "res_ok1" builder
      in
      res_ok_1
    end
  in

  Hashtbl.add registry ".as" (Some as_fn)
