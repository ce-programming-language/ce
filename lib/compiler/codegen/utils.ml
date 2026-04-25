open Llvm
open Ce_parser.Ast
open State
open Ce_error

let rec build_numeric_op lv rv build_int build_float name =
  if type_of lv = double_type ce_ctx then build_float lv rv name !ce_builder
  else build_int lv rv name !ce_builder

and resolve_property_ptr env llvm_type_of current_ptr current_llty
    current_ast_ty props =
  let rec get_gep ptr ty ast_ty props =
    match props with
    | [] -> ptr
    | prop :: rest -> (
        let is_ptr = match ast_ty with TPointer _ -> true | _ -> false in
        let base_ast_ty = match ast_ty with TPointer t -> t | t -> t in
        let actual_ty = llvm_type_of env base_ast_ty in
        let actual_ptr =
          if is_ptr then
            build_load (pointer_type ce_ctx) ptr "deref_ptr" !ce_builder
          else ptr
        in
        match classify_type actual_ty with
        | TypeKind.Struct ->
            let clean_name =
              try ast_base_type_name base_ast_ty
              with _ -> (
                match struct_name actual_ty with
                | Some sn -> clean_struct_name sn
                | None -> "<unknown>")
            in
            let _, field_map, def_mod =
              try Hashtbl.find env.struct_registry clean_name
              with Not_found -> (
                let fallback_name =
                  match struct_name actual_ty with
                  | Some sn -> clean_struct_name sn
                  | None -> clean_name
                in
                try Hashtbl.find env.struct_registry fallback_name
                with Not_found ->
                  raise
                    (Error.Error
                       ("Struct not found in registry: " ^ clean_name ^ " / "
                      ^ fallback_name)))
            in
            let field_opt =
              List.find_opt (fun (n, _, _, _, _) -> n = prop) field_map
            in
            if Option.is_none field_opt then
              raise
                (Error.Error
                   ("Unknown property '" ^ prop ^ "' on struct '" ^ clean_name
                  ^ "'"));
            let _, idx, _, next_ast_ty, is_pub = Option.get field_opt in
            if (not is_pub) && !(env.current_module) <> def_mod then
              raise
                (Error.Error
                   ("Cannot access private property '" ^ prop ^ "' on struct '"
                  ^ clean_name ^ "'"));
            let next_ptr =
              build_struct_gep actual_ty actual_ptr idx "prop_ptr" !ce_builder
            in
            let next_ty = (struct_element_types actual_ty).(idx) in
            get_gep next_ptr next_ty next_ast_ty rest
        | _ ->
            raise
              (Error.Error
                 ("Cannot access property '" ^ prop ^ "' on non-struct")))
  in
  get_gep current_ptr current_llty current_ast_ty props

and resolve_cross_module v builder_module ty _name =
  let kind = classify_value v in
  if kind = ValueKind.GlobalVariable || kind = ValueKind.Function then
    let val_module = global_parent v in
    if val_module != builder_module then
      let v_name = value_name v in
      let actual_name = if v_name = "" then _name else v_name in
      if kind = ValueKind.GlobalVariable then
        match Llvm.lookup_global actual_name builder_module with
        | Some g -> g
        | None -> declare_global ty actual_name builder_module
      else
        match Llvm.lookup_function actual_name builder_module with
        | Some f -> f
        | None -> declare_function actual_name ty builder_module
    else v
  else v

and is_unsigned = function TInt (_, Unsigned) -> true | _ -> false

and clean_struct_name s_name =
  if String.starts_with ~prefix:"struct." s_name then
    String.sub s_name 7 (String.length s_name - 7)
  else s_name

and ast_base_type_name = function
  | TNamed n | TStruct n -> n
  | TGenericInst (n, arg_types) ->
      n ^ "_" ^ String.concat "_" (List.map show_types arg_types)
  | TInt (1, _) -> "bool"
  | TInt (8, Unsigned) -> "char"
  | TInt (size, sign) ->
      let prefix = match sign with Signed -> "i" | Unsigned -> "u" in
      prefix ^ string_of_int size
  | TFloat 32 -> "f32"
  | TFloat 64 -> "float"
  | TString -> "string"
  | TVoid -> "void"
  | TPointer t -> ast_base_type_name t
  | TArray (_, t) -> ast_base_type_name t
  | TResult t -> ast_base_type_name t
  | TUnknown -> "unknown"
  | _ -> "unknown"

and build_ptr_arith lv rv op name =
  let ptr_int = build_ptrtoint lv (i64_type ce_ctx) "pti" !ce_builder in
  let rv_i64 = build_intcast rv (i64_type ce_ctx) "rv_i64" !ce_builder in
  build_inttoptr
    (op ptr_int rv_i64 name !ce_builder)
    (type_of lv) "itp" !ce_builder

and lookup_function env name m =
  let real_name =
    try Hashtbl.find env.extern_aliases name with Not_found -> name
  in
  match Llvm.lookup_function real_name m with
  | Some f -> Some f
  | None -> (
      match Hashtbl.find_opt env.function_types real_name with
      | Some (ft, _, _) -> Some (Llvm.declare_function real_name ft m)
      | None -> None)

let next_builtin_id = ref (-1)

let get_builtin_id () =
  let id = !next_builtin_id in
  decr next_builtin_id;
  id

let mk_expr (n : expr_node) : expr =
  let loc =
    { line = 0; col = 0; end_line = 0; end_col = 0; file = "<builtin>" }
  in
  {
    id = get_builtin_id ();
    loc;
    node = n;
    inferred_type = ref None;
    resolved_def_id = ref None;
  }

let mk_stmt (n : stmt_node) : stmt =
  let loc =
    { line = 0; col = 0; end_line = 0; end_col = 0; file = "<builtin>" }
  in
  {
    id = get_builtin_id ();
    loc;
    node = n;
    docstring = None;
    is_pub = false;
    mod_name = "main";
  }

let gen_panic env ctx module_ builder format_str arg_vals =
  let printf_ty = var_arg_function_type (i32_type ctx) [| pointer_type ctx |] in
  let printf_fn =
    match lookup_function env "printf" module_ with
    | Some f -> f
    | None -> declare_function "printf" printf_ty module_
  in
  let err_fmt = build_global_stringptr format_str "panic_fmt" builder in
  let all_args = Array.of_list (err_fmt :: arg_vals) in
  ignore (build_call printf_ty printf_fn all_args "panic_printf" builder);

  let exit_ty = function_type (void_type ctx) [| i32_type ctx |] in
  let exit_fn =
    match lookup_function env "exit" module_ with
    | Some f -> f
    | None -> declare_function "exit" exit_ty module_
  in
  ignore
    (build_call exit_ty exit_fn [| const_int (i32_type ctx) 1 |] "" builder);
  ignore (build_unreachable builder)

let create_block ctx builder name =
  let the_func = block_parent (insertion_block builder) in
  append_block ctx name the_func

let create_blocks ctx builder names = List.map (create_block ctx builder) names

let gen_ok_result ctx builder res_ll_ty ok_val =
  let s1 =
    build_insertvalue (const_null res_ll_ty)
      (const_int (i1_type ctx) 0)
      0 "ok_flag" builder
  in
  if type_of ok_val = void_type ctx then s1
  else build_insertvalue s1 ok_val 1 "ok_val" builder

let gen_err_result ctx builder res_ll_ty err_msg =
  let s1 =
    build_insertvalue (const_null res_ll_ty)
      (const_int (i1_type ctx) 1)
      0 "err_flag" builder
  in
  build_insertvalue s1 err_msg 2 "err_msg" builder

module Expr = struct
  let rec build_eq_cmp l_val r_val builder =
    let ty = type_of l_val in
    match classify_type ty with
    | TypeKind.Struct ->
        let elems = struct_element_types ty in
        let num_elems = Array.length elems in
        if num_elems = 0 then const_int (i1_type ce_ctx) 1
        else
          let rec check_fields i acc =
            if i >= num_elems then acc
            else
              let l_elem = build_extractvalue l_val i "l_elem" builder in
              let r_elem = build_extractvalue r_val i "r_elem" builder in
              let elem_eq = build_eq_cmp l_elem r_elem builder in
              let new_acc =
                if i = 0 then elem_eq
                else build_and acc elem_eq "struct_eq_and" builder
              in
              check_fields (i + 1) new_acc
          in
          check_fields 0 (const_int (i1_type ce_ctx) 1)
    | TypeKind.Array ->
        let len = array_length ty in
        if len = 0 then const_int (i1_type ce_ctx) 1
        else
          let rec check_elems i acc =
            if i >= len then acc
            else
              let l_elem = build_extractvalue l_val i "l_elem" builder in
              let r_elem = build_extractvalue r_val i "r_elem" builder in
              let elem_eq = build_eq_cmp l_elem r_elem builder in
              let new_acc =
                if i = 0 then elem_eq
                else build_and acc elem_eq "arr_eq_and" builder
              in
              check_elems (i + 1) new_acc
          in
          check_elems 0 (const_int (i1_type ce_ctx) 1)
    | TypeKind.Double | TypeKind.Float ->
        build_fcmp Fcmp.Oeq l_val r_val "eqtmp" builder
    | _ -> build_icmp Icmp.Eq l_val r_val "eqtmp" builder

  let gen_binary_op op_type l_val r_val l_ty =
    let is_unsigned_ty = is_unsigned l_ty in
    match op_type with
    | `Add ->
        if classify_type (type_of l_val) = TypeKind.Pointer then
          build_ptr_arith l_val r_val build_add "addptr"
        else if classify_type (type_of r_val) = TypeKind.Pointer then
          build_ptr_arith r_val l_val build_add "addptr"
        else build_numeric_op l_val r_val build_add build_fadd "addtmp"
    | `Sub ->
        if classify_type (type_of l_val) = TypeKind.Pointer then
          build_ptr_arith l_val r_val build_sub "subptr"
        else build_numeric_op l_val r_val build_sub build_fsub "subtmp"
    | `Mul -> build_numeric_op l_val r_val build_mul build_fmul "multmp"
    | `Div ->
        build_numeric_op l_val r_val
          (if is_unsigned_ty then build_udiv else build_sdiv)
          build_fdiv "divtmp"
    | `Mod ->
        build_numeric_op l_val r_val
          (if is_unsigned_ty then build_urem else build_srem)
          build_frem "modtmp"
    | `Eq -> build_eq_cmp l_val r_val !ce_builder
    | `Lt ->
        build_numeric_op l_val r_val
          (build_icmp (if is_unsigned_ty then Icmp.Ult else Icmp.Slt))
          (build_fcmp Fcmp.Olt) "lttmp"
    | `Lte ->
        build_numeric_op l_val r_val
          (build_icmp (if is_unsigned_ty then Icmp.Ule else Icmp.Sle))
          (build_fcmp Fcmp.Ole) "ltetmp"
    | `Gt ->
        build_numeric_op l_val r_val
          (build_icmp (if is_unsigned_ty then Icmp.Ugt else Icmp.Sgt))
          (build_fcmp Fcmp.Ogt) "gttmp"
    | `Gte ->
        build_numeric_op l_val r_val
          (build_icmp (if is_unsigned_ty then Icmp.Uge else Icmp.Sge))
          (build_fcmp Fcmp.Oge) "gtetmp"
    | `And -> build_and l_val r_val "andtmp" !ce_builder
    | `Or -> build_or l_val r_val "ortmp" !ce_builder
end

module Stmt = struct
  let gen_return env ce_builder ce_ctx v =
    if !(env.current_fn_is_res) then begin
      let ret_ty = !(env.current_fn_ret_ty) in
      let s1 =
        build_insertvalue (const_null ret_ty)
          (const_int (i1_type ce_ctx) 0)
          0 "ok_flag" ce_builder
      in
      let s2 =
        if type_of v = void_type ce_ctx then s1
        else build_insertvalue s1 v 1 "ok_val" ce_builder
      in
      ignore (build_ret s2 ce_builder);
      const_null (void_type ce_ctx)
    end
    else begin
      if type_of v = void_type ce_ctx then ignore (build_ret_void ce_builder)
      else ignore (build_ret v ce_builder);

      const_null (void_type ce_ctx)
    end

  let gen_assignment ce_builder expected_ll_ty var_ptr val_to_store =
    ignore (build_store val_to_store var_ptr ce_builder);
    val_to_store
end
