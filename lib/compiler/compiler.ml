open Llvm
open Llvm_target
open Ce_parser.Ast
open State
open Utils
open Substitue
open Infer

exception Error of string

let rec llvm_type_of = function
  | TInt | TUInt | TI32 | TU32 -> i32_type ce_ctx
  | TI8 | TU8 -> i8_type ce_ctx
  | TI16 | TU16 -> i16_type ce_ctx
  | TI64 | TU64 -> i64_type ce_ctx
  | TI128 | TU128 -> integer_type ce_ctx 128
  | TFloat | TF64 -> double_type ce_ctx
  | TF32 -> float_type ce_ctx
  | TBool -> i1_type ce_ctx
  | TVoid -> void_type ce_ctx
  | TString -> pointer_type ce_ctx
  | TChar -> i8_type ce_ctx
  | TPointer _ -> pointer_type ce_ctx
  | TArray (n, ty) -> array_type (llvm_type_of ty) n
  | TNamed name -> (
      match Hashtbl.find_opt type_aliases name with
      | Some actual_ty -> llvm_type_of actual_ty
      | None -> (
          match Hashtbl.find_opt struct_registry name with
          | Some (llty, _) -> llty
          | None -> (
              match Hashtbl.find_opt interface_registry name with
              | Some _ ->
                  struct_type ce_ctx
                    [| pointer_type ce_ctx; pointer_type ce_ctx |]
              | None -> raise (Error ("Undefined type: " ^ name)))))
  | TStruct name -> (
      try
        let llty, _ = Hashtbl.find struct_registry name in
        llty
      with Not_found -> raise (Error ("Unknown struct '" ^ name ^ "'")))
  | TUnknown -> raise (Error "Cannot compile unknown type")
  | TGenericParam name ->
      raise (Error ("Uninstantiated generic parameter '" ^ name))
  | TResult ty ->
      let inner = llvm_type_of ty in
      let ok_ty = if inner = void_type ce_ctx then i1_type ce_ctx else inner in
      struct_type ce_ctx [| i1_type ce_ctx; ok_ty; pointer_type ce_ctx |]
  | TGenericInst (name, arg_types) -> (
      let mangled_name =
        name ^ "_" ^ String.concat "_" (List.map show_types arg_types)
      in
      match Hashtbl.find_opt struct_registry mangled_name with
      | Some (llty, _) -> llty
      | None ->
          let saved_bb =
            try Some (insertion_block ce_builder) with Not_found -> None
          in

          let params, fields =
            try Hashtbl.find struct_templates name
            with Not_found ->
              raise
                (Error ("Cannot find generic struct template for '" ^ name ^ "'"))
          in
          let type_map =
            List.map2
              (fun (p_name, _) arg_ty -> (p_name, arg_ty))
              params arg_types
          in

          let specialized_fields =
            List.map
              (fun f ->
                {
                  field_name = f.field_name;
                  ty = substitute_type type_map f.ty;
                  is_mut = f.is_mut;
                })
              fields
          in

          ignore
            (codegen_stmt (DefStruct (mangled_name, [], specialized_fields)));

          (match Hashtbl.find_opt impl_templates name with
          | Some (_, methods) ->
              let specialized_methods =
                List.map
                  (fun (m_name, self_id, is_ptr, m_params, ret_ty, body) ->
                    let sub_params =
                      List.map
                        (fun p ->
                          {
                            param_name = p.param_name;
                            ty = substitute_type type_map p.ty;
                          })
                        m_params
                    in
                    let sub_body = List.map (substitute_stmt type_map) body in
                    ( m_name,
                      self_id,
                      is_ptr,
                      sub_params,
                      substitute_type type_map ret_ty,
                      sub_body ))
                  methods
              in
              ignore
                (codegen_stmt (Impl (mangled_name, [], specialized_methods)))
          | None -> ());

          (match saved_bb with
          | Some bb -> position_at_end bb ce_builder
          | None -> ());

          fst (Hashtbl.find struct_registry mangled_name))
  | TTuple ts -> struct_type ce_ctx (Array.of_list (List.map llvm_type_of ts))
  | TFn _ -> struct_type ce_ctx [| pointer_type ce_ctx; pointer_type ce_ctx |]

and instantiate_generic_fn name targs =
  let mangled_name =
    name ^ "_" ^ String.concat "_" (List.map show_types targs)
  in

  if Hashtbl.mem function_types mangled_name then mangled_name
  else
    begin match Hashtbl.find_opt fn_templates name with
    | Some (tparams, fn_params, ret_ty, body) ->
        let type_map =
          List.map2 (fun (p_name, _) arg_ty -> (p_name, arg_ty)) tparams targs
        in
        let sub_params =
          List.map
            (fun p ->
              { param_name = p.param_name; ty = substitute_type type_map p.ty })
            fn_params
        in
        let sub_ret_ty = substitute_type type_map ret_ty in
        let sub_body = List.map (substitute_stmt type_map) body in
        let saved_bb =
          try Some (insertion_block ce_builder) with Not_found -> None
        in

        ignore
          (codegen_stmt
             (DefFN (mangled_name, [], sub_params, sub_ret_ty, sub_body)));
        (match saved_bb with
        | Some bb -> position_at_end bb ce_builder
        | None -> ());
        mangled_name
    | None -> raise (Error ("Undefined generic function: " ^ name))
    end

and codegen_expr = function
  | Void -> const_null (void_type ce_ctx)
  | Nil -> const_null (pointer_type ce_ctx)
  | Int n -> const_int (i32_type ce_ctx) n
  | Float f -> const_float (double_type ce_ctx) f
  | Bool b -> const_int (i1_type ce_ctx) (if b then 1 else 0)
  | Char c -> const_int (i8_type ce_ctx) (Char.code c)
  | String s -> build_global_stringptr s "strtmp" ce_builder
  | ArrayAccess (name, index_expr) ->
      Codegen.Expr.gen_array_access llvm_type_of codegen_expr name index_expr
  | Let name -> Codegen.Expr.gen_let llvm_type_of codegen_expr name
  | Call (name, targs, args) ->
      Codegen.Expr.gen_call llvm_type_of codegen_expr coerce_value
        instantiate_generic_fn name targs args
  | If (cond, then_body, elif_branches, else_body) ->
      Codegen.Expr.gen_if codegen_expr codegen_stmt cond then_body elif_branches
        else_body
  | Catch (expr, err_name, catch_ty, body) ->
      Codegen.Expr.gen_catch llvm_type_of codegen_expr codegen_stmt expr
        err_name catch_ty body
  | CatchExpr (expr, handler) ->
      Codegen.Expr.gen_catch_expr llvm_type_of codegen_expr coerce_value expr
        handler
  | AnonFN (params, ret_ty, body) ->
      Codegen.Expr.gen_anon_fn llvm_type_of codegen_block params ret_ty body
  | Ref (Let name) -> (
      if String.contains name '.' then
        let parts = String.split_on_char '.' name in
        let base_name = List.hd parts in
        let v, ast_ty, _ =
          try Hashtbl.find named_values base_name
          with Not_found ->
            raise
              (Error ("Cannot reference unknown variable: '" ^ base_name ^ "'"))
        in
        let is_ptr, base_struct_ast_ty =
          match ast_ty with TPointer t -> (true, t) | t -> (false, t)
        in
        let base_ptr =
          if is_ptr then
            build_load (llvm_type_of ast_ty) v "auto_deref_ptr" ce_builder
          else v
        in
        resolve_property_ptr base_ptr
          (llvm_type_of base_struct_ast_ty)
          (List.tl parts)
      else
        try
          let ptr_val, _, _ = Hashtbl.find named_values name in
          ptr_val
        with Not_found ->
          raise (Error ("Cannot reference unknown variable: '" ^ name ^ "'")))
  | Ref _ -> raise (Error "Can only reference variables (e.g., &a)")
  | Deref e ->
      let ptr_val = codegen_expr e in
      let ptr_ast_ty = infer_ast_type e in
      let inner_ty =
        match ptr_ast_ty with
        | TPointer t -> t
        | TString -> TChar
        | _ -> raise (Error "Cannot dereference non-pointer expression")
      in
      build_load (llvm_type_of inner_ty) ptr_val "dereftmp" ce_builder
  | Add (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      if classify_type (type_of lv) = TypeKind.Pointer then
        build_ptr_arith lv rv build_add "addptr"
      else if classify_type (type_of rv) = TypeKind.Pointer then
        build_ptr_arith rv lv build_add "addptr"
      else build_numeric_op lv rv build_add build_fadd "addtmp"
  | Sub (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      if classify_type (type_of lv) = TypeKind.Pointer then
        build_ptr_arith lv rv build_sub "subptr"
      else build_numeric_op lv rv build_sub build_fsub "subtmp"
  | Mul (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv build_mul build_fmul "multmp"
  | Div (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (if is_unsigned (infer_ast_type l) then build_udiv else build_sdiv)
        build_fdiv "divtmp"
  | Mod (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (if is_unsigned (infer_ast_type l) then build_urem else build_srem)
        build_frem "modtmp"
  | Eq (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv (build_icmp Icmp.Eq) (build_fcmp Fcmp.Oeq) "eqtmp"
  | Lt (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (build_icmp
           (if is_unsigned (infer_ast_type l) then Icmp.Ult else Icmp.Slt))
        (build_fcmp Fcmp.Olt) "lttmp"
  | Lte (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (build_icmp
           (if is_unsigned (infer_ast_type l) then Icmp.Ule else Icmp.Sle))
        (build_fcmp Fcmp.Ole) "ltetmp"
  | Gt (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (build_icmp
           (if is_unsigned (infer_ast_type l) then Icmp.Ugt else Icmp.Sgt))
        (build_fcmp Fcmp.Ogt) "gttmp"
  | Gte (l, r) ->
      let lv, rv = (codegen_expr l, codegen_expr r) in
      build_numeric_op lv rv
        (build_icmp
           (if is_unsigned (infer_ast_type l) then Icmp.Uge else Icmp.Sge))
        (build_fcmp Fcmp.Oge) "gtetmp"
  | And (l, r) ->
      build_and (codegen_expr l) (codegen_expr r) "andtmp" ce_builder
  | Or (l, r) -> build_or (codegen_expr l) (codegen_expr r) "ortmp" ce_builder
  | Neg e ->
      let v = codegen_expr e in
      if type_of v = double_type ce_ctx then build_fneg v "fnegtmp" ce_builder
      else build_neg v "negtmp" ce_builder
  | Not e ->
      let v = codegen_expr e in
      if type_of v = i1_type ce_ctx then build_not v "nottmp" ce_builder
      else
        raise (Error "NOT operator (!) can only be applied to boolean values")
  | Array (n, ty, elems) ->
      let arr_ty = array_type (llvm_type_of ty) n in
      let alloc = build_alloca arr_ty "arrtmp" ce_builder in
      List.iteri
        (fun i e ->
          let ptr =
            build_gep arr_ty alloc
              [| const_int (i32_type ce_ctx) 0; const_int (i32_type ce_ctx) i |]
              "elemtmp" ce_builder
          in
          ignore (build_store (codegen_expr e) ptr ce_builder))
        elems;
      build_load arr_ty alloc "arrload" ce_builder
  | Struct (name, type_args, fields) ->
      if type_args <> [] then begin
        ignore (llvm_type_of (TGenericInst (name, type_args)))
      end;

      let mangled_name =
        if type_args = [] then name
        else name ^ "_" ^ String.concat "_" (List.map show_types type_args)
      in
      let llty, field_map =
        try Hashtbl.find struct_registry mangled_name
        with Not_found ->
          raise (Error ("Cannot find struct '" ^ name ^ "' for instantiation"))
      in
      let alloc = build_alloca llty "structtmp" ce_builder in
      ignore (build_store (const_null llty) alloc ce_builder);

      List.iter
        (fun (fname, fexpr) ->
          let _, fidx, _ = List.find (fun (n, _, _) -> n = fname) field_map in
          let fptr = build_struct_gep llty alloc fidx "fieldptr" ce_builder in
          let expected_ty = (struct_element_types llty).(fidx) in
          let raw_val = codegen_expr fexpr in
          let val_to_store = coerce_value expected_ty raw_val false false in
          ignore (build_store val_to_store fptr ce_builder))
        fields;

      build_load llty alloc "structload" ce_builder
  | Tuple elems ->
      let lltypes = List.map (fun e -> type_of (codegen_expr e)) elems in
      let struct_ty = struct_type ce_ctx (Array.of_list lltypes) in
      let alloc = build_alloca struct_ty "tupletmp" ce_builder in
      List.iteri
        (fun i e ->
          ignore
            (build_store (codegen_expr e)
               (build_struct_gep struct_ty alloc i "tupleelem" ce_builder)
               ce_builder))
        elems;
      build_load struct_ty alloc "tupleload" ce_builder

and coerce_value expected_ll_ty raw_val is_unsigned_target is_unsigned_source =
  let raw_ty = type_of raw_val in

  (if
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
               raise (Error "Cannot assign negative value to unsigned type")
             else false
           else true
       | None -> true
     in
     if needs_runtime_check then begin
       let the_func = block_parent (insertion_block ce_builder) in
       let ok_bb = append_block ce_ctx "uint_ok" the_func in
       let err_bb = append_block ce_ctx "uint_err" the_func in
       let zero = const_int raw_ty 0 in
       let is_neg = build_icmp Icmp.Slt raw_val zero "is_neg" ce_builder in
       ignore (build_cond_br is_neg err_bb ok_bb ce_builder);
       position_at_end err_bb ce_builder;
       let printf_ty =
         var_arg_function_type (i32_type ce_ctx) [| pointer_type ce_ctx |]
       in
       let printf_fn =
         match lookup_function "printf" ce_module with
         | Some f -> f
         | None -> declare_function "printf" printf_ty ce_module
       in
       let err_fmt =
         build_global_stringptr
           "Runtime Error: Cannot assign negative value to unsigned type\n"
           "err_fmt" ce_builder
       in
       ignore (build_call printf_ty printf_fn [| err_fmt |] "p" ce_builder);
       let exit_ty = function_type (void_type ce_ctx) [| i32_type ce_ctx |] in
       let exit_fn =
         match lookup_function "exit" ce_module with
         | Some f -> f
         | None -> declare_function "exit" exit_ty ce_module
       in
       ignore
         (build_call exit_ty exit_fn
            [| const_int (i32_type ce_ctx) 1 |]
            "" ce_builder);
       ignore (build_unreachable ce_builder);

       position_at_end ok_bb ce_builder
     end);

  if raw_ty = expected_ll_ty then raw_val
  else if
    classify_type raw_ty = TypeKind.Integer
    && classify_type expected_ll_ty = TypeKind.Integer
  then build_intcast raw_val expected_ll_ty "int_coerce" ce_builder
  else if raw_ty = double_type ce_ctx && expected_ll_ty = float_type ce_ctx then
    build_fptrunc raw_val expected_ll_ty "float_trunc" ce_builder
  else if raw_ty = float_type ce_ctx && expected_ll_ty = double_type ce_ctx then
    build_fpext raw_val expected_ll_ty "float_ext" ce_builder
  else
    let is_result =
      match classify_type raw_ty with
      | TypeKind.Struct ->
          let elems = struct_element_types raw_ty in
          Array.length elems = 3
          && elems.(0) = i1_type ce_ctx
          && elems.(2) = pointer_type ce_ctx
      | _ -> false
    in
    if is_result then begin
      let is_err = build_extractvalue raw_val 0 "is_err" ce_builder in

      let the_func = block_parent (insertion_block ce_builder) in
      let err_bb = append_block ce_ctx "unwrap_err" the_func in
      let ok_bb = append_block ce_ctx "unwrap_ok" the_func in
      let merge_bb = append_block ce_ctx "unwrap_merge" the_func in

      ignore (build_cond_br is_err err_bb ok_bb ce_builder);

      position_at_end err_bb ce_builder;
      let err_msg = build_extractvalue raw_val 2 "err_msg" ce_builder in
      let printf_ty =
        var_arg_function_type (i32_type ce_ctx) [| pointer_type ce_ctx |]
      in
      let printf_fn =
        match lookup_function "printf" ce_module with
        | Some f -> f
        | None -> declare_function "printf" printf_ty ce_module
      in
      let err_fmt =
        build_global_stringptr "Uncaught Error: %s\n" "err_fmt" ce_builder
      in
      ignore
        (build_call printf_ty printf_fn [| err_fmt; err_msg |] "p" ce_builder);

      let exit_ty = function_type (void_type ce_ctx) [| i32_type ce_ctx |] in
      let exit_fn =
        match lookup_function "exit" ce_module with
        | Some f -> f
        | None -> declare_function "exit" exit_ty ce_module
      in
      ignore
        (build_call exit_ty exit_fn
           [| const_int (i32_type ce_ctx) 1 |]
           "" ce_builder);
      ignore (build_unreachable ce_builder);

      position_at_end ok_bb ce_builder;
      let ok_val = build_extractvalue raw_val 1 "ok_val" ce_builder in
      let final_val =
        coerce_value expected_ll_ty ok_val is_unsigned_target false
      in
      let final_ok_bb = insertion_block ce_builder in
      ignore (build_br merge_bb ce_builder);

      position_at_end merge_bb ce_builder;
      if expected_ll_ty = void_type ce_ctx then const_null (void_type ce_ctx)
      else build_phi [ (final_val, final_ok_bb) ] "unwrap_res" ce_builder
    end
    else
      let is_interface =
        match classify_type expected_ll_ty with
        | TypeKind.Struct ->
            let elems = struct_element_types expected_ll_ty in
            Array.length elems = 2
            && elems.(0) = pointer_type ce_ctx
            && elems.(1) = pointer_type ce_ctx
        | _ -> false
      in

      if is_interface then begin
        let actual_raw_val, actual_raw_ty =
          if classify_type raw_ty = TypeKind.Float then
            ( build_fpext raw_val (double_type ce_ctx) "box_fext" ce_builder,
              double_type ce_ctx )
          else (raw_val, raw_ty)
        in
        let malloc_val =
          build_malloc actual_raw_ty "autobox_malloc" ce_builder
        in
        ignore (build_store actual_raw_val malloc_val ce_builder);
        let ptr_ty = pointer_type ce_ctx in
        let data_ptr =
          build_bitcast malloc_val ptr_ty "autobox_data" ce_builder
        in
        let type_tag =
          match classify_type actual_raw_ty with
          | TypeKind.Integer ->
              let bw = integer_bitwidth actual_raw_ty in
              if bw = 1 then 3 else if bw = 8 then 5 else 1
          | TypeKind.Double -> 2
          | TypeKind.Pointer -> 4
          | _ -> 0
        in
        let tag_val = const_int (i64_type ce_ctx) type_tag in
        let vtable_ptr =
          build_inttoptr tag_val ptr_ty "autobox_tag" ce_builder
        in

        let box_0 =
          build_insertvalue
            (const_null expected_ll_ty)
            data_ptr 0 "autobox_d" ce_builder
        in
        build_insertvalue box_0 vtable_ptr 1 "autobox_v" ce_builder
      end
      else if
        classify_type expected_ll_ty = TypeKind.Pointer
        && classify_type raw_ty = TypeKind.Pointer
      then begin
        build_bitcast raw_val expected_ll_ty "ptr_cast" ce_builder
      end
      else raw_val

and codegen_block stmts =
  List.iter
    (fun s ->
      if Option.is_none (block_terminator (insertion_block ce_builder)) then
        ignore (codegen_stmt s))
    stmts

and codegen_stmt = function
  | Expr e ->
      let v = codegen_expr e in
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
        ignore (coerce_value (struct_element_types ty).(1) v false false);
      const_null (void_type ce_ctx)
  | DefLet (name, ismut, ty, expr_opt) ->
      Codegen.Stmt.gen_def_let llvm_type_of codegen_expr coerce_value name ismut
        ty expr_opt
  | DefFN (name, tparams, params, ret_ty, body) ->
      Codegen.Stmt.gen_def_fn llvm_type_of codegen_block name tparams params
        ret_ty body
  | DefType (name, underlying_ty) ->
      Hashtbl.add type_aliases name underlying_ty;
      const_null (void_type ce_ctx)
  | DefStruct (name, params, fields) ->
      if List.length params > 0 then begin
        Hashtbl.add struct_templates name (params, fields);
        const_null (void_type ce_ctx)
      end
      else begin
        let field_types =
          Array.of_list (List.map (fun f -> llvm_type_of f.ty) fields)
        in
        let struct_llty = named_struct_type ce_ctx name in
        struct_set_body struct_llty field_types false;

        let field_map =
          List.mapi (fun i f -> (f.field_name, i, f.is_mut)) fields
        in
        Hashtbl.add struct_registry name (struct_llty, field_map);
        const_null (void_type ce_ctx)
      end
  | Assign (name, expr) ->
      let val_ = codegen_expr expr in
      let var_ptr, expected_ll_ty, is_u =
        if String.contains name '.' then
          let parts = String.split_on_char '.' name in
          let base_name = List.hd parts in
          let v, ast_ty, _ = Hashtbl.find named_values base_name in

          let is_ptr, base_struct_ast_ty =
            match ast_ty with TPointer t -> (true, t) | t -> (false, t)
          in
          let base_struct_llty = llvm_type_of base_struct_ast_ty in

          let base_ptr =
            if is_ptr then
              build_load (llvm_type_of ast_ty) v "auto_deref_ptr" ce_builder
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
                      Hashtbl.find struct_registry clean_name
                    in
                    let _, idx, is_mut =
                      List.find (fun (n, _, _) -> n = prop) field_map
                    in
                    if rest = [] && not is_mut then
                      raise
                        (Error
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
            try Hashtbl.find named_values name
            with Not_found ->
              raise (Error ("Unknown variable: '" ^ name ^ "'"))
          in
          if not ismut then
            raise (Error ("Cannot assign to immutable variable '" ^ name ^ "'"));

          (v, llvm_type_of ast_ty, is_unsigned ast_ty)
      in
      let src_ty = infer_ast_type expr in
      let is_src_u = is_unsigned src_ty in
      let val_to_store = coerce_value expected_ll_ty val_ is_u is_src_u in
      ignore (build_store val_to_store var_ptr ce_builder);
      val_to_store
  | ArrayAssign (name, index_expr, val_expr) ->
      let array_ptr_val, array_ty =
        match Hashtbl.find_opt named_values name with
        | Some (v, ty, ismut) ->
            if not ismut then
              raise (Error ("Cannot assign to immutable array '" ^ name ^ "'"));
            (v, ty)
        | None ->
            raise (Error ("Array '" ^ name ^ "' not found for assignment"))
      in

      let idx_val = codegen_expr index_expr in
      let val_to_store = codegen_expr val_expr in

      let zero = const_int (i32_type ce_ctx) 0 in
      let indices = [| zero; idx_val |] in
      let element_ptr =
        build_in_bounds_gep (llvm_type_of array_ty) array_ptr_val indices
          "arrayidx" ce_builder
      in

      ignore (build_store val_to_store element_ptr ce_builder);
      val_to_store
  | DerefAssign (ptr_expr, val_expr) ->
      let actual_ptr = codegen_expr ptr_expr in
      let ptr_ast_ty = infer_ast_type ptr_expr in
      let expected_ast_ty =
        match ptr_ast_ty with
        | TPointer t -> t
        | TString -> TChar
        | _ ->
            raise
              (Error
                 "Left-hand side of dereference assignment must be a pointer")
      in

      let raw_val = codegen_expr val_expr in
      let src_ty = infer_ast_type val_expr in
      let is_src_u = is_unsigned src_ty in
      let val_to_store =
        coerce_value
          (llvm_type_of expected_ast_ty)
          raw_val
          (is_unsigned expected_ast_ty)
          is_src_u
      in

      ignore (build_store val_to_store actual_ptr ce_builder);
      val_to_store
  | Block stmts ->
      codegen_block stmts;
      const_null (void_type ce_ctx)
  | For (init, cond, mut, stmts) ->
      let init_var_name =
        match init with Some (DefLet (n, _, _, _)) -> Some n | _ -> None
      in
      (match init with Some s -> ignore (codegen_stmt s) | None -> ());

      let the_function = block_parent (insertion_block ce_builder) in
      let cond_bb = append_block ce_ctx "loop_cond" the_function in
      let loop_bb = append_block ce_ctx "loop" the_function in
      let mut_bb = append_block ce_ctx "loop_mut" the_function in
      let after_bb = append_block ce_ctx "afterloop" the_function in

      ignore (build_br cond_bb ce_builder);

      position_at_end cond_bb ce_builder;
      (match cond with
      | Some c ->
          let cond_val = codegen_expr c in
          ignore (build_cond_br cond_val loop_bb after_bb ce_builder)
      | None -> ignore (build_br loop_bb ce_builder));

      position_at_end loop_bb ce_builder;
      Stack.push after_bb loop_exit_blocks;

      codegen_block stmts;

      if Option.is_none (block_terminator (insertion_block ce_builder)) then
        ignore (build_br mut_bb ce_builder);

      position_at_end mut_bb ce_builder;
      (match mut with Some m -> ignore (codegen_stmt m) | None -> ());

      ignore (build_br cond_bb ce_builder);

      ignore (Stack.pop loop_exit_blocks);
      position_at_end after_bb ce_builder;

      (match init_var_name with
      | Some n -> Hashtbl.remove named_values n
      | None -> ());

      const_null (void_type ce_ctx)
  | Break ->
      if Stack.is_empty loop_exit_blocks then
        raise (Error "Break outside of a loop");
      let exit_block = Stack.top loop_exit_blocks in
      ignore (build_br exit_block ce_builder);
      const_null (void_type ce_ctx)
  | Return e ->
      let v = codegen_expr e in
      if !current_fn_is_res then begin
        let ret_ty = !current_fn_ret_ty in
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
        ignore (build_ret v ce_builder);
        const_null (void_type ce_ctx)
      end
  | Import _ -> const_null (void_type ce_ctx)
  | Impl (name, params, methods) ->
      if List.length params > 0 then begin
        Hashtbl.add impl_templates name (params, methods);
        const_null (void_type ce_ctx)
      end
      else begin
        List.iter
          (fun (method_name, self_id, is_ptr, m_params, ret_ty, body) ->
            let mangled_name = name ^ "::" ^ method_name in
            let base_ty =
              match name with
              | "int" -> TI32
              | "float" -> TF64
              | "uint" -> TU32
              | "string" -> TString
              | "bool" -> TBool
              | "char" -> TChar
              | "i8" -> TI8
              | "i16" -> TI16
              | "i64" -> TI64
              | "i128" -> TI128
              | "u8" -> TU8
              | "u16" -> TU16
              | "u64" -> TU64
              | "u128" -> TU128
              | "f32" -> TF32
              | _ -> TNamed name
            in

            let self_ty = if is_ptr then TPointer base_ty else base_ty in
            let self_param = { param_name = self_id; ty = self_ty } in
            let all_params = self_param :: m_params in
            ignore
              (codegen_stmt
                 (DefFN (mangled_name, [], all_params, ret_ty, body))))
          methods;
        const_null (void_type ce_ctx)
      end
  | Raise e ->
      let err_msg = codegen_expr e in
      let ret_ty = !current_fn_ret_ty in
      let s1 =
        build_insertvalue (const_null ret_ty)
          (const_int (i1_type ce_ctx) 1)
          0 "err_flag" ce_builder
      in
      let s2 = build_insertvalue s1 err_msg 2 "err_msg" ce_builder in
      ignore (build_ret s2 ce_builder);
      const_null (void_type ce_ctx)
  | DefInterface (name, sigs) ->
      Hashtbl.add interface_registry name sigs;
      const_null (void_type ce_ctx)
  | ExternFN (alias_opt, name, params, ret_ty) ->
      let c_name = match alias_opt with Some a -> a | None -> name in
      if c_name <> name then Hashtbl.add extern_aliases name c_name;

      let param_types =
        Array.of_list (List.map (fun (p : param) -> llvm_type_of p.ty) params)
      in
      let ft = function_type (llvm_type_of ret_ty) param_types in
      Hashtbl.add function_types name (ft, ret_ty);

      let _ =
        match Llvm.lookup_function c_name ce_module with
        | Some f -> f
        | None -> declare_function c_name ft ce_module
      in
      const_null (void_type ce_ctx)

let optimize the_module =
  ignore (Llvm_all_backends.initialize ());
  let target_triple = Llvm_target.Target.default_triple () in
  let target_machine =
    Llvm_target.TargetMachine.create ~triple:target_triple
      (Llvm_target.Target.by_triple target_triple)
  in
  let pbo = Llvm_passbuilder.create_passbuilder_options () in
  ignore
    (Llvm_passbuilder.run_passes the_module "default<O3>" target_machine pbo);
  Llvm_passbuilder.dispose_passbuilder_options pbo;
  the_module

let compile (stmts : stmt list) =
  List.iter (fun s -> ignore (codegen_stmt s)) stmts;
  optimize ce_module
