open Llvm
open Ce_parser.Ast
open State
open Substitue
open Compiler_intf

module Make (Stmt : STMT) : TYPES = struct
  exception Error of string

  let rec llvm_type_of env = function
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
    | TArray (n, ty) -> array_type (llvm_type_of env ty) n
    | TNamed name -> (
        match Hashtbl.find_opt env.type_aliases name with
        | Some actual_ty -> llvm_type_of env actual_ty
        | None -> (
            match Hashtbl.find_opt env.struct_registry name with
            | Some (llty, _) -> llty
            | None -> (
                match Hashtbl.find_opt env.interface_registry name with
                | Some _ ->
                    struct_type ce_ctx
                      [| pointer_type ce_ctx; pointer_type ce_ctx |]
                | None -> raise (Error ("Undefined type: " ^ name)))))
    | TStruct name -> (
        try
          let llty, _ = Hashtbl.find env.struct_registry name in
          llty
        with Not_found -> raise (Error ("Unknown struct '" ^ name ^ "'")))
    | TUnknown -> raise (Error "Cannot compile unknown type")
    | TGenericParam name ->
        raise (Error ("Uninstantiated generic parameter '" ^ name))
    | TResult ty ->
        let inner = llvm_type_of env ty in
        let ok_ty =
          if inner = void_type ce_ctx then i1_type ce_ctx else inner
        in
        struct_type ce_ctx [| i1_type ce_ctx; ok_ty; pointer_type ce_ctx |]
    | TGenericInst (name, arg_types) -> (
        let mangled_name =
          name ^ "_" ^ String.concat "_" (List.map show_types arg_types)
        in
        match Hashtbl.find_opt env.struct_registry mangled_name with
        | Some (llty, _) -> llty
        | None ->
            let saved_bb =
              try Some (insertion_block ce_builder) with Not_found -> None
            in

            let params, fields =
              try Hashtbl.find env.struct_templates name
              with Not_found ->
                raise
                  (Error
                     ("Cannot find generic struct template for '" ^ name ^ "'"))
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
              (Stmt.codegen_stmt env
                 (DefStruct (mangled_name, [], specialized_fields)));

            (match Hashtbl.find_opt env.impl_templates name with
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
                  (Stmt.codegen_stmt env
                     (Impl (mangled_name, [], specialized_methods)))
            | None -> ());

            (match saved_bb with
            | Some bb -> position_at_end bb ce_builder
            | None -> ());

            fst (Hashtbl.find env.struct_registry mangled_name))
    | TTuple ts ->
        struct_type ce_ctx (Array.of_list (List.map (llvm_type_of env) ts))
    | TFn _ -> struct_type ce_ctx [| pointer_type ce_ctx; pointer_type ce_ctx |]

  and instantiate_generic_fn env name targs =
    let mangled_name =
      name ^ "_" ^ String.concat "_" (List.map show_types targs)
    in

    if Hashtbl.mem env.function_types mangled_name then mangled_name
    else
      begin match Hashtbl.find_opt env.fn_templates name with
      | Some (tparams, fn_params, ret_ty, body) ->
          let type_map =
            List.map2 (fun (p_name, _) arg_ty -> (p_name, arg_ty)) tparams targs
          in
          let sub_params =
            List.map
              (fun p ->
                {
                  param_name = p.param_name;
                  ty = substitute_type type_map p.ty;
                })
              fn_params
          in
          let sub_ret_ty = substitute_type type_map ret_ty in
          let sub_body = List.map (substitute_stmt type_map) body in
          let saved_bb =
            try Some (insertion_block ce_builder) with Not_found -> None
          in

          ignore
            (Stmt.codegen_stmt env
               (DefFN (mangled_name, [], sub_params, sub_ret_ty, sub_body)));
          (match saved_bb with
          | Some bb -> position_at_end bb ce_builder
          | None -> ());
          mangled_name
      | None -> raise (Error ("Undefined generic function: " ^ name))
      end
end
