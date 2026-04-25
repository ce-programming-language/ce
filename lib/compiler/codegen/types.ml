open Llvm
open Ce_parser.Ast
open Ce_parser.Ast_mapper
open Ce_error
open State
open Codegen

module Make () : TYPES = struct
  let rec llvm_type_of env = function
    | TInt (bits, _) -> integer_type ce_ctx bits
    | TFloat 32 -> float_type ce_ctx
    | TFloat 64 | TFloat _ -> double_type ce_ctx
    | TVoid -> void_type ce_ctx
    | TString -> pointer_type ce_ctx
    | TPointer _ -> pointer_type ce_ctx
    | TArray (n, ty) -> array_type (llvm_type_of env ty) n
    | TNamed name -> (
        match Hashtbl.find_opt env.type_aliases name with
        | Some actual_ty -> llvm_type_of env actual_ty
        | None -> (
            match Hashtbl.find_opt env.struct_registry name with
            | Some (llty, _, _) -> llty
            | None -> (
                match Hashtbl.find_opt env.interface_registry name with
                | Some _ ->
                    struct_type ce_ctx
                      [| pointer_type ce_ctx; pointer_type ce_ctx |]
                | None -> raise (Error.unknown_type name))))
    | TStruct name -> (
        try
          let llty, _, _ = Hashtbl.find env.struct_registry name in
          llty
        with Not_found -> raise (Error.unknown_type name))
    | TUnknown -> raise (Error.unknown_type "<unknown>")
    | TGenericParam name -> raise (Error.generic_requires_type name)
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
        | Some (llty, _, _) -> llty
        | None ->
            let saved_bb =
              try Some (insertion_block !ce_builder) with Not_found -> None
            in
            let params, fields, def_mod =
              try Hashtbl.find env.struct_templates name
              with Not_found ->
                if name = "slices.Slice" then
                  raise (Error.missing_import "slices")
                else raise (Error.cant_find_struct name)
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
                    is_pub = f.is_pub;
                  })
                fields
            in

            let struct_llty = named_struct_type ce_ctx mangled_name in
            Hashtbl.add env.struct_registry mangled_name
              (struct_llty, [], def_mod);
            let field_types =
              Array.of_list
                (List.map (fun f -> llvm_type_of env f.ty) specialized_fields)
            in
            struct_set_body struct_llty field_types false;
            let field_map =
              List.mapi
                (fun i f -> (f.field_name, i, f.is_mut, f.ty, f.is_pub))
                specialized_fields
            in
            Hashtbl.replace env.struct_registry mangled_name
              (struct_llty, field_map, def_mod);

            (match Hashtbl.find_opt env.impl_templates name with
            | Some (_, methods, def_impl_mod) ->
                let specialized_methods =
                  List.map
                    (fun ( m_name,
                           m_tparams,
                           is_pub,
                           self_id_opt,
                           is_ptr,
                           m_params,
                           ret_ty,
                           body ) ->
                      let sub_params =
                        List.map
                          (fun (p : param) ->
                            {
                              param_name = p.param_name;
                              ty = substitute_type type_map p.ty;
                            })
                          m_params
                      in
                      let sub_tparams =
                        List.map
                          (fun (n, ty) -> (n, substitute_type type_map ty))
                          m_tparams
                      in
                      let sub_ret_ty = substitute_type type_map ret_ty in
                      let sub_body = List.map (substitute_stmt type_map) body in

                      let mangled_method = mangled_name ^ "::" ^ m_name in

                      let all_sub_params =
                        match self_id_opt with
                        | Some self_id ->
                            let self_ty =
                              if is_ptr then TPointer (TNamed mangled_name)
                              else TNamed mangled_name
                            in
                            { param_name = self_id; ty = self_ty } :: sub_params
                        | None -> sub_params
                      in

                      let param_types =
                        Array.of_list
                          (List.map
                             (fun (p : param) -> llvm_type_of env p.ty)
                             all_sub_params)
                      in
                      let ft =
                        function_type (llvm_type_of env sub_ret_ty) param_types
                      in
                      Hashtbl.replace env.function_types mangled_method
                        ( ft,
                          List.map (fun (p : param) -> p.ty) all_sub_params,
                          sub_ret_ty );
                      Hashtbl.replace env.method_registry mangled_method
                        (is_pub, def_impl_mod);
                      let _ =
                        match
                          Llvm.lookup_function mangled_method !ce_module
                        with
                        | Some existing -> existing
                        | None ->
                            let new_f =
                              declare_function mangled_method ft !ce_module
                            in
                            if not is_pub then
                              set_linkage Linkage.Internal new_f;
                            new_f
                      in

                      ( m_name,
                        sub_tparams,
                        is_pub,
                        self_id_opt,
                        is_ptr,
                        sub_params,
                        sub_ret_ty,
                        sub_body ))
                    methods
                in
                let impl_stmt =
                  Utils.mk_stmt (Impl (mangled_name, [], specialized_methods))
                in
                Queue.push
                  { impl_stmt with mod_name = def_impl_mod }
                  env.pending_instantiations
            | None -> ());

            (match !(env.process_pending_cb) with
            | Some cb -> cb ()
            | None -> ());

            (match saved_bb with
            | Some bb -> position_at_end bb !ce_builder
            | None -> ());
            let llty, _, _ =
              try Hashtbl.find env.struct_registry mangled_name
              with Not_found -> raise (Error.unknown_type mangled_name)
            in
            llty)
    | TTuple ts ->
        struct_type ce_ctx (Array.of_list (List.map (llvm_type_of env) ts))
    | TFn _ -> struct_type ce_ctx [| pointer_type ce_ctx; pointer_type ce_ctx |]
    | TVariadic ty -> llvm_type_of env (TGenericInst ("slices.Slice", [ ty ]))

  and instantiate_generic_fn env name targs =
    let mangled_name =
      name ^ "_" ^ String.concat "_" (List.map show_types targs)
    in

    if Hashtbl.mem env.function_types mangled_name then mangled_name
    else
      begin match Hashtbl.find_opt env.fn_templates name with
      | Some (tparams, fn_params, ret_ty, body, is_pub, def_mod) ->
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
          let param_types =
            Array.of_list
              (List.map (fun (p : param) -> llvm_type_of env p.ty) sub_params)
          in
          let ft = function_type (llvm_type_of env sub_ret_ty) param_types in
          Hashtbl.replace env.function_types mangled_name
            (ft, List.map (fun (p : param) -> p.ty) sub_params, sub_ret_ty);
          let _ =
            match Llvm.lookup_function mangled_name !ce_module with
            | Some existing -> existing
            | None ->
                let new_f = declare_function mangled_name ft !ce_module in
                if not is_pub then set_linkage Linkage.Internal new_f;
                new_f
          in
          let fn_stmt =
            Utils.mk_stmt
              (DefFN (mangled_name, [], sub_params, sub_ret_ty, sub_body))
          in
          Queue.push
            { fn_stmt with mod_name = def_mod; is_pub }
            env.pending_instantiations;
          mangled_name
      | None -> raise (Error.unknown_var_fn name)
      end
end
