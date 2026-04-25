open Llvm
open Ce_parser.Ast
open Ce_error
open Codegen

let register context the_module builder registry =
  let typeof =
   fun (context : llcontext) (the_module : llmodule) (builder : llbuilder)
       (fn_name : string) (arg_vals : llvalue list) (targ_lltypes : lltype list)
       (arg_asts : types list) (targs : types list)
       (codegen_expr : expr -> llvalue) (llvm_type_of : types -> lltype)
       (infer_ast_type : expr -> types) ->
    if List.length arg_vals <> 1 then
      raise (Error.expects_exactly_args "typeof" "1");
    let arg_val = List.hd arg_vals in
    let ty = type_of arg_val in

    let str_int = build_global_stringptr "int" "s_int" builder in
    let str_float = build_global_stringptr "float" "s_float" builder in
    let str_bool = build_global_stringptr "bool" "s_bool" builder in
    let str_str = build_global_stringptr "string" "s_str" builder in
    let str_char = build_global_stringptr "char" "s_char" builder in
    let str_unk = build_global_stringptr "unknown" "s_unk" builder in

    let rec type_to_string = function
      | TInt (32, Signed) -> "int"
      | TInt (32, Unsigned) -> "uint"
      | TInt (1, Unsigned) -> "bool"
      | TInt (8, Unsigned) -> "u8"
      | TInt (size, sign) ->
          let prefix = match sign with Signed -> "i" | Unsigned -> "u" in
          prefix ^ string_of_int size
      | TFloat 32 -> "f32"
      | TFloat 64 -> "float"
      | TString -> "string"
      | TTuple ts -> "(" ^ String.concat ", " (List.map type_to_string ts) ^ ")"
      | TNamed n | TStruct n -> n
      | TArray (n, t) -> "[" ^ string_of_int n ^ "]" ^ type_to_string t
      | TResult t -> "!" ^ type_to_string t
      | TFn (args, ret) ->
          "fn("
          ^ String.concat ", " (List.map type_to_string args)
          ^ ") " ^ type_to_string ret
      | _ -> "unknown"
    in
    let ast_ty = List.hd arg_asts in

    match classify_type ty with
    | TypeKind.Integer ->
        let bw = integer_bitwidth ty in
        if bw = 1 then str_bool
        else if bw = 8 then str_char
        else if bw = 16 then build_global_stringptr "i16" "s_i16" builder
        else if bw = 32 then build_global_stringptr "i32" "s_i32" builder
        else if bw = 128 then build_global_stringptr "i128" "s_i128" builder
        else str_int
    | TypeKind.Double -> str_float
    | TypeKind.Float -> build_global_stringptr "f32" "s_f32" builder
    | TypeKind.Pointer -> (
        match ast_ty with
        | TFn _ -> build_global_stringptr (type_to_string ast_ty) "s_fn" builder
        | _ -> str_str)
    | TypeKind.Struct -> (
        match ast_ty with
        | TFn _ -> build_global_stringptr (type_to_string ast_ty) "s_fn" builder
        | _ ->
            let elems = struct_element_types ty in
            if
              Array.length elems = 2
              && elems.(0) = pointer_type context
              && elems.(1) = pointer_type context
            then begin
              let tag_ptr = build_extractvalue arg_val 1 "tag_ptr" builder in
              let tag_val =
                build_ptrtoint tag_ptr (i64_type context) "tag_val" builder
              in

              let is_1 =
                build_icmp Icmp.Eq tag_val
                  (const_int (i64_type context) 1)
                  "is_1" builder
              in
              let is_2 =
                build_icmp Icmp.Eq tag_val
                  (const_int (i64_type context) 2)
                  "is_2" builder
              in
              let is_3 =
                build_icmp Icmp.Eq tag_val
                  (const_int (i64_type context) 3)
                  "is_3" builder
              in
              let is_4 =
                build_icmp Icmp.Eq tag_val
                  (const_int (i64_type context) 4)
                  "is_4" builder
              in
              let is_5 =
                build_icmp Icmp.Eq tag_val
                  (const_int (i64_type context) 5)
                  "is_5" builder
              in

              let res_5 = build_select is_5 str_char str_unk "res5" builder in
              let res_4 = build_select is_4 str_str res_5 "res4" builder in
              let res_3 = build_select is_3 str_bool res_4 "res3" builder in
              let res_2 = build_select is_2 str_float res_3 "res2" builder in
              build_select is_1 str_int res_2 "res_final" builder
            end
            else
              begin match struct_name ty with
              | Some s_name ->
                  let clean_name =
                    if String.starts_with ~prefix:"struct." s_name then
                      String.sub s_name 7 (String.length s_name - 7)
                    else s_name
                  in
                  build_global_stringptr clean_name "s_struct" builder
              | None -> (
                  match ast_ty with
                  | TTuple _ ->
                      build_global_stringptr (type_to_string ast_ty) "s_tuple"
                        builder
                  | _ -> str_unk)
              end)
    | _ -> str_unk
  in

  let sizeof =
   fun (context : llcontext) (the_module : llmodule) (builder : llbuilder)
       (fn_name : string) (arg_vals : llvalue list) (targ_lltypes : lltype list)
       (arg_asts : types list) (targs : types list)
       (codegen_expr : expr -> llvalue) (llvm_type_of : types -> lltype)
       (infer_ast_type : expr -> types) ->
    let target_ll_ty =
      if List.length arg_asts = 1 then llvm_type_of (List.hd arg_asts)
      else raise (Error.expects_exactly_args "typeof" "1")
    in
    let size_val = size_of target_ll_ty in
    build_intcast size_val (i32_type context) "sizeof_cast" builder
  in

  let malloc =
   fun (context : llcontext) (the_module : llmodule) (builder : llbuilder)
       (fn_name : string) (arg_vals : llvalue list) (targ_lltypes : lltype list)
       (arg_asts : types list) (targs : types list)
       (codegen_expr : expr -> llvalue) (llvm_type_of : types -> lltype)
       (infer_ast_type : expr -> types) ->
    if List.length targ_lltypes <> 1 then
      raise (Error.expects_exactly_args fn_name "1");
    if List.length arg_vals <> 1 then
      raise (Error.expects_exactly_args fn_name "1");

    let elem_ty = List.hd targ_lltypes in
    let count_val = List.hd arg_vals in
    let count_i64 =
      build_intcast count_val (i64_type context) "count_i64" builder
    in
    let size_val = size_of elem_ty in
    let total_size = build_mul count_i64 size_val "alloc_size" builder in

    let ptr_ty = pointer_type context in
    let gc_malloc_ty = function_type ptr_ty [| i64_type context |] in
    let gc_malloc_fn =
      match lookup_function "GC_malloc" the_module with
      | Some f -> f
      | None -> declare_function "GC_malloc" gc_malloc_ty the_module
    in
    build_call gc_malloc_ty gc_malloc_fn [| total_size |] "gc_alloc_tmp" builder
  in

  let realloc =
   fun (context : llcontext) (the_module : llmodule) (builder : llbuilder)
       (fn_name : string) (arg_vals : llvalue list) (targ_lltypes : lltype list)
       (arg_asts : types list) (targs : types list)
       (codegen_expr : expr -> llvalue) (llvm_type_of : types -> lltype)
       (infer_ast_type : expr -> types) ->
    if List.length targ_lltypes <> 1 then
      raise (Error.expects_exactly_args fn_name "1");
    if List.length arg_vals <> 2 then
      raise (Error.expects_exactly_args fn_name "2");

    let elem_ty = List.hd targ_lltypes in
    let ptr_val = List.hd arg_vals in
    let ptr_ty = pointer_type context in

    let count_val = List.nth arg_vals 1 in
    let count_i64 =
      build_intcast count_val (i64_type context) "count_i64" builder
    in
    let size_val = size_of elem_ty in
    let total_size = build_mul count_i64 size_val "realloc_size" builder in

    let gc_realloc_ty = function_type ptr_ty [| ptr_ty; i64_type context |] in
    let gc_realloc_fn =
      match lookup_function "GC_realloc" the_module with
      | Some f -> f
      | None -> declare_function "GC_realloc" gc_realloc_ty the_module
    in

    build_call gc_realloc_ty gc_realloc_fn [| ptr_val; total_size |]
      "gc_realloc_tmp" builder
  in

  Hashtbl.add registry "typeof" (Some typeof);
  Hashtbl.add registry "sizeof" (Some sizeof);
  Hashtbl.add registry "malloc" (Some malloc);
  Hashtbl.add registry "realloc" (Some realloc)
