open Llvm
open Ce_parser.Ast
open State

let build_numeric_op lv rv build_int build_float name =
  if type_of lv = double_type ce_ctx then build_float lv rv name ce_builder
  else build_int lv rv name ce_builder

and resolve_property_ptr env current_ptr current_ty props =
  let rec get_gep ptr ty props =
    match props with
    | [] -> ptr
    | prop :: rest -> (
        let actual_ptr, actual_ty =
          if classify_type ty = TypeKind.Pointer then
            (build_load ty ptr "deref_ptr" ce_builder, element_type ty)
          else (ptr, ty)
        in
        match classify_type actual_ty with
        | TypeKind.Struct ->
            let s_name = Option.get (struct_name actual_ty) in
            let clean_name =
              if String.starts_with ~prefix:"struct." s_name then
                String.sub s_name 7 (String.length s_name - 7)
              else s_name
            in
            let _, field_map = Hashtbl.find env.struct_registry clean_name in
            let _, idx, _, _ =
              List.find (fun (n, _, _, _) -> n = prop) field_map
            in
            let next_ptr =
              build_struct_gep actual_ty actual_ptr idx "prop_ptr" ce_builder
            in
            let next_ty = (struct_element_types actual_ty).(idx) in
            get_gep next_ptr next_ty rest
        | _ ->
            raise
              (Error ("Cannot access property '" ^ prop ^ "' on non-struct")))
  in
  get_gep current_ptr current_ty props

and is_unsigned = function TInt (_, Unsigned) -> true | _ -> false

and clean_struct_name s_name =
  if String.starts_with ~prefix:"struct." s_name then
    String.sub s_name 7 (String.length s_name - 7)
  else s_name

and ast_base_type_name = function
  | TNamed n | TStruct n -> n
  | TGenericInst (n, arg_types) ->
      n ^ "_" ^ String.concat "_" (List.map show_types arg_types)
  | TString -> "string"
  | TBool -> "bool"
  | TChar -> "char"
  | TInt (size, sign) ->
      let prefix = match sign with Signed -> "i" | Unsigned -> "u" in
      let bits =
        match size with
        | I8 -> "8"
        | I16 -> "16"
        | I32 -> "32"
        | I64 -> "64"
        | I128 -> "128"
      in
      prefix ^ bits
  | TFloat F32 -> "f32"
  | TFloat F64 -> "f64"
  | _ -> raise Not_found

and build_ptr_arith lv rv op name =
  let ptr_int = build_ptrtoint lv (i64_type ce_ctx) "pti" ce_builder in
  let rv_i64 = build_intcast rv (i64_type ce_ctx) "rv_i64" ce_builder in
  build_inttoptr
    (op ptr_int rv_i64 name ce_builder)
    (type_of lv) "itp" ce_builder

and lookup_function env name m =
  let real_name =
    try Hashtbl.find env.extern_aliases name with Not_found -> name
  in
  Llvm.lookup_function real_name m

let mk_expr (n : expr_node) : expr =
  { loc = { line = 0; col = 0; file = "<builtin>" }; node = n }

let mk_stmt (n : stmt_node) : stmt =
  { loc = { line = 0; col = 0; file = "<builtin>" }; node = n }
