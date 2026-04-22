open Llvm
open Ce_parser.Ast
open Compiler_intf

let register context the_module builder registry =
  let get_printf context the_module =
    match lookup_function "printf" the_module with
    | Some f -> f
    | None ->
        let printf_ty =
          var_arg_function_type (i32_type context) [| pointer_type context |]
        in
        declare_function "printf" printf_ty the_module
  in
  let get_print_any context the_module builder =
    match lookup_function "__print_any" the_module with
    | Some f -> f
    | None ->
        let ptr_ty = pointer_type context in
        let any_ty = struct_type context [| ptr_ty; ptr_ty |] in
        let ft = function_type (void_type context) [| any_ty |] in
        let f = declare_function "__print_any" ft the_module in

        let saved_bb = insertion_block builder in
        let bb = append_block context "entry" f in
        position_at_end bb builder;

        let any_val = param f 0 in
        let data_ptr = build_extractvalue any_val 0 "data" builder in
        let tag_ptr = build_extractvalue any_val 1 "tag_ptr" builder in
        let tag_val = build_ptrtoint tag_ptr (i64_type context) "tag" builder in

        let printf_func = get_printf context the_module in
        let print_fmt fmt_str args =
          let fmt_val = build_global_stringptr fmt_str "fmt" builder in
          let printf_ty =
            var_arg_function_type (i32_type context) [| ptr_ty |]
          in
          ignore
            (build_call printf_ty printf_func
               (Array.of_list (fmt_val :: args))
               "p" builder)
        in

        let bb_int = append_block context "t_int" f in
        let bb_float = append_block context "t_float" f in
        let bb_bool = append_block context "t_bool" f in
        let bb_str = append_block context "t_str" f in
        let bb_char = append_block context "t_char" f in
        let bb_end = append_block context "t_end" f in

        let sw = build_switch tag_val bb_end 5 builder in
        add_case sw (const_int (i64_type context) 1) bb_int;
        add_case sw (const_int (i64_type context) 2) bb_float;
        add_case sw (const_int (i64_type context) 3) bb_bool;
        add_case sw (const_int (i64_type context) 4) bb_str;
        add_case sw (const_int (i64_type context) 5) bb_char;

        position_at_end bb_int builder;
        let int_val =
          build_load (i64_type context) data_ptr "int_val" builder
        in
        print_fmt "%ld" [ int_val ];
        ignore (build_br bb_end builder);

        position_at_end bb_float builder;
        let flt_val =
          build_load (double_type context) data_ptr "flt_val" builder
        in
        print_fmt "%g" [ flt_val ];
        ignore (build_br bb_end builder);

        position_at_end bb_bool builder;
        let bool_val =
          build_load (i1_type context) data_ptr "bool_val" builder
        in
        let true_str = build_global_stringptr "true" "t" builder in
        let false_str = build_global_stringptr "false" "f" builder in
        let str_val = build_select bool_val true_str false_str "s" builder in
        print_fmt "%s" [ str_val ];
        ignore (build_br bb_end builder);

        position_at_end bb_str builder;
        let str_val2 = build_load ptr_ty data_ptr "str_val" builder in

        let is_null_str = build_is_null str_val2 "is_null_str" builder in
        let nil_str = build_global_stringptr "<nil>" "nil_str" builder in
        let print_str_val =
          build_select is_null_str nil_str str_val2 "print_str_val" builder
        in

        print_fmt "%s" [ print_str_val ];
        ignore (build_br bb_end builder);

        position_at_end bb_char builder;
        let char_val =
          build_load (i8_type context) data_ptr "char_val" builder
        in
        let char_val_i32 =
          build_intcast char_val (i32_type context) "char_i32" builder
        in
        print_fmt "%c" [ char_val_i32 ];
        ignore (build_br bb_end builder);

        position_at_end bb_end builder;
        ignore (build_ret_void builder);

        position_at_end saved_bb builder;
        f
  in
  let print_fn =
   fun ctx md bldr fn_name arg_vals targ_lltypes arg_asts targs codegen_expr
       llvm_type_of infer_ast_type ->
    let printf_func = get_printf context the_module in
    let printf_ty =
      var_arg_function_type (i32_type context) [| pointer_type context |]
    in

    let print_str s =
      let fmt = build_global_stringptr s "fmt" builder in
      ignore (build_call printf_ty printf_func [| fmt |] "p" builder)
    in

    let rec print_arg v ast_ty =
      let ty = type_of v in
      match classify_type ty with
      | TypeKind.Integer ->
          let bw = integer_bitwidth ty in
          if bw = 1 then begin
            let t = build_global_stringptr "true" "t" builder in
            let f = build_global_stringptr "false" "f" builder in
            let s = build_select v t f "s" builder in
            let fmt = build_global_stringptr "%s" "fmt" builder in
            ignore (build_call printf_ty printf_func [| fmt; s |] "p" builder)
          end
          else if bw <= 32 then begin
            let v_i32 = build_intcast v (i32_type context) "cast_i32" builder in
            let is_unsigned = Utils.is_unsigned ast_ty in
            let fmt_str = if is_unsigned then "%u" else "%d" in
            let fmt = build_global_stringptr fmt_str "fmt" builder in
            ignore
              (build_call printf_ty printf_func [| fmt; v_i32 |] "p" builder)
          end
          else if bw = 64 then begin
            let is_unsigned = Utils.is_unsigned ast_ty in
            let fmt_str = if is_unsigned then "%lu" else "%ld" in
            let fmt = build_global_stringptr fmt_str "fmt" builder in
            ignore (build_call printf_ty printf_func [| fmt; v |] "p" builder)
          end
          else begin
            let is_unsigned = Utils.is_unsigned ast_ty in
            let v_float =
              if is_unsigned then
                build_uitofp v (double_type context) "cast_u128_to_f64" builder
              else
                build_sitofp v (double_type context) "cast_i128_to_f64" builder
            in

            let fmt = build_global_stringptr "%e" "fmt" builder in
            ignore
              (build_call printf_ty printf_func [| fmt; v_float |] "p" builder)
          end
      | TypeKind.Double ->
          let fmt = build_global_stringptr "%f" "fmt" builder in
          ignore (build_call printf_ty printf_func [| fmt; v |] "p" builder)
      | TypeKind.Float ->
          let v_ext =
            build_fpext v (double_type context) "f32_to_f64" builder
          in
          let fmt = build_global_stringptr "%f" "fmt" builder in
          ignore (build_call printf_ty printf_func [| fmt; v_ext |] "p" builder)
      | TypeKind.Pointer -> (
          match ast_ty with
          | TFn _ ->
              let fn_str = build_global_stringptr "<fn>" "fn_str" builder in
              let fmt = build_global_stringptr "%s" "fmt" builder in
              ignore
                (build_call printf_ty printf_func [| fmt; fn_str |] "p" builder)
          | TPointer _ ->
              let fmt = build_global_stringptr "%p" "fmt" builder in
              ignore (build_call printf_ty printf_func [| fmt; v |] "p" builder)
          | _ ->
              let is_null = build_is_null v "is_null" builder in
              let nil_str = build_global_stringptr "<nil>" "nil_str" builder in
              let ptr_ty = pointer_type context in
              let v_cast = build_bitcast v ptr_ty "v_cast" builder in
              let print_val =
                build_select is_null nil_str v_cast "print_val" builder
              in
              let fmt = build_global_stringptr "%s" "fmt" builder in
              ignore
                (build_call printf_ty printf_func [| fmt; print_val |] "p"
                   builder))
      | TypeKind.Array ->
          print_str "[";
          let len = array_length ty in
          for i = 0 to len - 1 do
            let elem = build_extractvalue v i "ext" builder in
            let elem_ast_ty =
              match ast_ty with TArray (_, t) -> t | _ -> TUnknown
            in
            print_arg elem elem_ast_ty;
            if i < len - 1 then print_str ", "
          done;
          print_str "]"
      | TypeKind.Struct -> (
          match ast_ty with
          | TFn _ ->
              let fn_str = build_global_stringptr "<fn>" "fn_str" builder in
              let fmt = build_global_stringptr "%s" "fmt" builder in
              ignore
                (build_call printf_ty printf_func [| fmt; fn_str |] "p" builder)
          | _ ->
              let elems = struct_element_types ty in
              if
                Array.length elems = 2
                && elems.(0) = pointer_type context
                && elems.(1) = pointer_type context
              then begin
                let print_any_f = get_print_any context the_module builder in
                ignore
                  (build_call
                     (function_type (void_type context) [| ty |])
                     print_any_f [| v |] "" builder)
              end
              else if
                Array.length elems = 3
                && elems.(0) = i1_type context
                && elems.(2) = pointer_type context
              then begin
                let is_err = build_extractvalue v 0 "is_err" builder in

                let the_func = block_parent (insertion_block builder) in
                let err_bb = append_block context "res_err" the_func in
                let ok_bb = append_block context "res_ok" the_func in
                let merge_bb = append_block context "res_merge" the_func in

                ignore (build_cond_br is_err err_bb ok_bb builder);

                position_at_end err_bb builder;
                let err_msg = build_extractvalue v 2 "err_msg" builder in
                let err_fmt =
                  build_global_stringptr "Error: %s" "err_fmt" builder
                in
                ignore
                  (build_call printf_ty printf_func [| err_fmt; err_msg |] "p"
                     builder);
                ignore (build_br merge_bb builder);

                position_at_end ok_bb builder;
                let ok_val = build_extractvalue v 1 "ok_val" builder in
                let ok_ast_ty =
                  match ast_ty with TResult t -> t | _ -> TUnknown
                in
                print_arg ok_val ok_ast_ty;

                ignore (build_br merge_bb builder);

                position_at_end merge_bb builder
              end
              else begin
                print_str "{";
                let len = Array.length elems in
                for i = 0 to len - 1 do
                  let elem = build_extractvalue v i "ext" builder in
                  print_arg elem TUnknown;
                  if i < len - 1 then print_str ", "
                done;
                print_str "}"
              end)
      | _ -> print_str "(complex_type)"
    in

    let len = List.length arg_vals in
    List.iteri
      (fun i v ->
        let ast_ty = List.nth arg_asts i in
        print_arg v ast_ty;
        if i < len - 1 then print_str " ")
      arg_vals;

    if fn_name = "println" then print_str "\n";

    const_int (i32_type context) 0
  in

  Hashtbl.add registry "print" (Some print_fn);
  Hashtbl.add registry "println" (Some print_fn);
  Hashtbl.add registry "printf" (Some print_fn)
