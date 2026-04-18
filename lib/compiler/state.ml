open Llvm
open Ce_parser.Ast

exception Error of string

let type_aliases : (string, types) Hashtbl.t = Hashtbl.create 10

let named_values : (string, llvalue * types * bool) Hashtbl.t =
  Hashtbl.create 10

let function_types : (string, lltype * types) Hashtbl.t = Hashtbl.create 10

let struct_templates :
    (string, (string * types) list * struct_field list) Hashtbl.t =
  Hashtbl.create 10

let impl_templates :
    ( string,
      (string * types) list
      * (string * string * bool * param list * types * stmt list) list )
    Hashtbl.t =
  Hashtbl.create 10

let fn_templates :
    (string, (string * types) list * param list * types * stmt list) Hashtbl.t =
  Hashtbl.create 10

let struct_registry : (string, lltype * (string * int * bool) list) Hashtbl.t =
  Hashtbl.create 10

let interface_registry : (string, fn_signature list) Hashtbl.t =
  Hashtbl.create 10

let extern_aliases : (string, string) Hashtbl.t = Hashtbl.create 10
let loop_exit_blocks : llbasicblock Stack.t = Stack.create ()
let current_fn_is_res = ref false
let current_fn_ret_ty = ref (void_type ce_ctx)
