open Llvm
open Ce_parser.Ast

exception Error of string

type compiler_env = {
  type_aliases : (string, types) Hashtbl.t;
  named_values : (string, llvalue * types * bool) Hashtbl.t;
  function_types : (string, lltype * types list * types) Hashtbl.t;
  struct_templates :
    (string, (string * types) list * struct_field list * string) Hashtbl.t;
  impl_templates :
    ( string,
      (string * types) list
      * (string * bool * string * bool * param list * types * stmt list) list
      * string )
    Hashtbl.t;
  fn_templates :
    (string, (string * types) list * param list * types * stmt list) Hashtbl.t;
  struct_registry :
    ( string,
      lltype * (string * int * bool * types * bool) list * string )
    Hashtbl.t;
  method_registry : (string, bool * string) Hashtbl.t;
  interface_registry : (string, fn_signature list) Hashtbl.t;
  extern_aliases : (string, string) Hashtbl.t;
  loop_exit_blocks : llbasicblock Stack.t;
  current_fn_is_res : bool ref;
  current_fn_ret_ty : lltype ref;
  current_module : string ref;
  pending_instantiations : Ce_parser.Ast.stmt Queue.t;
}

let create_env context =
  {
    type_aliases = Hashtbl.create 10;
    named_values = Hashtbl.create 10;
    function_types = Hashtbl.create 10;
    struct_templates = Hashtbl.create 10;
    impl_templates = Hashtbl.create 10;
    fn_templates = Hashtbl.create 10;
    struct_registry = Hashtbl.create 10;
    method_registry = Hashtbl.create 10;
    interface_registry = Hashtbl.create 10;
    extern_aliases = Hashtbl.create 10;
    loop_exit_blocks = Stack.create ();
    current_fn_is_res = ref false;
    current_fn_ret_ty = ref @@ void_type context;
    current_module = ref "main";
    pending_instantiations = Queue.create ();
  }
