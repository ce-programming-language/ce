open Llvm
open Ce_parser.Ast
open State

module type TYPES = sig
  val llvm_type_of : compiler_env -> types -> lltype
  val instantiate_generic_fn : compiler_env -> string -> types list -> string
end

module type EXPR = sig
  val codegen_expr : compiler_env -> expr -> llvalue

  val coerce_value :
    compiler_env -> lltype -> llvalue -> bool -> bool -> llvalue
end

module type STMT = sig
  val codegen_block : compiler_env -> stmt list -> unit
  val codegen_stmt : compiler_env -> stmt -> llvalue
end
