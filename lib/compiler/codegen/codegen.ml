open State
open Llvm
open Ce_parser.Ast

module type TYPES = sig
  val llvm_type_of :
    compiler_env -> (compiler_env -> stmt -> llvalue) -> types -> lltype

  val instantiate_generic_fn :
    compiler_env ->
    (compiler_env -> stmt -> llvalue) ->
    string ->
    types list ->
    string
end

module type EXPR = sig
  val coerce_value :
    compiler_env ->
    loc ->
    types ->
    types ->
    lltype ->
    llvalue ->
    bool ->
    bool ->
    llvalue

  val codegen :
    compiler_env -> (compiler_env -> stmt -> llvalue) -> expr -> llvalue
end

module type STMT = sig
  val gen_block : compiler_env -> stmt list -> unit
  val codegen : compiler_env -> stmt -> llvalue
end
