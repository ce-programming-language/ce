open Llvm
open Codegen
open Ce_parser.Ast

module type BUILTIN_MODULE = sig
  val register :
    llcontext ->
    llmodule ->
    llbuilder ->
    ( string,
      (llcontext ->
      llmodule ->
      llbuilder ->
      string ->
      llvalue list ->
      lltype list ->
      types list ->
      types list ->
      (expr -> llvalue) ->
      (types -> lltype) ->
      (expr -> types) ->
      llvalue)
      option )
    Hashtbl.t ->
    unit
end

let registry = Hashtbl.create 20

let initialize context the_module builder =
  Cast.register context the_module builder registry

let get name =
  let search =
    if String.ends_with ~suffix:".as" name then Hashtbl.find_opt registry ".as"
    else Hashtbl.find_opt registry name
  in
  match search with Some fn -> fn | None -> None
