open Ce_parser.Ast
open Ce_parser.Ast_mapper

class substituter type_map =
  object (self)
    inherit mapper as super

    method! map_type t =
      match t with
      | TGenericParam name -> (
          try List.assoc name type_map with Not_found -> TGenericParam name)
      | TNamed name -> (
          try List.assoc name type_map with Not_found -> TNamed name)
      | _ -> super#map_type t
  end

let substitute_type type_map t = (new substituter type_map)#map_type t
let substitute_expr type_map e = (new substituter type_map)#map_expr e
let substitute_stmt type_map s = (new substituter type_map)#map_stmt s
