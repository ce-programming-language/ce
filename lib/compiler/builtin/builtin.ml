open Llvm
open Compiler_intf

let registry = Hashtbl.create 20

let initialize context the_module builder =
  Io.register context the_module builder registry;
  Memory.register context the_module builder registry;
  Cast.register context the_module builder registry

let get name =
  let search =
    if String.ends_with ~suffix:".as" name then Hashtbl.find_opt registry ".as"
    else Hashtbl.find_opt registry name
  in
  match search with Some fn -> fn | None -> None
