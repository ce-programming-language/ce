open Ce_parser.Ast

exception Error of string

let mk_error (loc : loc) msg =
  Error (Printf.sprintf "%s:%d:%d: %s" loc.file loc.line loc.col msg)

let cant_access_private_on_struct ?loc prop name =
  let m =
    "Cannot access private property or method '" ^ prop ^ "' on struct '" ^ name
    ^ "'"
  in
  match loc with Some v -> mk_error v m | None -> Error m

let cant_call_private_on_struct ?loc met name =
  let m = "Cannot call private method '" ^ met ^ "' on type '" ^ name ^ "'" in
  match loc with Some v -> mk_error v m | None -> Error m

let cant_access_prop_on_nonstruct ?loc prop =
  let m = "Cannot access property '" ^ prop ^ "' on non-struct" in
  match loc with Some v -> mk_error v m | None -> Error m

let cant_call_method_on_nonstruct ?loc prop =
  let m = "Cannot call method '" ^ prop ^ "' on non-struct" in
  match loc with Some v -> mk_error v m | None -> Error m

let cant_infer_type_for_var loc name =
  mk_error loc
    ("Cannot infer type for variable '" ^ name
   ^ "'. Please specify the type explicitly.")

let cant_infer_type_without_init loc name =
  mk_error loc ("Cannot infer type for '" ^ name ^ "' without initialization")

let main_must_public loc =
  mk_error loc "The main function must be public. Use 'pub fn main'"

let function_missing_return loc name =
  mk_error loc ("Function '" ^ name ^ "' is missing a return statement")

let cant_assign_immutable_field loc prop name =
  mk_error loc
    ("Cannot assign to immutable field '" ^ prop ^ "' on struct '" ^ name ^ "'")

let unknown_var_fn loc name =
  mk_error loc ("Unknown variable or function: '" ^ name ^ "'")

let unknown_prop loc prop name =
  mk_error loc ("Unknown property '" ^ prop ^ "' on struct '" ^ name ^ "'")

let unknown_method loc met name =
  mk_error loc ("Unknown method '" ^ met ^ "' on struct '" ^ name ^ "'")

let unknown_fn loc name =
  mk_error loc ("Unknown function or method: '" ^ name ^ "'")

let cant_assign_immutable_var loc name =
  mk_error loc ("Cannot assign to immutable variable '" ^ name ^ "'")

let break_outside_loop loc = mk_error loc "Break outside of a loop"

let cant_assign_immutable_arr loc name =
  mk_error loc ("Cannot assign to immutable array '" ^ name ^ "'")

let left_side_dereference_assignment_must_pointer loc =
  mk_error loc "Left-hand side of dereference assignment must be a pointer"

let cant_reference_nonvar loc =
  mk_error loc "Can only reference variables (e.g., &a)"

let cant_dereference_nonpointer loc =
  mk_error loc "Cannot dereference non-pointer expression"

let cant_implicitly_cast loc =
  mk_error loc "Type mismatch: Could not implicitly cast value to expected type"

let cant_find_struct loc name =
  mk_error loc ("Could not find struct definition for '" ^ name ^ "'")

let tuple_index_out_bounds loc prop =
  mk_error loc ("Tuple index out of bounds: " ^ prop)

let cant_apply_operator loc operator =
  mk_error loc ("Cannot apply " ^ operator ^ " operator")

let generic_requires_type loc name =
  mk_error loc (name ^ "' is generic and requires type arguments")

let catch_handler_must_fn loc = mk_error loc "Catch handler must be a function"
