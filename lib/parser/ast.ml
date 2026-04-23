open Llvm

let ce_ctx = global_context ()
let ce_module = ref (create_module ce_ctx "main")
let ce_builder = ref (builder ce_ctx)

type loc = {
  line : int;
  end_line : int;
  col : int;
  end_col : int;
  file : string;
}
[@@deriving show, eq]

type int_size = I8 | I16 | I32 | I64 | I128 [@@deriving show, eq]
type signedness = Signed | Unsigned [@@deriving show, eq]
type float_size = F32 | F64 [@@deriving show, eq]

type types =
  | TBool
  | TVoid
  | TString
  | TChar
  | TPointer of types
  | TNamed of string
  | TStruct of string
  | TResult of types
  | TInt of int_size * signedness
  | TFloat of float_size
  | TUnknown
  | TGenericParam of string
  | TGenericInst of string * types list
  | TArray of int * types
  | TTuple of types list
  | TFn of types list * types
  | TVariadic of types
[@@deriving show]

type expr = {
  id : int;
  loc : loc;
  node : expr_node;
  inferred_type : types option ref; [@opaque]
  resolved_def_id : int option ref; [@opaque]
}
[@@deriving show]

and expr_node =
  | Void
  | Nil
  | String of string
  | Char of char
  | Ref of expr
  | Catch of expr * string * types * stmt list
  | Deref of expr
  | Bool of bool
  | Int of int
  | Float of float
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Mod of expr * expr
  | Eq of expr * expr
  | Lt of expr * expr
  | Lte of expr * expr
  | Gt of expr * expr
  | Gte of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Neg of expr
  | Not of expr
  | Call of string * types list * expr list
  | Let of string
  | Array of int * types * expr list
  | ArrayAccess of string * expr
  | If of expr * stmt list * (expr * stmt list) list * stmt list option
  | Struct of string * types list * (string * expr) list
  | Tuple of expr list
  | AnonFN of param list * types * stmt list
  | CatchExpr of expr * expr
[@@deriving show]

and param = { param_name : string; ty : types }
and struct_field = { field_name : string; ty : types; is_mut : bool }
and fn_signature = { fn_name : string; params : param list; ret_ty : types }

and stmt = {
  id : int;
  loc : loc;
  node : stmt_node;
  docstring : string option;
  is_pub : bool;
  mod_name : string;
}
[@@deriving show]

and stmt_node =
  | Expr of expr
  | DefFN of string * (string * types) list * param list * types * stmt list
  | DefLet of string * bool * types * expr option
  | DefType of string * types
  | DefStruct of string * (string * types) list * struct_field list
  | Assign of string * expr
  | Impl of
      string
      * (string * types) list
      * (string * string * bool * param list * types * stmt list) list
  | ArrayAssign of string * expr * expr
  | DerefAssign of expr * expr
  | Return of expr
  | Block of stmt list
  | For of stmt option * expr option * stmt option * stmt list
  | ForEach of string option * string option * expr * stmt list
  | Break
  | Import of string list
  | ImportFrom of string list * string list
  | Raise of expr
  | DefInterface of string * fn_signature list
  | ExternFN of string option * string * param list * types
