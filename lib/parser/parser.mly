%{
  open Ast

  let rec attach_generic_call e targs args =
    match e with
    | Let id -> Call(id, targs, args)
    | CatchExpr(l, r) -> CatchExpr(l, attach_generic_call r targs args)
    | Add(l, r) -> Add(l, attach_generic_call r targs args)
    | Sub(l, r) -> Sub(l, attach_generic_call r targs args)
    | Mul(l, r) -> Mul(l, attach_generic_call r targs args)
    | Div(l, r) -> Div(l, attach_generic_call r targs args)
    | Mod(l, r) -> Mod(l, attach_generic_call r targs args)
    | Eq(l, r) -> Eq(l, attach_generic_call r targs args)
    | Lt(l, r) -> Lt(l, attach_generic_call r targs args)
    | Lte(l, r) -> Lte(l, attach_generic_call r targs args)
    | Gt(l, r) -> Gt(l, attach_generic_call r targs args)
    | Gte(l, r) -> Gte(l, attach_generic_call r targs args)
    | And(l, r) -> And(l, attach_generic_call r targs args)
    | Or(l, r) -> Or(l, attach_generic_call r targs args)
    | Not e -> Not (attach_generic_call e targs args)
    | Neg e -> Neg (attach_generic_call e targs args)
    | Ref e -> Ref (attach_generic_call e targs args)
    | Deref e -> Deref (attach_generic_call e targs args)
    | _ -> raise (Failure "Invalid generic function call")

  let rec attach_generic_struct e targs fields =
    match e with
    | Let id -> Struct(id, targs, fields)
    | CatchExpr(l, r) -> CatchExpr(l, attach_generic_struct r targs fields)
    | Add(l, r) -> Add(l, attach_generic_struct r targs fields)
    | Sub(l, r) -> Sub(l, attach_generic_struct r targs fields)
    | Mul(l, r) -> Mul(l, attach_generic_struct r targs fields)
    | Div(l, r) -> Div(l, attach_generic_struct r targs fields)
    | Mod(l, r) -> Mod(l, attach_generic_struct r targs fields)
    | Eq(l, r) -> Eq(l, attach_generic_struct r targs fields)
    | Lt(l, r) -> Lt(l, attach_generic_struct r targs fields)
    | Lte(l, r) -> Lte(l, attach_generic_struct r targs fields)
    | Gt(l, r) -> Gt(l, attach_generic_struct r targs fields)
    | Gte(l, r) -> Gte(l, attach_generic_struct r targs fields)
    | And(l, r) -> And(l, attach_generic_struct r targs fields)
    | Or(l, r) -> Or(l, attach_generic_struct r targs fields)
    | Not e -> Not (attach_generic_struct e targs fields)
    | Neg e -> Neg (attach_generic_struct e targs fields)
    | Ref e -> Ref (attach_generic_struct e targs fields)
    | Deref e -> Deref (attach_generic_struct e targs fields)
    | _ -> raise (Failure "Invalid generic struct instantiation")
%}

%token <int>    INT
%token <float>  FLOAT
%token <string> STRING IDENT
%token <char>   CHAR
%token          PLUS MINUS STAR SLASH MOD EQEQ LT LTE GT GTE AND OR BANG
%token          LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA EQUALS DOT AMP SEMICOLON
%token          EOF RETURN IMPORT BREAK NEWLINE TYPE IMPL RAISE CATCH STRUCT TRAIT EXTERN
%token          TYPE_BOOL TYPE_VOID TYPE_STRING TYPE_CHAR
%token          TYPE_INT TYPE_I8 TYPE_I16 TYPE_I32 TYPE_I64 TYPE_I128
%token          TYPE_UINT TYPE_U8 TYPE_U16 TYPE_U32 TYPE_U64 TYPE_U128
%token          TYPE_FLOAT TYPE_F32 TYPE_F64
%token          LET MUT TRUE FALSE FN IF ELSE FOR NIL

%left OR AND
%left EQEQ LT LTE GT GTE
%left PLUS MINUS
%left STAR SLASH MOD
%nonassoc UMINUS

%start <Ast.stmt list> prog
%%

prog:
  | sep_opt EOF                 { [] }
  | sep_opt global_stmt_list EOF       { $2 }

sep:
  | NEWLINE       { () }
  | sep NEWLINE   { () }

sep_opt:
  |   { () }
  | sep           { () }

global_stmt_list:
  | global_stmt                           { [$1] }
  | global_stmt sep                       { [$1] }
  | global_stmt sep global_stmt_list      { $1 :: $3 }

global_stmt:
  | def_fn          { $1 }
  | def_let         { $1 }
  | def_type        { $1 }
  | def_struct      { $1 }
  | def_trait       { $1 }
  | def_extern      { $1 }
  | IMPORT path = module_path { Import path }
  | IMPL struct_name = impl_target params = generic_params_opt LBRACE sep_opt methods = impl_method_list RBRACE
      { Impl (struct_name, params, methods) }

stmt:
  | def_fn          { $1 }
  | def_let         { $1 }
  | def_type        { $1 }
  | def_struct      { $1 }
  | def_trait       { $1 }
  | def_extern      { $1 }
  | name = path EQUALS e = expr { Assign (name, e) }
  | name = path LBRACKET idx = expr RBRACKET EQUALS e = expr { ArrayAssign (name, idx, e) }
  | STAR ptr = expr_simple EQUALS e = expr { DerefAssign (ptr, e) }
  | RETURN expr     { Return $2 }
  | RETURN          { Return Void }
  | BREAK           { Break }
  | block           { Block $1 }
  | expr            { Expr $1 }
  | RAISE e = expr  { Raise e }
  | IMPL struct_name = impl_target params = generic_params_opt LBRACE sep_opt methods = impl_method_list RBRACE
      { Impl (struct_name, params, methods) }
  | FOR body = block { For (None, None, None, body) }
  | FOR cond = expr_no_struct body = block { For (None, Some cond, None, body) }
  | FOR init = for_init SEMICOLON cond = expr_no_struct body = block { For (Some init, Some cond, None, body) }
  | FOR init = for_init SEMICOLON cond = expr_no_struct SEMICOLON mut = for_mut body = block { For (Some init, Some cond, Some mut, body) }

block:
  | LBRACE sep_opt RBRACE             { [] }
  | LBRACE sep_opt stmt_list RBRACE   { $3 }

stmt_if:
  | IF e = expr_no_struct body = block tail = stmt_if_tail
    { let (elif_branches, else_body) = tail in 
      ( If (e, body, elif_branches, else_body) ) }

stmt_if_tail:
  | { ([], None) }
  | ELSE IF e = expr_no_struct body = block tail = stmt_if_tail 
      { let (elif_branches, else_body) = tail in ((e, body) :: elif_branches, else_body) }
  | ELSE body = block { ([], Some body) }

stmt_list:
  | stmt                  { [$1] }
  | stmt sep              { [$1] }
  | stmt sep stmt_list    { $1 :: $3 }

def_let:
  | LET name = IDENT ty = types EQUALS e = expr { DefLet (name, false, ty, Some e) }
  | LET MUT name = IDENT ty = types EQUALS e = expr { DefLet (name, true, ty, Some e) }
  | LET name = IDENT ty = types                 { DefLet (name, false, ty, None) }
  | LET MUT name = IDENT ty = types             { DefLet (name, true, ty, None) }

  | LET name = IDENT EQUALS e = expr            { DefLet (name, false, TUnknown, Some e) }
  | LET MUT name = IDENT EQUALS e = expr        { DefLet (name, true, TUnknown, Some e) }

type_scalar:
  | TYPE_VOID  { TVoid }
  | TYPE_STRING{ TString }
  | TYPE_CHAR  { TChar }
  | TYPE_BOOL  { TBool }
  | TYPE_INT   { TI32 } | TYPE_I8 { TI8 } | TYPE_I16 { TI16 } | TYPE_I32 { TI32 } | TYPE_I64 { TI64 } | TYPE_I128 { TI128 }
  | TYPE_UINT  { TU32 } | TYPE_U8 { TU8 } | TYPE_U16 { TU16 } | TYPE_U32 { TU32 } | TYPE_U64 { TU64 } | TYPE_U128 { TU128 }
  | TYPE_FLOAT { TF64 } | TYPE_F32 { TF32 } | TYPE_F64 { TF64 }
  | id = path { TNamed id }

types:
  | t = type_scalar                       { t }
  | LBRACKET n = INT RBRACKET ty = types  { TArray (n, ty) }
  | STAR ty = types                       { TPointer ty }
  | name = path LT arg_tys = separated_nonempty_list(COMMA, types) GT { TGenericInst (name, arg_tys) }
  | BANG ty = types                       { TResult ty }
  | LPAREN t = types COMMA rest = separated_nonempty_list(COMMA, types) RPAREN { TTuple (t :: rest) }
  | FN LPAREN RPAREN ret_ty = types { TFn([], ret_ty) }
  | FN LPAREN arg_tys = separated_nonempty_list(COMMA, types) RPAREN ret_ty = types { TFn(arg_tys, ret_ty) }

array:
  | LBRACKET n = INT RBRACKET t = type_scalar
    LBRACE elems = separated_list(COMMA, expr) RBRACE
    {  Array (n, t, elems) }

param:
  | name = IDENT ty = types { { param_name = name; ty = ty } }

def_fn:
  | FN name = IDENT tparams = generic_params_opt LPAREN params = separated_list(COMMA, param) RPAREN ty = types body = block
    { DefFN (name, tparams, params, ty, body) }

def_type:
  | TYPE name = IDENT ty = types { DefType (name, ty) }

def_struct:
  | STRUCT name = IDENT params = generic_params_opt LBRACE sep_opt RBRACE 
    { DefStruct (name, params, []) }
  | STRUCT name = IDENT params = generic_params_opt LBRACE sep_opt fields = struct_field_list RBRACE 
    { DefStruct (name, params, fields) }

struct_field_list:
  | f = struct_field                                            { [f] }
  | f = struct_field SEMICOLON                                  { [f] }
  | f = struct_field sep                                        { [f] }
  | f = struct_field SEMICOLON sep_opt rest = struct_field_list { f :: rest }
  | f = struct_field sep rest = struct_field_list               { f :: rest }

struct_field:
  | name = IDENT ty = types             { { field_name = name; ty = ty; is_mut = false } }
  | MUT name = IDENT ty = types         { { field_name = name; ty = ty; is_mut = true } }

struct_init_list:
  | f = struct_init_field                                            { [f] }
  | f = struct_init_field SEMICOLON                                  { [f] }
  | f = struct_init_field sep                                        { [f] }
  | f = struct_init_field SEMICOLON sep_opt rest = struct_init_list  { f :: rest }
  | f = struct_init_field sep rest = struct_init_list                { f :: rest }

struct_init_field:
  | name = IDENT EQUALS e = expr { (name, e) }

module_path:
  | IDENT { [$1] }
  | IDENT DOT module_path { $1 :: $3 }

path:
  | id = IDENT { id }
  | id = IDENT DOT p = path_tail { id ^ "." ^ p }

path_tail:
  | id = IDENT { id }
  | i = INT { string_of_int i }
  | id = IDENT DOT p = path_tail { id ^ "." ^ p }
  | i = INT DOT p = path_tail { string_of_int i ^ "." ^ p }

generic_param:
  | name = IDENT ty = types { (name, ty) }

generic_params_opt:
  | { [] }
  | LT params = separated_nonempty_list(COMMA, generic_param) GT { params }

impl_method_list:
  |  { [] }
  | m = impl_method sep_opt rest = impl_method_list { m :: rest }

impl_method:
  | FN name = IDENT LPAREN self_id = IDENT RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, self_id, false, [], ret_ty, body) }
  | FN name = IDENT LPAREN AMP self_id = IDENT RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, self_id, true, [], ret_ty, body) }
  | FN name = IDENT LPAREN self_id = IDENT COMMA params = separated_list(COMMA, param) RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, self_id, false, params, ret_ty, body) }
  | FN name = IDENT LPAREN AMP self_id = IDENT COMMA params = separated_list(COMMA, param) RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, self_id, true, params, ret_ty, body) }

impl_target:
  | id = IDENT { id }
  | TYPE_INT | TYPE_I32 { "int" }
  | TYPE_FLOAT | TYPE_F64 { "float" }
  | TYPE_UINT | TYPE_U32 { "uint" }
  | TYPE_STRING { "string" }
  | TYPE_BOOL { "bool" }
  | TYPE_CHAR { "char" }
  | TYPE_I8 { "i8" } | TYPE_I16 { "i16" } | TYPE_I64 { "i64" } | TYPE_I128 { "i128" }
  | TYPE_U8 { "u8" } | TYPE_U16 { "u16" } | TYPE_U64 { "u64" } | TYPE_U128 { "u128" }
  | TYPE_F32 { "f32" }

def_trait:
  | TRAIT name = IDENT LBRACE sep_opt RBRACE 
      { DefInterface (name, []) }
  | TRAIT name = IDENT LBRACE sep_opt sigs = fn_signature_list RBRACE 
      { DefInterface (name, sigs) }

def_extern:
  | EXTERN FN name = IDENT LPAREN params = separated_list(COMMA, param) RPAREN ty = types
      { ExternFN (None, name, params, ty) }
  | EXTERN alias = STRING FN name = IDENT LPAREN params = separated_list(COMMA, param) RPAREN ty = types
      { ExternFN (Some alias, name, params, ty) }

fn_signature_list:
  | s = fn_signature                                            { [s] }
  | s = fn_signature SEMICOLON                                  { [s] }
  | s = fn_signature sep                                        { [s] }
  | s = fn_signature SEMICOLON sep_opt rest = fn_signature_list { s :: rest }
  | s = fn_signature sep rest = fn_signature_list               { s :: rest }

fn_signature:
  | FN name = IDENT LPAREN params = separated_list(COMMA, param) RPAREN ty = types 
      { { fn_name = name; params = params; ret_ty = ty } }

for_init:
  | name = IDENT ty = types EQUALS e = expr { DefLet (name, true, ty, Some e) }
  | name = IDENT EQUALS e = expr            { DefLet (name, true, TUnknown, Some e) }

for_mut:
  | name = path EQUALS e = expr_no_struct { Assign (name, e) }
  | name = path LBRACKET idx = expr RBRACKET EQUALS e = expr_no_struct { ArrayAssign (name, idx, e) }
  | STAR ptr = expr_simple EQUALS e = expr_no_struct { DerefAssign (ptr, e) }
  | e = expr_no_struct { Expr e }

expr_simple:
  | a = array                                                     { a }
  | LPAREN e = expr RPAREN                                        { e }
  | NIL                                                           { Nil }        
  | TRUE                                                          { Bool true }
  | FALSE                                                         { Bool false }
  | n = INT                                                       { Int n }
  | f = FLOAT                                                     { Float f }
  | s = STRING                                                    { String s }
  | c = CHAR                                                      { Char c }
  | id = path                                                     { Let id }
  | MINUS e = expr %prec UMINUS                                   { Neg e }
  | BANG e = expr %prec UMINUS                                    { Not e }
  | AMP e = expr_simple                                           { Ref e }
  | STAR e = expr_simple                                          { Deref e }
  | name = path LBRACKET idx = expr RBRACKET                      { ArrayAccess (name, idx) }
  
  | name = path LBRACE sep_opt RBRACE                             { Struct (name, [], []) }
  | name = path LBRACE sep_opt fields = struct_init_list RBRACE   { Struct (name, [], fields) }
  | id = path LPAREN args = separated_list(COMMA, expr) RPAREN    { Call(id, [], args) }

  | e = expr LT targs = separated_list(COMMA, types) GT LPAREN args = separated_list(COMMA, expr) RPAREN
    { attach_generic_call e targs args }
  | e = expr LT targs = separated_list(COMMA, types) GT LBRACE sep_opt RBRACE
    { attach_generic_struct e targs [] }
  | e = expr LT targs = separated_list(COMMA, types) GT LBRACE sep_opt fields = struct_init_list RBRACE
    { attach_generic_struct e targs fields }

  | e = expr_simple CATCH LPAREN id = IDENT RPAREN ty = types body = block { Catch(e, id, ty, body) }
  | e = expr_simple CATCH handler = expr_simple { CatchExpr(e, handler) }
  | LPAREN e = expr COMMA rest = separated_nonempty_list(COMMA, expr) RPAREN { Tuple (e :: rest) }
  | FN LPAREN RPAREN ty = types body = block { AnonFN([], ty, body) }
  | FN LPAREN params = separated_nonempty_list(COMMA, param) RPAREN ty = types body = block { AnonFN(params, ty, body) }

expr:
  | e = expr_simple               { e }
  | l = expr PLUS  r = expr       {  Add (l, r) }
  | l = expr MINUS r = expr       {  Sub (l, r) }
  | l = expr STAR  r = expr       {  Mul (l, r) }
  | l = expr SLASH r = expr       {  Div (l, r) }
  | l = expr MOD   r = expr       {  Mod (l, r) }
  | l = expr EQEQ  r = expr       {  Eq (l, r) }
  | l = expr LT    r = expr       {  Lt (l, r) }
  | l = expr LTE   r = expr       {  Lte (l, r) }
  | l = expr GT    r = expr       {  Gt (l, r) }
  | l = expr GTE   r = expr       {  Gte (l, r) }
  | l = expr AND   r = expr       {  And (l, r) }
  | l = expr OR    r = expr       {  Or (l, r) }
  | stmt_if { $1 }
  
expr_simple_no_struct:
  | a = array                                                     { a }
  | NIL                                                           { Nil }
  | LPAREN e = expr RPAREN                                        { e }
  | TRUE                                                          { Bool true }
  | FALSE                                                         { Bool false }
  | n = INT                                                       { Int n }
  | f = FLOAT                                                     { Float f }
  | s = STRING                                                    { String s }
  | c = CHAR                                                      { Char c }
  | id = path                                                     { Let id }
  | MINUS e = expr_no_struct %prec UMINUS                         { Neg e }
  | BANG e = expr_no_struct %prec UMINUS                          { Not e }
  | AMP e = expr_simple_no_struct                                 { Ref e }
  | STAR e = expr_simple_no_struct                                { Deref e }
  | name = path LBRACKET idx = expr RBRACKET                      { ArrayAccess (name, idx) }
  | id = path LPAREN args = separated_list(COMMA, expr) RPAREN    { Call(id, [], args) }
  | e = expr_no_struct LT targs = separated_list(COMMA, types) GT LPAREN args = separated_list(COMMA, expr) RPAREN
    { attach_generic_call e targs args }
  | LPAREN e = expr_no_struct COMMA rest = separated_nonempty_list(COMMA, expr) RPAREN { Tuple (e :: rest) }
  | FN LPAREN RPAREN ty = types body = block { AnonFN([], ty, body) }
  | FN LPAREN params = separated_nonempty_list(COMMA, param) RPAREN ty = types body = block { AnonFN(params, ty, body) }

expr_no_struct:
  | e = expr_simple_no_struct                     { e }
  | l = expr_no_struct PLUS  r = expr_no_struct   { Add (l, r) }
  | l = expr_no_struct MINUS r = expr_no_struct   { Sub (l, r) }
  | l = expr_no_struct STAR  r = expr_no_struct   { Mul (l, r) }
  | l = expr_no_struct SLASH r = expr_no_struct   { Div (l, r) }
  | l = expr_no_struct MOD   r = expr_no_struct   { Mod (l, r) }
  | l = expr_no_struct EQEQ  r = expr_no_struct   { Eq (l, r) }
  | l = expr_no_struct LT    r = expr_no_struct   { Lt (l, r) }
  | l = expr_no_struct LTE   r = expr_no_struct   { Lte (l, r) }
  | l = expr_no_struct GT    r = expr_no_struct   { Gt (l, r) }
  | l = expr_no_struct GTE   r = expr_no_struct   { Gte (l, r) }
  | l = expr_no_struct AND   r = expr_no_struct   { And (l, r) }
  | l = expr_no_struct OR    r = expr_no_struct   { Or (l, r) }
  | stmt_if { $1 }

