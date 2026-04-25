%{
  open Ast

  let next_ast_id = ref 0
  let get_id () =
    let id = !next_ast_id in
    incr next_ast_id;
    id

  let make_loc (start_pos : Lexing.position) (end_pos : Lexing.position) =
    { line = start_pos.pos_lnum;
      col = start_pos.pos_cnum - start_pos.pos_bol;
      end_line = end_pos.pos_lnum;
      end_col = end_pos.pos_cnum - end_pos.pos_bol;
      file = start_pos.pos_fname }

  let mk_expr start_pos end_pos (node: expr_node): expr = 
    { id = get_id (); 
      loc = make_loc start_pos end_pos; 
      node; 
      inferred_type = ref None; 
      resolved_def_id = ref None }
      
  let mk_stmt is_pub start_pos end_pos (node: stmt_node): stmt = 
    { id = get_id (); 
      loc = make_loc start_pos end_pos; 
      node; 
      is_pub;
      mod_name = "main";
      docstring = None }

  let mk_stmt_pub start_pos end_pos (node: stmt_node): stmt = 
    mk_stmt true start_pos end_pos node

  let rec attach_generic_call (e: expr) targs args =
    let attached = match e.node with
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
    in { e with node = attached }

  let rec attach_generic_struct (e: expr) targs fields =
    let attached = match e.node with
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
    in { e with node = attached }
%}

%token <int>    INT
%token <float>  FLOAT
%token <string> STRING IDENT
%token <char>   CHAR
%token          PLUS MINUS STAR SLASH MOD EQEQ LT LTE GT GTE AND OR BANG
%token          LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA EQUALS DOT AMP SEMICOLON ELLIPSIS
%token          EOF RETURN IMPORT FROM BREAK NEWLINE TYPE IMPL RAISE CATCH STRUCT TRAIT EXTERN PUB
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

%inline pub_opt:
  |     { false }
  | PUB { true }

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
  | IMPORT path = module_path { mk_stmt false $startpos $endpos @@ Import path }
  | IMPORT names = separated_list(COMMA, IDENT) FROM path = module_path { mk_stmt false $startpos $endpos @@ ImportFrom (names, path) }
  | IMPL struct_name = impl_target params = generic_params_opt LBRACE sep_opt methods = impl_method_list RBRACE
      { mk_stmt false $startpos $endpos @@ Impl (struct_name, params, methods) }

stmt:
  | def_fn          { $1 }
  | def_let         { $1 }
  | def_type        { $1 }
  | def_struct      { $1 }
  | def_trait       { $1 }
  | def_extern      { $1 }
  | name = path EQUALS e = expr { mk_stmt false $startpos $endpos @@ Assign (name, e) }
  | name = path LBRACKET idx = expr RBRACKET EQUALS e = expr { mk_stmt false $startpos $endpos @@ ArrayAssign (name, idx, e) }
  | STAR ptr = expr_simple EQUALS e = expr { mk_stmt false $startpos $endpos @@ DerefAssign (ptr, e) }
  | RETURN expr     { mk_stmt false $startpos $endpos @@ Return $2 }
  | RETURN          { mk_stmt false $startpos $endpos @@ Return (mk_expr $startpos $endpos Void) }
  | BREAK           { mk_stmt false $startpos $endpos Break }
  | block           { mk_stmt false $startpos $endpos @@ Block $1 }
  | expr            { mk_stmt false $startpos $endpos @@ Expr $1 }
  | RAISE e = expr  { mk_stmt false $startpos $endpos @@ Raise e }
  | IMPL struct_name = impl_target params = generic_params_opt LBRACE sep_opt methods = impl_method_list RBRACE
      { mk_stmt false $startpos $endpos @@ Impl (struct_name, params, methods) }

  | FOR idx = IDENT COMMA v = IDENT EQUALS iter = expr_no_struct body = block { mk_stmt false $startpos $endpos @@ ForEach (Some idx, Some v, iter, body) }
  | FOR idx = IDENT EQUALS iter = expr_no_struct body = block { mk_stmt false $startpos $endpos @@ ForEach (Some idx, None, iter, body) }

  | FOR body = block { mk_stmt false $startpos $endpos @@ For (None, None, None, body) }
  | FOR cond = expr_no_struct body = block { mk_stmt false $startpos $endpos @@ For (None, Some cond, None, body) }
  | FOR init = for_init SEMICOLON cond = expr_no_struct body = block { mk_stmt false $startpos $endpos @@ For (Some init, Some cond, None, body) }
  | FOR init = for_init SEMICOLON cond = expr_no_struct SEMICOLON mut = for_mut body = block { mk_stmt false $startpos $endpos@@ For (Some init, Some cond, Some mut, body) }

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
  | p = pub_opt LET name = IDENT ty = types EQUALS e = expr { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  DefLet (name, false, ty, Some e) }
  | p = pub_opt LET MUT name = IDENT ty = types EQUALS e = expr { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefLet (name, true, ty, Some e) }
  | p = pub_opt LET name = IDENT ty = types                 { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefLet (name, false, ty, None) }
  | p = pub_opt LET MUT name = IDENT ty = types             { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefLet (name, true, ty, None) }
  | p = pub_opt LET name = IDENT EQUALS e = expr            { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefLet (name, false, TUnknown, Some e) }
  | p = pub_opt LET MUT name = IDENT EQUALS e = expr        { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefLet (name, true, TUnknown, Some e) }

type_scalar:
  | TYPE_VOID   { TVoid }
  | TYPE_STRING { TString }
  | TYPE_CHAR   { TInt (8, Unsigned) }
  | TYPE_BOOL   { TInt(1, Unsigned) }
  
  | TYPE_INT    { TInt (32, Signed) }
  | TYPE_I8     { TInt (8, Signed) }
  | TYPE_I16    { TInt (16, Signed) }
  | TYPE_I32    { TInt (32, Signed) }
  | TYPE_I64    { TInt (64, Signed) }
  | TYPE_I128   { TInt (128, Signed) }
  
  | TYPE_UINT   { TInt (32, Unsigned) }
  | TYPE_U8     { TInt (8, Unsigned) }
  | TYPE_U16    { TInt (16, Unsigned) }
  | TYPE_U32    { TInt (32, Unsigned) }
  | TYPE_U64    { TInt (64, Unsigned) }
  | TYPE_U128   { TInt (128, Unsigned) }
  
  | TYPE_FLOAT  { TFloat 64 }
  | TYPE_F32    { TFloat 32 }
  | TYPE_F64    { TFloat 64 }
  
  | id = path   { TNamed id }

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
  | name = IDENT ELLIPSIS ty = types { { param_name = name; ty = TVariadic ty } }

def_fn:
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN params = separated_list(COMMA, param) RPAREN ty = types body = block
    { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefFN (name, tparams, params, ty, body) }

def_type:
  | p = pub_opt TYPE name = IDENT ty = types { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@ DefType (name, ty) }

def_struct:
  | p = pub_opt STRUCT name = IDENT params = generic_params_opt LBRACE sep_opt RBRACE 
    { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  DefStruct (name, params, []) }
  | p = pub_opt STRUCT name = IDENT params = generic_params_opt LBRACE sep_opt fields = struct_field_list RBRACE 
    { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  DefStruct (name, params, fields) }

struct_field_list:
  | f = struct_field                                            { [f] }
  | f = struct_field SEMICOLON                                  { [f] }
  | f = struct_field sep                                        { [f] }
  | f = struct_field SEMICOLON sep_opt rest = struct_field_list { f :: rest }
  | f = struct_field sep rest = struct_field_list               { f :: rest }

struct_field:
  | p = pub_opt name = IDENT ty = types             { { field_name = name; ty = ty; is_mut = false; is_pub = p } }
  | p = pub_opt MUT name = IDENT ty = types         { { field_name = name; ty = ty; is_mut = true; is_pub = p } }

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
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN self_id = IDENT RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, tparams, p, Some self_id, false, [], ret_ty, body) }
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN AMP self_id = IDENT RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, tparams, p, Some self_id, true, [], ret_ty, body) }
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN self_id = IDENT COMMA params = separated_list(COMMA, param) RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, tparams, p, Some self_id, false, params, ret_ty, body) }
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN AMP self_id = IDENT COMMA params = separated_list(COMMA, param) RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, tparams, p, Some self_id, true, params, ret_ty, body) }
  | p = pub_opt FN name = IDENT tparams = generic_params_opt LPAREN params = separated_list(COMMA, param) RPAREN ret_ty = types LBRACE sep_opt body = stmt_list RBRACE
    { (name, tparams, p, None, false, params, ret_ty, body) }

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
  | p = pub_opt TRAIT name = IDENT LBRACE sep_opt RBRACE 
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  DefInterface (name, []) }
  | p = pub_opt TRAIT name = IDENT LBRACE sep_opt sigs = fn_signature_list RBRACE 
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  DefInterface (name, sigs) }

def_extern:
  | p = pub_opt EXTERN FN name = IDENT LPAREN params = separated_list(COMMA, param) RPAREN ty = types
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  ExternFN (None, name, params, ty) }
  | p = pub_opt EXTERN alias = STRING FN name = IDENT LPAREN params = separated_list(COMMA, param) RPAREN ty = types
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  ExternFN (Some alias, name, params, ty) }
  | p = pub_opt EXTERN LET name = IDENT ty = types
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  ExternLet (None, name, ty) }
  | p = pub_opt EXTERN alias = STRING LET name = IDENT ty = types
      { (if p then mk_stmt_pub else mk_stmt false) $startpos $endpos @@  ExternLet (Some alias, name, ty) }

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
  | name = IDENT ty = types EQUALS e = expr_no_struct { mk_stmt false $startpos $endpos @@  DefLet (name, true, ty, Some e) }
  | name = IDENT EQUALS e = expr_no_struct            { mk_stmt false $startpos $endpos @@  DefLet (name, true, TUnknown, Some e) }

for_mut:
  | name = path EQUALS e = expr_no_struct {  mk_stmt false $startpos $endpos @@ Assign (name, e) }
  | name = path LBRACKET idx = expr RBRACKET EQUALS e = expr_no_struct {  mk_stmt false $startpos $endpos @@ ArrayAssign (name, idx, e) }
  | STAR ptr = expr_simple EQUALS e = expr_no_struct {  mk_stmt false $startpos $endpos @@ DerefAssign (ptr, e) }
  | e = expr_no_struct { mk_stmt false $startpos $endpos @@  Expr e }

expr_simple:
  | a = array                                                     { mk_expr $startpos $endpos a }
  | LPAREN e = expr RPAREN                                        { e }
  | NIL                                                           { mk_expr $startpos $endpos Nil }        
  | TRUE                                                          { mk_expr $startpos $endpos @@ Bool true }
  | FALSE                                                         { mk_expr $startpos $endpos @@ Bool false }
  | n = INT                                                       { mk_expr $startpos $endpos @@ Int n }
  | f = FLOAT                                                     { mk_expr $startpos $endpos @@ Float f }
  | s = STRING                                                    { mk_expr $startpos $endpos @@ String s }
  | c = CHAR                                                      { mk_expr $startpos $endpos @@ Char c }
  | id = path                                                     { mk_expr $startpos $endpos @@ Let id }
  | MINUS e = expr %prec UMINUS                                   { mk_expr $startpos $endpos @@ Neg e }
  | BANG e = expr %prec UMINUS                                    { mk_expr $startpos $endpos @@ Not e }
  | AMP e = expr_simple                                           { mk_expr $startpos $endpos @@ Ref e }
  | STAR e = expr_simple                                          { mk_expr $startpos $endpos @@ Deref e }
  | name = path LBRACKET idx = expr RBRACKET                      { mk_expr $startpos $endpos @@ ArrayAccess (name, idx) }
  | name = path LBRACE sep_opt RBRACE                             { mk_expr $startpos $endpos @@ Struct (name, [], []) }
  | name = path LBRACE sep_opt fields = struct_init_list RBRACE   { mk_expr $startpos $endpos @@ Struct (name, [], fields) }
  | id = path LPAREN args = separated_list(COMMA, expr) RPAREN    { mk_expr $startpos $endpos @@ Call(id, [], args) }

  | e = expr LT targs = separated_list(COMMA, types) GT LPAREN args = separated_list(COMMA, expr) RPAREN
    { attach_generic_call e targs args }
  | e = expr LT targs = separated_list(COMMA, types) GT LBRACE sep_opt RBRACE
    { attach_generic_struct e targs [] }
  | e = expr LT targs = separated_list(COMMA, types) GT LBRACE sep_opt fields = struct_init_list RBRACE
    { attach_generic_struct e targs fields }

  | e = expr_simple CATCH LPAREN id = IDENT RPAREN ty = types body = block { mk_expr $startpos $endpos @@ Catch(e, id, ty, body) }
  | e = expr_simple CATCH handler = expr_simple { mk_expr $startpos $endpos @@ CatchExpr(e, handler) }
  | LPAREN e = expr COMMA rest = separated_nonempty_list(COMMA, expr) RPAREN { mk_expr $startpos $endpos @@ Tuple (e :: rest) }
  | FN LPAREN RPAREN ty = types body = block { mk_expr $startpos $endpos @@ AnonFN([], ty, body) }
  | FN LPAREN params = separated_nonempty_list(COMMA, param) RPAREN ty = types body = block { mk_expr $startpos $endpos @@ AnonFN(params, ty, body) }

expr:
  | e = expr_simple               { e }
  | l = expr PLUS  r = expr       { mk_expr $startpos $endpos @@ Add (l, r) }
  | l = expr MINUS r = expr       { mk_expr $startpos $endpos @@ Sub (l, r) }
  | l = expr STAR  r = expr       { mk_expr $startpos $endpos @@ Mul (l, r) }
  | l = expr SLASH r = expr       { mk_expr $startpos $endpos @@ Div (l, r) }
  | l = expr MOD   r = expr       { mk_expr $startpos $endpos @@ Mod (l, r) }
  | l = expr EQEQ  r = expr       { mk_expr $startpos $endpos @@ Eq (l, r) }
  | l = expr LT    r = expr       { mk_expr $startpos $endpos @@ Lt (l, r) }
  | l = expr LTE   r = expr       { mk_expr $startpos $endpos @@ Lte (l, r) }
  | l = expr GT    r = expr       { mk_expr $startpos $endpos @@ Gt (l, r) }
  | l = expr GTE   r = expr       { mk_expr $startpos $endpos @@ Gte (l, r) }
  | l = expr AND   r = expr       { mk_expr $startpos $endpos @@ And (l, r) }
  | l = expr OR    r = expr       { mk_expr $startpos $endpos @@ Or (l, r) }
  | stmt_if { mk_expr $startpos $endpos $1 }
  
expr_simple_no_struct:
  | a = array                                                     { mk_expr $startpos $endpos a }
  | NIL                                                           { mk_expr $startpos $endpos Nil }
  | LPAREN e = expr RPAREN                                        { e }
  | TRUE                                                          { mk_expr $startpos $endpos @@ Bool true }
  | FALSE                                                         { mk_expr $startpos $endpos @@ Bool false }
  | n = INT                                                       { mk_expr $startpos $endpos @@ Int n }
  | f = FLOAT                                                     { mk_expr $startpos $endpos @@ Float f }
  | s = STRING                                                    { mk_expr $startpos $endpos @@ String s }
  | c = CHAR                                                      { mk_expr $startpos $endpos @@ Char c }
  | id = path                                                     { mk_expr $startpos $endpos @@ Let id }
  | MINUS e = expr_no_struct %prec UMINUS                         { mk_expr $startpos $endpos @@ Neg e }
  | BANG e = expr_no_struct %prec UMINUS                          { mk_expr $startpos $endpos @@ Not e }
  | AMP e = expr_simple_no_struct                                 { mk_expr $startpos $endpos @@ Ref e }
  | STAR e = expr_simple_no_struct                                { mk_expr $startpos $endpos @@ Deref e }
  | name = path LBRACKET idx = expr RBRACKET                      { mk_expr $startpos $endpos @@ ArrayAccess (name, idx) }
  | id = path LPAREN args = separated_list(COMMA, expr) RPAREN    { mk_expr $startpos $endpos @@ Call(id, [], args) }
  | e = expr_no_struct LT targs = separated_list(COMMA, types) GT LPAREN args = separated_list(COMMA, expr) RPAREN
    { attach_generic_call e targs args }
  | LPAREN e = expr_no_struct COMMA rest = separated_nonempty_list(COMMA, expr) RPAREN { mk_expr $startpos $endpos @@ Tuple (e :: rest) }
  | FN LPAREN RPAREN ty = types body = block { mk_expr $startpos $endpos @@ AnonFN([], ty, body) }
  | FN LPAREN params = separated_nonempty_list(COMMA, param) RPAREN ty = types body = block { mk_expr $startpos $endpos @@ AnonFN(params, ty, body) }

expr_no_struct:
  | e = expr_simple_no_struct                     { e }
  | l = expr_no_struct PLUS  r = expr_no_struct   { mk_expr $startpos $endpos @@ Add (l, r) }
  | l = expr_no_struct MINUS r = expr_no_struct   { mk_expr $startpos $endpos @@ Sub (l, r) }
  | l = expr_no_struct STAR  r = expr_no_struct   { mk_expr $startpos $endpos @@ Mul (l, r) }
  | l = expr_no_struct SLASH r = expr_no_struct   { mk_expr $startpos $endpos @@ Div (l, r) }
  | l = expr_no_struct MOD   r = expr_no_struct   { mk_expr $startpos $endpos @@ Mod (l, r) }
  | l = expr_no_struct EQEQ  r = expr_no_struct   { mk_expr $startpos $endpos @@ Eq (l, r) }
  | l = expr_no_struct LT    r = expr_no_struct   { mk_expr $startpos $endpos @@ Lt (l, r) }
  | l = expr_no_struct LTE   r = expr_no_struct   { mk_expr $startpos $endpos @@ Lte (l, r) }
  | l = expr_no_struct GT    r = expr_no_struct   { mk_expr $startpos $endpos @@ Gt (l, r) }
  | l = expr_no_struct GTE   r = expr_no_struct   { mk_expr $startpos $endpos @@ Gte (l, r) }
  | l = expr_no_struct AND   r = expr_no_struct   { mk_expr $startpos $endpos @@ And (l, r) }
  | l = expr_no_struct OR    r = expr_no_struct   { mk_expr $startpos $endpos @@ Or (l, r) }
  | stmt_if { mk_expr $startpos $endpos $1 }

