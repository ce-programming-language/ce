open Cmdliner
open Lsp.Types
open Linol_lwt
open Ce_parser.Ast

let log msg = Printf.eprintf "[ce-lsp] %s\n%!" msg
let documents : (string, string) Hashtbl.t = Hashtbl.create 10
let signatures : (string * string, string) Hashtbl.t = Hashtbl.create 50

let definitions : (string * string, Linol_lsp.Lsp.Types.Location.t) Hashtbl.t =
  Hashtbl.create 50

type analysis_result = {
  symbols : DocumentSymbol.t list;
  hints : InlayHint.t list;
  lenses : CodeLens.t list;
  completions : (string, CompletionItemKind.t) Hashtbl.t;
}

let analyses : (string, analysis_result) Hashtbl.t = Hashtbl.create 10

let check_syntax src =
  Ce_lexer.Lexer.reset_state ();
  let lexbuf = Lexing.from_string src in
  try
    let _ast = Ce_parser.Parser.prog Ce_lexer.Lexer.tokenize lexbuf in
    None
  with
  | Ce_parser.Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let line = pos.pos_lnum - 1 in
      let col = pos.pos_cnum - pos.pos_bol in
      Some (line, col, "Syntax Error: unexpected token")
  | Ce_lexer.Lexer.Lexer_error (msg, pos) ->
      let line = pos.pos_lnum - 1 in
      let col = pos.pos_cnum - pos.pos_bol in
      Some (line, col, "Lexer Error: " ^ msg)
  | e -> Some (0, 0, "Unknown Error: " ^ Printexc.to_string e)

let publish_diags notify_back uri src =
  let diags =
    match check_syntax src with
    | None -> []
    | Some (line, col, msg) ->
        let start_pos = Position.create ~line ~character:col in
        let end_pos = Position.create ~line ~character:(col + 1) in
        let range = Range.create ~start:start_pos ~end_:end_pos in
        let diagnostic = Diagnostic.create ~range ~message:(`String msg) () in
        [ diagnostic ]
  in
  notify_back#send_diagnostic diags

let get_word_at_pos content line col =
  let lines = String.split_on_char '\n' content in
  try
    let target_line = List.nth lines line in
    let is_ident c =
      match c with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
      | _ -> false
    in
    let start_idx = ref col in
    while !start_idx > 0 && is_ident target_line.[!start_idx - 1] do
      decr start_idx
    done;
    let end_idx = ref col in
    let len = String.length target_line in
    while !end_idx < len && is_ident target_line.[!end_idx] do
      incr end_idx
    done;
    if !start_idx < !end_idx then
      String.sub target_line !start_idx (!end_idx - !start_idx)
    else ""
  with _ -> ""

let get_hover_docs word =
  match word with
  | "println" ->
      Some
        "```ce\n\
         fn println(args... any) void\n\
         ```\n\
         Prints values to stdout, followed by a newline."
  | "print" ->
      Some "```ce\nfn print(args... any) void\n```\nPrints values to stdout."
  | "printf" ->
      Some
        "```ce\n\
         fn printf(fmt string, args... any) void\n\
         ```\n\
         Formats and prints values to stdout."
  | "malloc" ->
      Some
        "```ce\n\
         fn malloc<T>(count uint) *T\n\
         ```\n\
         Allocates space on the heap for `count` elements of type `T`."
  | "realloc" ->
      Some
        "```ce\n\
         fn realloc<T>(ptr *T, new_size uint) *T\n\
         ```\n\
         Reallocates memory to a new size."
  | "free" ->
      Some
        "```ce\n\
         fn free<T>(ptr *T) void\n\
         ```\n\
         Frees memory previously allocated by `malloc`."
  | "typeof" ->
      Some
        "```ce\n\
         fn typeof(val any) string\n\
         ```\n\
         Returns the name of the type of the given value."
  | "fn" -> Some "**fn**\n\nDeclares a new function."
  | "let" -> Some "**let**\n\nDeclares a variable."
  | "mut" -> Some "**mut**\n\nMarks a variable or struct field as mutable."
  | "struct" -> Some "**struct**\n\nDeclares a custom data structure."
  | "trait" -> Some "**trait**\n\nDeclares an interface/trait."
  | "impl" -> Some "**impl**\n\nImplements methods for a struct or trait."
  | "int" | "string" | "bool" | "float" | "char" | "void" | "uint" | "u8" | "i8"
  | "i32" | "i64" | "f32" | "f64" ->
      Some ("```ce\n" ^ word ^ "\n```\n\nBuilt-in primitive type.")
  | _ -> None

let parse_ast src =
  Ce_lexer.Lexer.reset_state ();
  let lexbuf = Lexing.from_string src in
  try Some (Ce_parser.Parser.prog Ce_lexer.Lexer.tokenize lexbuf)
  with _ -> None

let analyze_document uri src =
  let uri_str = DocumentUri.to_string uri in
  match parse_ast src with
  | None -> ()
  | Some ast ->
      let symbols = ref [] in
      let hints = ref [] in
      let lenses = ref [] in
      let completions : (string, Linol_lsp.Types.CompletionItemKind.t) Hashtbl.t
          =
        Hashtbl.create 50
      in
      let lines = String.split_on_char '\n' src in

      let get_line l =
        if l >= 0 && l < List.length lines then String.trim (List.nth lines l)
        else ""
      in

      let add_def name (loc : Ce_parser.Ast.loc) kind =
        let start_line = loc.line - 1 in
        let start_col = loc.col in
        let end_line = loc.end_line - 1 in
        let end_col = loc.end_col in

        let start_pos = Position.create ~line:start_line ~character:start_col in
        let end_pos = Position.create ~line:end_line ~character:end_col in
        let range = Range.create ~start:start_pos ~end_:end_pos in

        let selection_end_pos =
          Position.create ~line:start_line
            ~character:(start_col + String.length name)
        in
        let selection_range =
          Range.create ~start:start_pos ~end_:selection_end_pos
        in

        let lsp_loc = Location.create ~uri ~range in
        Hashtbl.replace definitions (uri_str, name) lsp_loc;
        Hashtbl.replace signatures (uri_str, name) (get_line start_line);

        let symbol =
          DocumentSymbol.create ~name ~kind ~range
            ~selectionRange:selection_range ()
        in
        symbols := symbol :: !symbols;
        let comp_kind =
          match kind with
          | SymbolKind.Function -> CompletionItemKind.Function
          | SymbolKind.Struct -> CompletionItemKind.Struct
          | SymbolKind.Interface -> CompletionItemKind.Interface
          | SymbolKind.Method -> CompletionItemKind.Method
          | _ -> CompletionItemKind.Variable
        in
        Hashtbl.replace completions name comp_kind
      in

      let rec visit_stmt (s : Ce_parser.Ast.stmt) =
        match s.node with
        | DefLet (name, _, ty, expr_opt) -> (
            add_def name s.loc SymbolKind.Variable;
            if ty = TUnknown then begin
              let inferred =
                match expr_opt with
                | Some { node = Int _ } -> "int"
                | Some { node = Float _ } -> "float"
                | Some { node = String _ } -> "string"
                | Some { node = Bool _ } -> "bool"
                | Some { node = Char _ } -> "char"
                | _ -> "any"
              in
              let line = s.loc.line - 1 in
              let col = s.loc.col + 4 + String.length name in
              let pos = Position.create ~line ~character:col in
              let hint =
                InlayHint.create ~position:pos
                  ~label:(`String (": " ^ inferred))
                  ~kind:InlayHintKind.Type ~paddingLeft:false ~paddingRight:true
                  ()
              in
              hints := hint :: !hints
            end;
            match expr_opt with Some e -> visit_expr e | None -> ())
        | DefFN (name, _, _, _, body) ->
            add_def name s.loc SymbolKind.Function;
            if name = "main" then begin
              let start_line = s.loc.line - 1 in
              let end_line = s.loc.end_line - 1 in
              let range =
                Range.create
                  ~start:(Position.create ~line:start_line ~character:s.loc.col)
                  ~end_:
                    (Position.create ~line:end_line ~character:s.loc.end_col)
              in
              let command =
                Command.create ~title:"▶ Run Program" ~command:"ce.run"
                  ~arguments:[ `String uri_str ]
                  ()
              in
              lenses := CodeLens.create ~range ~command () :: !lenses
            end;
            List.iter visit_stmt body
        | DefStruct (name, _, _) -> add_def name s.loc SymbolKind.Struct
        | DefInterface (name, _) -> add_def name s.loc SymbolKind.Interface
        | Impl (_, _, methods) ->
            List.iter
              (fun (m_name, _, _, _, _, _, body) ->
                add_def m_name s.loc SymbolKind.Method;
                List.iter visit_stmt body)
              methods
        | Assign (_, e)
        | ArrayAssign (_, _, e)
        | DerefAssign (_, e)
        | Return e
        | Raise e ->
            visit_expr e
        | Block stmts -> List.iter visit_stmt stmts
        | Expr e -> visit_expr e
        | For (i, c, m, stmts) ->
            (match i with Some st -> visit_stmt st | None -> ());
            (match c with Some ex -> visit_expr ex | None -> ());
            (match m with Some st -> visit_stmt st | None -> ());
            List.iter visit_stmt stmts
        | ForEach (_, _, iter, stmts) ->
            visit_expr iter;
            List.iter visit_stmt stmts
        | _ -> ()
      and visit_expr (e : Ce_parser.Ast.expr) =
        match e.node with
        | Struct (_, _, fields) ->
            List.iter (fun (_, ex) -> visit_expr ex) fields
        | Call (_, _, args) -> List.iter visit_expr args
        | Array (_, _, elems) -> List.iter visit_expr elems
        | ArrayAccess (_, idx) -> visit_expr idx
        | If (c, tb, elifs, eb) -> (
            visit_expr c;
            List.iter visit_stmt tb;
            List.iter
              (fun (ec, eb) ->
                visit_expr ec;
                List.iter visit_stmt eb)
              elifs;
            match eb with Some e -> List.iter visit_stmt e | None -> ())
        | Tuple elems -> List.iter visit_expr elems
        | AnonFN (_, _, body) -> List.iter visit_stmt body
        | Catch (ex, _, _, body) ->
            visit_expr ex;
            List.iter visit_stmt body
        | CatchExpr (ex, handler) ->
            visit_expr ex;
            visit_expr handler
        | Add (l, r)
        | Sub (l, r)
        | Mul (l, r)
        | Div (l, r)
        | Mod (l, r)
        | Eq (l, r)
        | Lt (l, r)
        | Lte (l, r)
        | Gt (l, r)
        | Gte (l, r)
        | And (l, r)
        | Or (l, r) ->
            visit_expr l;
            visit_expr r
        | Neg ex | Not ex | Ref ex | Deref ex -> visit_expr ex
        | _ -> ()
      in

      List.iter visit_stmt ast;
      let result =
        {
          symbols = List.rev !symbols;
          hints = List.rev !hints;
          lenses = List.rev !lenses;
          completions;
        }
      in
      Hashtbl.replace analyses uri_str result

let get_dynamic_completions uri_str =
  match Hashtbl.find_opt analyses uri_str with
  | Some res ->
      Hashtbl.fold
        (fun label kind acc -> CompletionItem.create ~label ~kind () :: acc)
        res.completions []
  | None -> []

let get_document_symbols uri_str =
  match Hashtbl.find_opt analyses uri_str with
  | Some res -> res.symbols
  | None -> []

let get_inlay_hints uri_str =
  match Hashtbl.find_opt analyses uri_str with
  | Some res -> res.hints
  | None -> []

let get_code_lenses uri_str =
  match Hashtbl.find_opt analyses uri_str with
  | Some res -> res.lenses
  | None -> []

class ce_lsp_server =
  object (self)
    inherit Jsonrpc2.server as super
    method! config_hover = Some (`Bool true)
    method! config_definition = Some (`Bool true)
    method! config_symbol = Some (`Bool true)
    method! config_inlay_hints = Some (`Bool true)

    method! config_code_lens_options =
      Some (CodeLensOptions.create ~resolveProvider:false ())

    method! config_completion =
      Some
        (Linol_lsp.Lsp.Types.CompletionOptions.create ~resolveProvider:false ())

    method spawn_query_handler f = Lwt.async f

    method on_notif_doc_did_open ~notify_back d ~content =
      Hashtbl.replace documents (DocumentUri.to_string d.uri) content;
      analyze_document d.uri content;
      publish_diags notify_back d.uri content

    method on_notif_doc_did_close ~notify_back:_ uri =
      Hashtbl.remove documents (DocumentUri.to_string uri.uri);
      Hashtbl.remove analyses (DocumentUri.to_string uri.uri);
      Lwt.return_unit

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_ ~new_content
        =
      Hashtbl.replace documents (DocumentUri.to_string d.uri) new_content;
      analyze_document d.uri new_content;
      publish_diags notify_back d.uri new_content

    method! on_req_execute_command ~notify_back ~id:_ ~workDoneToken:_ _command
        _args =
      Lwt.return `Null

    method! on_req_completion ~notify_back:_ ~id:_ ~uri ~pos:_ ~ctx:_
        ~workDoneToken:_ ~partialResultToken:_ _doc_state =
      let uri_str = DocumentUri.to_string uri in

      let create_keyword label =
        CompletionItem.create ~label ~kind:CompletionItemKind.Keyword ()
      in

      let create_type label =
        CompletionItem.create ~label ~kind:CompletionItemKind.TypeParameter ()
      in

      let keywords =
        List.map create_keyword
          [
            "let";
            "mut";
            "if";
            "else";
            "for";
            "break";
            "return";
            "import";
            "type";
            "impl";
            "raise";
            "catch";
            "struct";
            "trait";
            "true";
            "false";
            "nil";
          ]
      in

      let types =
        List.map create_type
          [
            "int";
            "string";
            "bool";
            "float";
            "char";
            "void";
            "i8";
            "i16";
            "i32";
            "i64";
            "i128";
            "uint";
            "u8";
            "u16";
            "u32";
            "u64";
            "u128";
            "f32";
            "f64";
          ]
      in

      let fn_snippet =
        CompletionItem.create ~label:"fn" ~kind:CompletionItemKind.Snippet
          ~insertText:"fn ${1:name}(${2}) ${3:void} {\n  $0\n}"
          ~insertTextFormat:InsertTextFormat.Snippet
          ~detail:"Define a new function" ()
      in
      let dynamic_items = get_dynamic_completions uri_str in
      let items = fn_snippet :: (keywords @ types @ dynamic_items) in
      Lwt.return_some (`List items)

    method! on_req_hover ~notify_back:_ ~id:_ ~uri ~pos ~workDoneToken:_
        _doc_state =
      let uri_str = DocumentUri.to_string uri in
      match Hashtbl.find_opt documents uri_str with
      | None -> Lwt.return_none
      | Some content -> (
          let word = get_word_at_pos content pos.line pos.character in
          if word = "" then Lwt.return_none
          else
            match get_hover_docs word with
            | None -> Lwt.return_none
            | Some markdown_text ->
                let contents =
                  `MarkupContent
                    (MarkupContent.create ~kind:MarkupKind.Markdown
                       ~value:markdown_text)
                in
                let hover_response = Hover.create ~contents () in
                Lwt.return_some hover_response)

    method! on_req_definition ~notify_back:_ ~id:_ ~uri ~pos ~workDoneToken:_
        ~partialResultToken:_ _doc_state =
      let uri_str = DocumentUri.to_string uri in

      match Hashtbl.find_opt documents uri_str with
      | None -> Lwt.return_none
      | Some content -> (
          let word = get_word_at_pos content pos.line pos.character in

          if word = "" then Lwt.return_none
          else
            match Hashtbl.find_opt definitions (uri_str, word) with
            | Some loc -> Lwt.return_some (`Location [ loc ])
            | None -> Lwt.return_none)

    method on_req_symbol ~notify_back:_ ~id:_ ~uri ~workDoneToken:_
        ~partialResultToken:_ _doc_state =
      let uri_str = DocumentUri.to_string uri in
      let symbols = get_document_symbols uri_str in
      Lwt.return_some (`DocumentSymbol symbols)

    method! on_req_inlay_hint ~notify_back:_ ~id:_ ~uri ~range:_ () =
      let uri_str = DocumentUri.to_string uri in
      let hints = get_inlay_hints uri_str in
      Lwt.return_some hints

    method! on_req_code_lens ~notify_back:_ ~id:_ ~uri ~workDoneToken:_
        ~partialResultToken:_ state =
      let uri_str = DocumentUri.to_string uri in
      Lwt.return (get_code_lenses uri_str)
  end

let execute () =
  let server = new ce_lsp_server in
  let run_server () =
    let looper = Jsonrpc2.create_stdio ~env:() server in
    Jsonrpc2.run looper
  in
  Lwt_main.run (run_server ())

let command =
  let doc = "Compile inserted ce-lang code file then execute that" in
  let info = Cmd.info "lsp" ~doc in
  Cmd.v info Term.(const execute $ const ())
