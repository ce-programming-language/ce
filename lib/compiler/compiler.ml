open Llvm
open Llvm_target
open Ce_parser.Ast
open Compiler_intf

module rec Types : TYPES = Type_gen.Make (Stmt)
and Expr : EXPR = Expr_gen.Make (Types) (Stmt)
and Stmt : STMT = Stmt_gen.Make (Types) (Expr)

let optimize the_module =
  ignore (Llvm_all_backends.initialize ());
  let target_triple = Llvm_target.Target.default_triple () in
  let target_machine =
    Llvm_target.TargetMachine.create ~triple:target_triple
      (Llvm_target.Target.by_triple target_triple)
  in
  let pbo = Llvm_passbuilder.create_passbuilder_options () in
  ignore
    (Llvm_passbuilder.run_passes the_module "default<O3>" target_machine pbo);
  Llvm_passbuilder.dispose_passbuilder_options pbo;
  the_module

let compile (stmts : stmt list) =
  let env = State.create_env ce_ctx in
  Builtin.initialize ce_ctx ce_module ce_builder;
  List.iter (fun s -> ignore (Stmt.codegen env s)) stmts;
  optimize ce_module
