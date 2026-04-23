open Llvm
open Llvm_target
open Ce_parser.Ast
open Codegen
module Types = Types.Make ()
module Expr = Expr.Make (Types)
module Stmt = Stmt.Make (Types) (Expr)

let optimize opt_level the_module =
  ignore (Llvm_all_backends.initialize ());
  let pbo = Llvm_passbuilder.create_passbuilder_options () in
  let target_triple = Llvm_target.Target.default_triple () in
  let target_machine =
    Llvm_target.TargetMachine.create ~triple:target_triple
      (Llvm_target.Target.by_triple target_triple)
  in

  let pass_str = "default<O" ^ opt_level ^ ">" in
  ignore (Llvm_passbuilder.run_passes the_module pass_str target_machine pbo);
  Llvm_passbuilder.dispose_passbuilder_options pbo;
  the_module

let compile ?(opt = "0") (stmts : stmt list) =
  let env = State.create_env ce_ctx in
  let modules_map = Hashtbl.create 10 in

  let get_module mname =
    try Hashtbl.find modules_map mname
    with Not_found ->
      let m = create_module ce_ctx mname in
      let b = builder ce_ctx in
      Builtin.initialize ce_ctx m b;
      Hashtbl.add modules_map mname (m, b);
      (m, b)
  in

  List.iter
    (fun s ->
      let m, b = get_module s.mod_name in
      ce_module := m;
      ce_builder := b;
      ignore (Stmt.codegen env s))
    stmts;

  let rec process_pending () =
    if not (Queue.is_empty env.pending_instantiations) then begin
      let stmt = Queue.pop env.pending_instantiations in
      let m, b = get_module stmt.mod_name in
      ce_module := m;
      ce_builder := b;
      ignore (Stmt.codegen env stmt);
      process_pending ()
    end
  in
  process_pending ();

  if opt == "lto" then begin
    let lto_main = create_module ce_ctx "main" in
    Hashtbl.iter
      (fun _ (m, _) -> Llvm_linker.link_modules lto_main m)
      modules_map;
    [ ("main", optimize opt lto_main) ]
  end
  else begin
    let generated_modules = ref [] in
    Hashtbl.iter
      (fun mname (m, _) ->
        generated_modules := (mname, optimize opt m) :: !generated_modules)
      modules_map;
    !generated_modules
  end
