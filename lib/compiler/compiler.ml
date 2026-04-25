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
      ignore (Llvm_all_backends.initialize ());
      let target_triple = Target.default_triple () in
      let target = Target.by_triple target_triple in
      let machine = TargetMachine.create ~triple:target_triple target in
      Llvm.set_target_triple target_triple m;
      let dl = TargetMachine.data_layout machine in
      Llvm.set_data_layout (DataLayout.as_string dl) m;
      let b = builder ce_ctx in
      Builtin.initialize ce_ctx m b;
      Hashtbl.add modules_map mname (m, b);
      (m, b)
  in

  let rec process_pending () =
    if not (Queue.is_empty env.pending_instantiations) then begin
      let stmt = Queue.pop env.pending_instantiations in
      let old_m, old_b = (!ce_module, !ce_builder) in
      let old_mod_name = !(env.current_module) in
      let saved_bb =
        try Some (insertion_block old_b) with Not_found -> None
      in

      let m, b = get_module stmt.mod_name in
      ce_module := m;
      ce_builder := b;
      ignore (Stmt.codegen env stmt);

      ce_module := old_m;
      ce_builder := old_b;
      env.current_module := old_mod_name;
      (match saved_bb with Some bb -> position_at_end bb old_b | None -> ());
      process_pending ()
    end
  in
  env.process_pending_cb := Some process_pending;

  let is_decl s =
    match s.node with
    | DefStruct _ | DefType _ | DefInterface _ -> true
    | _ -> false
  in

  List.iter
    (fun s ->
      if is_decl s then begin
        let m, b = get_module s.mod_name in
        ce_module := m;
        ce_builder := b;
        ignore (Stmt.codegen env s)
      end)
    stmts;

  process_pending ();

  let main_m, _ = get_module "main" in
  let global_init_ft = function_type (void_type ce_ctx) [||] in
  let global_init_f =
    declare_function "__ce_global_init" global_init_ft main_m
  in
  let global_init_bb = append_block ce_ctx "entry" global_init_f in
  let global_init_b = builder_at_end ce_ctx global_init_bb in

  List.iter
    (fun s ->
      if not (is_decl s) then begin
        let m, b = get_module s.mod_name in
        let is_exec =
          match s.node with
          | DefFN _ | Impl _ | DefStruct _ | DefType _ | DefInterface _
          | ExternFN _ | ExternLet _ ->
              false
          | _ -> true
        in
        if is_exec then begin
          ce_module := main_m;
          ce_builder := global_init_b
        end
        else begin
          ce_module := m;
          ce_builder := b
        end;
        ignore (Stmt.codegen env s)
      end)
    stmts;

  ignore (build_ret_void global_init_b);

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
