open Ce_compiler
open Cmdliner
open Llvm

let dump modules =
  List.iter
    (fun (mname, m) ->
      print_endline ("\n=== Module: " ^ mname ^ " ===");
      print_endline (string_of_llmodule m))
    modules

let execute optimization file =
  let visited = Hashtbl.create 10 in
  let ast = Build.process_file visited file in
  let optimization = if optimization = "" then "0" else optimization in
  try ast |> Compiler.compile ~opt:optimization |> dump
  with Failure msg ->
    Printf.printf "Error: %s\n" msg;
    exit 1

let command =
  let doc = "Read ce-lang code file then show debug output" in
  let info = Cmd.info "debug" ~doc in
  Cmd.v info Term.(const execute $ Command.opt_flag $ Command.file_arg)
