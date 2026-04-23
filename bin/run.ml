open Ce_compiler
open Cmdliner

let execute optimization file =
  let visited = Hashtbl.create 10 in
  let binary_name = Build.remove_extension file in
  let optimization = if optimization == "" then "3" else optimization in
  let _ =
    try
      file |> Build.process_file visited
      |> Compiler.compile ~opt:optimization
      |> Build.export binary_name
    with Failure msg ->
      Printf.printf "Error: %s\n" msg;
      exit 1
  in

  let binary_name =
    if not (String.contains binary_name '/') then "./" ^ binary_name
    else binary_name
  in
  binary_name |> Sys.command |> fun code -> if code <> 0 then exit code

let command =
  let doc = "Compile inserted ce-lang code file then execute that" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info Term.(const execute $ Command.opt_flag $ Command.file_arg)
