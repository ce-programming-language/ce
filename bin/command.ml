open Cmdliner

let file_arg =
  let doc = "The ce-lang file to process." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"file" ~doc)

let opt_flag =
  let doc = "Optimization level (0, 1, 2, 3, s, z)" in
  Arg.(value & opt string "" & info [ "O"; "opt" ] ~docv:"OPT" ~doc)
