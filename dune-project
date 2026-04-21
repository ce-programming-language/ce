(lang dune 3.22)

(name ce)

(version 0.1.0)

(generate_opam_files true)

(source
 (github hadihammurabi/ce-lang))

(authors "hadihammurabi")

(maintainers "hadihammurabi")

(license GPL-3.0-or-later)

(documentation https://ce-lang.hadihammurabi.com)

(package
 (name ce)
 (synopsis "Celang - A Good Programming Language")
 (description "A good programming language")
 (depends
  ocaml
  dune
  menhir
  ppx_deriving
  cmdliner
  fmt
  llvm
  linol
  linol-lwt
  (alcotest :with-test)
  (bisect_ppx :with-test)))

(using menhir 3.0)
