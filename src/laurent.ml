(* ocamlfind ocamlc -o laurent -package z3 -linkpkg laurent.ml tactics.ml *)

open Tactics
open Inferer
open Theorems
open Suite

let main () =
  let env = [] in
  ignore (console_loop env state2)

let banner =
"https://laurent.groupoid.space/

  🧊 Laurent Theorem Prover version 0.5 (c) 2025 Groupoїd Infinity

For help type `help`."

let () = test_tactics (); print_endline banner; main ()
