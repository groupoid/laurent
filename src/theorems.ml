(* ocamlfind ocamlc -o laurent -package z3 -linkpkg laurent.ml tactics.ml *)

open Inferer
open Suite
open Tactics

let state1 = initial_state
    (Limit (
      Seq (Lam ("n", Nat, One)),
      Infinity,
      One,
      Var "p"))

let state2 = initial_state
    (App (
      Var "continuous_at",
      Pair (Lam ("x", Real, One), One)))

let state3 = initial_state
    (Forall ("x", Real,
      Forall ("_", App (Var "near", Var "x"),
        RealIneq (Lt,
          RealOps (Abs, RealOps (Minus, Var "x", One), Zero),
          RealOps (Plus, One, One)))))

let test_tactics () =
  let env = [] in

  let state3' = apply_tactic env state3 (Near ("x", One)) in
  let state3'' = apply_tactic env state3' ApplyLocally in
  Printf.printf "Testing Near and ApplyLocally:\n";
  print_state state3'';

  let state1' = apply_tactic env state1 Limit in
  let state1'' = apply_tactic env state1' (Intro "eps") in
  let state1''' = apply_tactic env state1'' (Existing One) in
  let state1'''' = apply_tactic env state1''' Assumption in
  Printf.printf "Testing Limit, Existing and Assumption:\n";
  print_state state1'''';

  let state2' = apply_tactic env state2 Continuity in
  let state2'' = apply_tactic env state2' (Intro "eps") in
  let state2''' = apply_tactic env state2'' (Existing One) in
  let state2'''' = apply_tactic env state2''' Assumption in
  Printf.printf "Testing Continuity, Existing and Assumption:\n";
  print_state state2'''';

  Printf.printf "Simple tactics tests passed!\n"

