(* ocamlfind ocamlc -o laurent -package z3 -linkpkg laurent.ml tactics.ml *)

open Laurent

type goal = {
  ctx : context;          (* Current context *)
  target : exp;           (* Type to prove *)
  id : int;               (* Goal identifier *)
}

type proof_state = {
  goals : goal list;      (* List of open goals *)
  solved : (int * exp) list; (* Solved goals with their terms *)
}

let initial_state target = {
  goals = [{ ctx = []; target; id = 1 }];
  solved = [];
}

let next_id state = 1 + List.fold_left (fun m g -> max m g.id) 0 state.goals

let ball x delta y = And (RealIneq (Gt, Var delta, Zero),
                         RealIneq (Lt, RealOps (Minus, Var y, Var x), Var delta))

type tactic =
  | Intro of string           (* Introduce a variable *)
  | Elim of exp               (* Eliminate a term *)
  | Apply of exp              (* Apply a term or hypothesis *)
  | Existing of exp           (* Apply a term or hypothesis *)
  | Assumption                (* Use a hypothesis from context *)
  | Auto                      (* Simple automation *)
  | Split                      (* Simple automation *)
  | Exact of exp              (* Provide an exact term *)
  | Limit                     (* Apply limit definition *)
  | Continuity                (* Apply continuity definition *)
  | Near of string * exp      (* Додаємо near *)
  | ApplyLocally              (* Додаємо apply_locally *)

exception TacticError of string

let print_goal g =
  Printf.printf "Goal %d:\nContext: [" g.id;
  List.iter (fun (n, ty) -> Printf.printf "(%s : %s); " n (string_of_exp ty)) g.ctx;
  print_endline "]";
  Printf.printf "⊢ %s\n\n" (string_of_exp g.target)

let print_state state =
  List.iter print_goal state.goals;
  Printf.printf "%d goals remaining\n" (List.length state.goals)

let update_goal state goal new_target new_ctx =
  { goal with target = new_target; ctx = new_ctx; id = next_id state }

let parse_exp (s : string) : exp =
  try
    match s with
    | "0" -> Zero
    | "1" -> One
    | "2" -> RealOps (Plus, One, One)
    | s when String.length s > 0 && s.[0] = 'x' -> Var s
    | s -> RealOps (Plus, One, Zero) (* Замість RealNum, підставляємо константу 1 для простоти *)
  with _ -> Var s

let parse_tactic (input : string) : tactic =
  let parts = String.split_on_char ' ' (String.trim input) in
  match parts with
  | ["intro"; var] -> Intro var
  | ["exists"; e] -> Existing (parse_exp e)
  | ["split"] -> Split
  | ["assumption"] -> Assumption
  | ["limit"] -> Limit
  | ["continuity"] -> Continuity
  | ["near"; var; point] -> Near (var, parse_exp point)
  | ["apply_locally"] -> ApplyLocally
  | _ -> raise (TacticError ("Invalid tactic: " ^ input))

let apply_tactic env state tac =
  match tac with
  | Intro var ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | Forall (v, ty, body) ->
                let new_ctx = (v, ty) :: goal.ctx in
                let new_goal = update_goal state goal body new_ctx in
                { state with goals = new_goal :: rest }
            | _ -> raise (TacticError "Intro expects a forall"))
       | _ -> raise (TacticError "No goals"))
  | Existing e ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | Exists (var, ty, body) ->
                let new_target = subst var e body in
                let new_goal = update_goal state goal new_target goal.ctx in
                (* Перевіряємо, чи нова ціль тривіальна *)
                let simplified_target = normalize env new_goal.ctx new_target in
                if equal env new_goal.ctx simplified_target True ||
                   List.exists (fun (_, e') -> equal env new_goal.ctx e' simplified_target) new_goal.ctx
                then { state with goals = rest; solved = (new_goal.id, e) :: state.solved }
                else { state with goals = new_goal :: rest }
            | _ -> raise (TacticError "Exists expects an existential"))
       | _ -> raise (TacticError "No goals"))
  | Split ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | And (p, q) ->
                let goal1 = update_goal state goal p goal.ctx in
                let goal2 = update_goal state goal q goal.ctx in
                { state with goals = goal1 :: goal2 :: rest }
            | _ -> raise (TacticError "Split expects a conjunction"))
       | _ -> raise (TacticError "No goals"))
  | Assumption ->
      (match state.goals with
       | goal :: rest ->
           if List.exists (fun (_, e) -> equal env goal.ctx e goal.target) goal.ctx
           then { state with goals = rest; solved = (goal.id, goal.target) :: state.solved }
           else raise (TacticError "Assumption not found in context")
       | _ -> raise (TacticError "No goals"))
  | Limit ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | Limit (Seq f, x, l, p) ->
                let new_target =
                  Forall ("eps", Real,
                    Forall ("_", RealIneq (Gt, Var "eps", Zero),
                      Exists ("N", Real,
                        Forall ("n", Nat,
                          Forall ("_", RealIneq (Gt, Var "n", Var "N"),
                            RealIneq (Lt, RealOps (Abs, RealOps (Minus, App (f, Var "n"), l), Zero), Var "eps")))))) in
                let new_goal = update_goal state goal new_target goal.ctx in
                { state with goals = new_goal :: rest }
            | _ -> raise (TacticError "Limit expects a limit expression"))
       | _ -> raise (TacticError "No goals"))
  | Continuity ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | App (Var "continuous_at", Pair (f, a)) ->
                let new_target =
                  Forall ("eps", Real,
                    Forall ("_", RealIneq (Gt, Var "eps", Zero),
                      Exists ("delta", Real,
                        Forall ("_", RealIneq (Gt, Var "delta", Zero),
                          Forall ("x", Real,
                            Forall ("_", RealIneq (Lt, RealOps (Abs, RealOps (Minus, Var "x", a), Zero), Var "delta"),
                              RealIneq (Lt, RealOps (Abs, RealOps (Minus, App (f, Var "x"), App (f, a)), Zero), Var "eps"))))))) in
                let new_goal = update_goal state goal new_target goal.ctx in
                { state with goals = new_goal :: rest }
            | _ -> raise (TacticError "Continuity expects a continuous_at expression"))
       | _ -> raise (TacticError "No goals"))
  | Near (var, point) ->
      (match state.goals with
       | goal :: rest ->
           let new_var = var ^ "_near" in
           let delta_var = "delta_" ^ var in
           let near_assumption =
             And (RealIneq (Gt, Var delta_var, Zero),
                  RealIneq (Lt, RealOps (Abs, RealOps (Minus, Var new_var, point), Zero), Var delta_var)) in
           let new_ctx = (new_var, Real) :: (delta_var, Real) :: goal.ctx in
           let new_target = Forall ("_", near_assumption, goal.target) in
           let new_goal = update_goal state goal new_target new_ctx in
           { state with goals = new_goal :: rest }
       | _ -> raise (TacticError "No goals to apply near tactic"))
  | ApplyLocally ->
      (match state.goals with
       | goal :: rest ->
           (match goal.target with
            | Forall (_, And (RealIneq (Gt, delta, Zero), RealIneq (Lt, dist, delta')), consequent) ->
                let new_goal = update_goal state goal consequent goal.ctx in
                { state with goals = new_goal :: rest }
            | _ -> raise (TacticError "ApplyLocally expects a forall with a ball assumption"))
       | _ -> raise (TacticError "No goals to apply apply_locally tactic"))
  | Elim _ | Apply _ | Auto | Exact _ ->
      raise (TacticError "Tactic not implemented yet")


let rec console_loop env state =
  print_state state;
  if state.goals = [] then (
    Printf.printf "Proof complete!\n";
    let final_term = List.fold_left (fun acc (_, t) -> subst "P" t acc) (Var "P") state.solved in
    Printf.printf "Final term: %s\n" (string_of_exp final_term);
    final_term
  ) else (
    Printf.printf "> ";
    let input = read_line () in
    try
      let tactic = parse_tactic input in
      let new_state = apply_tactic env state tactic in
      console_loop env new_state
    with
    | TacticError msg -> Printf.printf "Error: %s\n" msg; console_loop env state
    | TypeError msg -> Printf.printf "Type error: %s\n" msg; console_loop env state
  )

let main () =
  let env = [] in
  let target = (Universe 0) in
  let state = initial_state target in
  ignore (console_loop env state)

let test_tactics () =
  let env = [] in

  (* Тест 3: Near *)
  let state3 = initial_state (Forall ("x", Real,
                                Forall ("_", App (Var "near", Var "x"),
                                     RealIneq (Lt, RealOps (Abs, RealOps (Minus, Var "x", One), Zero), RealOps (Plus, One, One))))) in
  let state3' = apply_tactic env state3 (Near ("x", One)) in
  let state3'' = apply_tactic env state3' ApplyLocally in
  Printf.printf "Testing Near and ApplyLocally:\n";
  print_state state3'';



  (* Тест 1: Границя константи *)
  let state1 = initial_state (Limit (Seq (Lam ("n", Nat, One)), Infinity, One, Var "p")) in
  let state1' = apply_tactic env state1 Limit in
  let state1'' = apply_tactic env state1' (Intro "eps") in
  let state1''' = apply_tactic env state1'' (Existing One) in
  Printf.printf "Testing Limit on constant:\n";
  print_state state1''';
  (* Додаємо Assumption для завершення *)
  let state1'''' = apply_tactic env state1''' Assumption in
  Printf.printf "After Assumption:\n";
  print_state state1'''';

  (* Тест 2: Неперервність константи *)
  let state2 = initial_state (App (Var "continuous_at", Pair (Lam ("x", Real, One), One))) in
  let state2' = apply_tactic env state2 Continuity in
  let state2'' = apply_tactic env state2' (Intro "eps") in
  let state2''' = apply_tactic env state2'' (Existing One) in
  Printf.printf "Testing Continuity on constant:\n";
  print_state state2''';
  let state2'''' = apply_tactic env state2''' Assumption in
  Printf.printf "After Assumption:\n";
  print_state state2'''';

  Printf.printf "Simple tactics tests passed!\n"

let banner =
"https://laurent.groupoid.space/

  🧊 Laurent Theorem Prover version 0.5 (c) 2025 Groupoїd Infinity

For help type `help`."

let () = test_tactics (); print_endline banner; main ()
