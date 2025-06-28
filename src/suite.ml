open Z3
open Inferer

(* LAURENT FOUNDATIONS ⚡ *)

let universal  : exp = Power Prop
let set_a      : exp = Set (Lam ("x", Real, RealIneq (Gt, Var "x", Zero)))
let sup_a      : exp = Sup set_a
let inf_a      : exp = Inf set_a

let interval_a_b (a : exp) (b : exp) : exp =
  Set (Lam ("x", Real, And (RealIneq (Lte, a, Var "x"), RealIneq (Lte, Var "x", b))))

let lebesgue_measure (a : exp) (b : exp) : exp =
    Mu (Real,
      Power (Set Real),
        Lam ("A", Set Real,
          If (RealIneq (Lte, a, b),
              RealOps (Minus, b, a),
              Infinity)))

let integral_term : exp =
    Lam ("f", Forall ("x", Real, Real),
      Lam ("a", Real,
        Lam ("b", Real,
          Lebesgue (Var "f",
            Mu (Real,
              Power (Set Real),
                Lam ("A", Set Real,
                  If (And (RealIneq (Lte, Var "a", Var "b"), SetEq (Var "A", interval_a_b (Var "a") (Var "b"))),
                      RealOps (Minus, Var "b", Var "a"),
                      Zero))),
                  interval_a_b (Var "a") (Var "b")))))

let integral_sig : exp =
    Forall ("f", Forall ("x", Real, Real), Forall ("a", Real, Forall ("b", Real, Real)))

let integral_term2 : exp =
    Lam ("f", Forall ("x", Real, Real),
        Lam ("a", Real,
            Lam ("b", Real,
                Lebesgue (Var "f", lebesgue_measure (Var "a") (Var "b"), interval_a_b (Var "a") (Var "b")))))

let l2_space : exp =
    Lam ("f", Forall ("x", Real, Real),
        RealIneq (Lt,
            Lebesgue (
                Lam ("x", Real,
                    RealOps (Pow,
                        RealOps (Abs, App (Var "f", Var "x"), Zero),
                        RealOps (Plus, One, One))),
                lebesgue_measure Zero Infinity,
                interval_a_b Zero Infinity),
            Infinity))

let sequence_a : exp =
    Lam ("n", Nat, RealOps (Div, One, NatToReal (Var "n")))

let limit_a : exp =
  Limit (Seq sequence_a, Infinity, Zero,
    Lam ("ε", Real,
      Lam ("p", RealIneq (Gt, Var "ε", Zero),
        Pair (RealOps (Div, One, Var "ε"),
          Lam ("n", Nat,
            Lam ("q", RealIneq (Gt, Var "n", Var "N"),
              RealIneq (Lt, RealOps (Abs, RealOps (Minus, App (sequence_a, Var "n"), Zero), Zero), Var "ε")))))))

(* ∃l:R,∀ε>0,∃N:R,∀n>N,∣(1+1/n)^n − l∣<ε *)

let sequence_e : exp =
  Lam ("n", Nat, RealOps (Pow, RealOps (Plus, One, RealOps (Div, One, NatToReal (Var "n"))), NatToReal (Var "n")))

let e : exp =
  Fst (Pair (RealOps (Exp, One, One),  (* e = exp(1) *)
    Limit (Seq sequence_e, Infinity, RealOps (Exp, One, One),
      Lam ("ε", Real,
        Lam ("p", RealIneq (Gt, Var "ε", Zero),
          Pair (RealOps (Div, RealOps (Exp, One, Zero), RealOps (Mul, RealOps (Plus, One, One), Var "ε")),
            Lam ("n", Nat,
              Lam ("q", RealIneq (Gt, Var "n", Var "N"),
                RealIneq (Lt, RealOps (Abs, RealOps (Minus, App (sequence_e, Var "n"), RealOps (Exp, One, One)), Zero), Var "ε")))))))))

let sigma_algebra = is_sigma_algebra (Power (Set Real))

let measurable =
  is_measurable
    (Power (Set Real))
    (Lam ("x", Real, RealOps (Pow, RealOps (Abs, App (Var "f", Var "x"), Zero), NatToReal (S (S Z)))))

let test_set_eq : exp =
  let p = RealIneq (Lte, Var "x", One) (* x ≤ 1 *)
  and q = Or (RealIneq (Lt, Var "x", One), RealIneq (Eq, Var "x", One)) (* x < 1 ∨ x = 1 *)  in
  let f = Lam ("x", p, q) (* Proof: x ≤ 1 → x < 1 ∨ x = 1 *)
  and g = Lam ("x", q, p) (* Proof: x < 1 ∨ x = 1 → x ≤ 1 *) in
  Forall ("x", Real, iff_intro f g) (* Goal: ∀x. (x ≤ 1 ↔ x < 1 ∨ x = 1) *)

let test_set_eq_correct : exp =
  let s1 = Set (Lam ("x", Real, RealIneq (Lte, Var "x", One))) (* {x | x ≤ 1} *)
  and s2 = Set (Lam ("x", Real, Or (RealIneq (Lt, Var "x", One),  RealIneq (Eq, Var "x", One)))) (* {x | x < 1 ∨ x = 1} *)
  in SetEq (s1, s2)

let test_set_eq_incorrect : exp =
  let s1 = Set (Lam ("x", Real, RealIneq (Lte, Var "x", One))) (* {x | x ≤ 1} *)
  and s2 = Set (Lam ("x", Real, And (RealIneq (Lt, Var "x", One),  RealIneq (Eq, Var "x", One)))) (* {x | x < 1 ∧ x = 1} *)
  in SetEq (s1, s2)

(* suite *)

type test_error = { name : string; result : exp; expected : exp }
type test_result = (string, test_error) Result.t

let test_type env ctx (term : exp) (expected_type : exp) (name : string) : test_result =
    let inferred_type = infer env ctx term in
    if equal env ctx inferred_type expected_type then
        Result.ok name
    else (
        Result.error { name; result = inferred_type; expected = expected_type }
    )

let test_term env ctx (term : exp) (expected_type : exp) (name : string) : test_result =
    let normalized_term = normalize env ctx term in
    if equal env ctx normalized_term expected_type then
        Result.ok name
    else (
        Result.error { name; result = normalized_term; expected = expected_type }
    )

let test_print_result (result : test_result) : unit =
  match result with
  | Result.Ok name     -> Printf.printf "Test %s : OK\n" name
  | Result.Error error -> Printf.printf "\x1b[31mTest %s : ERROR | expected: %s, got: %s\x1b[0m\n" error.name (string_of_exp error.expected) (string_of_exp error.result)

let test_print_results (results : test_result list) : unit =
  List.iter test_print_result results;
  let ok_count = List.length (List.filter Result.is_ok results) in
  let all_count = List.length results in
  let color = if ok_count == all_count then "\x1b[32m" else "\x1b[31m" in
  Printf.printf "%s%i / %i tests passed\x1b[0m\n\n\n" color ok_count all_count

let test_z3 () : test_result list =
  (
    let ctx = (add_var ctx "x" Real) in
    let a = (interval_a_b Zero One) in
    let b = (interval_a_b One (RealOps (Plus, One, One))) in
    let c = (Intersect (a,b)) in
    let d = And (App (a, Var "x"), App (b, Var "x")) in
    let one_point = interval_a_b One One in
    (* Property 1: C = [1, 1] *)
    let prop1 = SetEq (c, one_point) in
    test_term env ctx (normalize env ctx prop1) True "C = [1, 1]" ::
    (* Property 2: D ⇔ (x = 1) *)
    let x_eq_one = RealIneq (Eq, Var "x", One) in
    let prop2 = smt_verify_iff ctx_z3 d x_eq_one in
    test_term env ctx prop2 True "D ⇔ x = 1" ::
    []
  )

let test_foundations () =
    print_endline "\n\n\x1b[1mTesting foundations\x1b[0m\n";
    let ctx = add_var ctx "f" (Forall ("x", Real, Real)) in (
      test_type env ctx integral_sig (Universe 0) "integral_sig" ::
      test_type env ctx sequence_a (Forall ("n", Nat, Real)) "sequence_a" ::
      test_type env ctx limit_a Prop "limit_a" ::
      test_type env ctx inf_a (Real) "inf_a" ::
      test_type env ctx sup_a (Real) "sup_a" ::
      test_type env ctx set_a (Set Real) "set_a" ::
      test_type env ctx universal (Set Prop) "universal set" ::
      test_type env ctx e Real "e" ::
      test_type env ctx l2_space (Forall ("f", Forall ("x", Real, Real), Prop)) "l_2 space" ::
      test_type env ctx sigma_algebra Prop "sigma_algebra" ::
      test_type env (add_var ctx "f" (Forall ("x", Real, Real))) measurable (Prop) "measurable" ::
      test_type env ctx (interval_a_b Zero One) (Set Real) "interval_[a,b]" ::
      test_type env ctx integral_term integral_sig "integral_term" ::
      test_type env ctx (lebesgue_measure Zero One) (Measure (Real, Set (Set Real))) "lebesgue_measure" ::
      test_type env ctx test_set_eq Prop "set_eq_s1_s2" ::
      test_type env ctx test_set_eq_incorrect Prop "set_eq_s1_s2_incorrect" ::
      test_term env ctx (normalize env ctx test_set_eq_incorrect) False "set_eq_s1_s2_incorrect" ::
      test_type env ctx test_set_eq_correct Prop "set_eq_s1_s2_correct" ::
      test_term env ctx (normalize env ctx test_set_eq_correct) True "set_eq_s1_s2_correct" ::
      []
    ) |> fun l -> l @ (test_z3 ())
      |> test_print_results
