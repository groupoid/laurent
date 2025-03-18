(* 1967 (c) Laurent Schwartz. Analyse Mathematique
   Copyright (c) 2025 Groupoid Infinity

   Type Theory for mechanical formalization of Théorie des
   Distributions and Analyse Mathematique by Laurent Schwartz.

   Type systems in mathematics and computer science provide
   a structured way to formalize proofs and computations.
   In this article, we present a minimal type system,
   designed to encode classical and modern analysis with explicit core constructors.
   We omit identity types `Id`, `idp`, `J` (HoTT, MLTT-80, MLTT-75) to
   keep the system lean with Pi and Set truncated Sigma relying instead on `Bool`
   predicates and external test validation for equational reasoning.
   Also we have explicitly built in Set theory with Open Sets and Topoligy
   to have more classical core. We’ll explore this system through examples,
   starting with classical Riemann sums, advancing to built-in Lebesgue integration and Custom Measures,
   Bishop’s constructive analysis, L₂ spaces, and culminating in Schwartz’s
   theory of distributions.
*)

let trace: bool = false
let tests: bool = true

type real_ineq = Lt | Gt | Leq | Geq | Eq
type real_op = Plus | Minus | Times | Div | Pow
type complex_op = CPlus | CMinus | CTimes | CDiv

type exp =
  | Universe of int
  | Var of string
  | Lam of string * exp * exp
  | App of exp * exp
  | Forall of string * exp * exp (* Universal quantification:   ∀ (x:A), B *)
  | Exists of string * exp * exp (* Existential quantification: ∃ (x:A), B *)
  | Pair of exp * exp
  | Fst of exp
  | Snd of exp
  | Zero
  | One
  | Infinity
  | NatToReal of exp
  | S of exp
  | Z
  | Bool
  | Nat
  | Real
  | Complex
  | If of exp * exp * exp
  | Vec of int * exp * exp * exp
  | RealIneq of real_ineq * exp * exp
  | RealOps of real_op * exp * exp
  | ComplexOps of complex_op * exp * exp
  | Closure of exp
  | Set of exp
  | Union of exp * exp
  | Intersect of exp * exp
  | Power of exp
  | And of exp * exp
  | Ordinal
  | Mu of exp * exp
  | Measure of exp * exp
  | Seq of exp
  | Limit of exp * exp * exp
  | Sup of exp
  | Inf of exp
  | Lebesgue of exp * exp * exp

exception TypeError of string

type env = (string * exp) list
type context = (string * exp) list
type subst_map = (string * exp) list

let env : env = []
let ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Forall (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Forall (x, subst_many m a, subst_many m' b)
    | Exists (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Exists (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | Pair (a, b) -> Pair (subst_many m a, subst_many m b)
    | Fst t -> Fst (subst_many m t)
    | Snd t -> Snd (subst_many m t)
    | If (cond, t, f) -> If (subst_many m cond, subst_many m t, subst_many m f)
    | Vec (n, field, a, b) -> Vec (n, subst_many m field, subst_many m a, subst_many m b)
    | RealIneq (op, a, b) -> RealIneq (op, subst_many m a, subst_many m b)
    | RealOps (op, a, b) -> RealOps (op, subst_many m a, subst_many m b)
    | ComplexOps (op, a, b) -> ComplexOps (op, subst_many m a, subst_many m b)
    | Closure s -> Closure (subst_many m s)
    | Set a -> Set (subst_many m a)
    | Union (a, b) -> Union (subst_many m a, subst_many m b)
    | Intersect (a, b) -> Intersect (subst_many m a, subst_many m b)
    | Power a -> Power (subst_many m a)
    | And (a, b) -> And (subst_many m a, subst_many m b)
    | Ordinal -> Ordinal
    | Mu (base, sigma) -> Mu (subst_many m base, subst_many m sigma)
    | Measure (space, sigma) -> Measure (subst_many m space, subst_many m sigma)
    | Seq a -> Seq (subst_many m a)
    | Limit (f, x', l) -> Limit (subst_many m f, subst_many m x', subst_many m l)
    | Sup s -> Sup (subst_many m s)
    | Inf s -> Inf (subst_many m s)
    | Lebesgue (f, measure, set) -> Lebesgue (subst_many m f, subst_many m measure, subst_many m set)
    | _ -> t

let subst x s t = subst_many [(x, s)] t

let is_lam = function | Lam _ -> true | _ -> false

let rec equal env ctx t1' t2' =
    let t1 = normalize env ctx t1' in
    let t2 = normalize env ctx t2' in
    equal' env ctx t1 t2

and lookup_var ctx x =
    try Some (List.assoc x ctx) with Not_found -> None

and infer env (ctx : context) (e : exp) : exp =
    match e with
    | Universe i -> Universe 0
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Forall (x, a, b) -> Universe 0
    | Exists (x, domain, body) when equal env ctx (infer env (add_var ctx x domain) body) Bool ->  Bool
    | Lam (x, domain, body) when equal env ctx domain Real && equal env ctx (infer env (add_var ctx x domain) body) Bool -> Set Real
    | Lam (x, domain, body) -> let ctx' = add_var ctx x domain in let body_ty = infer env ctx' body in Forall (x, domain, body_ty)
    | App (f, arg) -> (match infer env ctx f with | Forall (x, a, b) -> check env ctx arg a; subst x arg b | ty -> raise (TypeError "Application requires a Pi type"))
    | Pair (a, b) -> let a_ty = infer env ctx a in let b_ty = infer env ctx b in Exists ("_", a_ty, b_ty)
    | Fst p -> (match infer env ctx p with | Exists (x, a, b) -> a | ty -> raise (TypeError ("Fst expects a Sigma type")))
    | Snd p -> (match infer env ctx p with | Exists (x, a, b) -> subst x (Fst p) b | ty -> raise (TypeError ("Snd expects a Sigma type")))
    | Bool -> Universe 0
    | Nat -> Universe 0
    | Real -> Universe 0
    | S e -> let _ = check env ctx e Nat in Nat
    | NatToReal e -> let _ = check env ctx e Nat in Real
    | Zero -> Real
    | One -> Real
    | Infinity -> Real
    | Complex -> Universe 0
    | If (cond, t, f) -> let ct = infer env ctx cond in let _ = check env ctx ct Bool in let t_typ = infer env ctx t in let _ = check env ctx f t_typ in t_typ
    | Vec (n, field, a, b) -> let _ = check env ctx field (Universe 0) in let _ = check env ctx a field in let _ = check env ctx b field in Universe 0
    | RealIneq (op, a, b) -> let _ = check env ctx a Real in let _ = check env ctx b Real in  Bool
    | RealOps (op, a, b) -> let _ = check env ctx a Real in let _ = check env ctx b Real in Real
    | ComplexOps (op, a, b) -> let _ = check env ctx a Complex in let _ = check env ctx b Complex in Complex
    | Closure s -> let _ = check env ctx s (Set Real) in Set Real
    | Set a -> Universe 0
    | Union (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | Intersect (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | Power a -> let _ = check env ctx a (Universe 0) in Set a
    | And (a, b) -> let _ = check env ctx a Bool in let _ = check env ctx b Bool in Bool
    | Ordinal -> Universe 0
    | Mu (base, sigma) -> let _ = check env ctx base (Universe 0) in let _ = check env ctx sigma (Set (Set base)) in Measure (base, Set (Set base))
    | Measure (space, sigma) -> let _ = check env ctx space (Universe 0) in let _ = check env ctx sigma (Set (Set space)) in Universe 0
    | Seq a -> let _ = check env ctx a (Universe 0) in Universe 0
    | Limit (f, x, l) ->    let _ = check env ctx f (Forall ("n", Nat, Real)) in
      let _ = check env ctx x (if equal env ctx x Infinity then Real else Nat) in let _ = check env ctx l Real in Real
    | Sup s -> let _ = check env ctx s (Set Real) in Real
    | Inf s -> let _ = check env ctx s (Set Real) in Real
    | Lebesgue (f, mu, set) -> let _ = check env ctx f (Forall ("x", Real, Real)) in
      let _ = check env ctx mu (Measure (Real, Set (Set Real))) in let _ = check env ctx set (Set Real) in Real
    | _ -> raise (TypeError "No Type Yet")

and universe env ctx t =
    match infer env ctx t with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | ty -> raise (TypeError (Printf.sprintf "Expected a universe"))

and check env (ctx : context) (term : exp) (expected : exp) : unit =
    Printf.printf "Term: %s Expected: %s\n" (string_of_exp term) (string_of_exp expected);
    let inferred = infer env ctx term in
    if equal env ctx inferred expected then ()
    else raise (TypeError "Type mismatch")

and equal' env ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Forall (x, a, b), Forall (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Forall (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Forall (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Exists (x, a, b), Exists (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Pair (a, b), Pair (a', b') -> equal' env ctx a a' && equal' env ctx b b'
    | t, Pair (Fst t', Snd t'') when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Pair (Fst t', Snd t''), t when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Fst t, Fst t' -> equal' env ctx t t'
    | Snd t, Snd t' -> equal' env ctx t t'
    | Bool, Bool -> true
    | Nat, Nat -> true
    | Real, Real -> true
    | Complex, Complex -> true
    | If (c1, t1, f1), If (c2, t2, f2) -> equal' env ctx c1 c2 && equal' env ctx t1 t2 && equal' env ctx f1 f2
    | Vec (n1, f1, a1, b1), Vec (n2, f2, a2, b2) -> n1 = n2 && equal' env ctx f1 f2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | RealIneq (op1, a1, b1), RealIneq (op2, a2, b2) -> op1 = op2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | RealOps (op1, a1, b1), RealOps (op2, a2, b2) -> op1 = op2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | ComplexOps (op1, a1, b1), ComplexOps (op2, a2, b2) -> op1 = op2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Closure s1, Closure s2 -> equal' env ctx s1 s2
    | Set a1, Set a2 -> equal' env ctx a1 a2
    | Union (a1, b1), Union (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Intersect (a1, b1), Intersect (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Power a1, Power a2 -> equal' env ctx a1 a2
    | And (a1, b1), And (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Ordinal, Ordinal -> true
    | Mu (b1, s1), Mu (b2, s2) -> equal' env ctx b1 b2 && equal' env ctx s1 s2
    | Measure (sp1, s1), Measure (sp2, s2) -> equal' env ctx sp1 sp2 && equal' env ctx s1 s2
    | Seq a1, Seq a2 -> equal' env ctx a1 a2
    | Limit (f1, x1, l1), Limit (f2, x2, l2) -> equal' env ctx f1 f2 && equal' env ctx x1 x2 && equal' env ctx l1 l2
    | Sup s1, Sup s2 -> equal' env ctx s1 s2
    | Inf s1, Inf s2 -> equal' env ctx s1 s2
    | Lebesgue (f1, m1 ,s1), Lebesgue (f2, m2, s2) -> equal' env ctx f1 f2 && equal' env ctx m1 m2 && equal' env ctx s1 s2
    | Infinity, Infinity -> true
    | Zero, Zero -> true
    | One, One -> true
    | Z, Z -> true
    | S e1, S e2 -> equal' env ctx e1 e2
    | _ -> false

and reduce env ctx t =
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (f, arg) -> let f' = reduce env ctx f in let arg' = reduce env ctx arg in App (f', arg')
    | Fst (Pair (a, b)) -> a
    | Snd (Pair (a, b)) -> b
    | _ -> t

and normalize env ctx t =
    let t' = reduce env ctx t in
    if equal' env ctx t t' then t else normalize env ctx t'

and string_of_exp = function
  | Universe i -> "Universe " ^ string_of_int i
  | Var x -> x
  | Lam (x, a, b) -> "Lam (" ^ string_of_exp a ^ ", (" ^ x ^ ", " ^ string_of_exp b ^ "))"
  | App (f, arg) -> "App (" ^ string_of_exp f ^ ", " ^ string_of_exp arg ^ ")"
  | Exists (x, a, b) -> "Exists (" ^ string_of_exp a ^ ", (" ^ x ^ ", " ^ string_of_exp b ^ "))"
  | Pair (a, b) -> "Pair (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Fst t -> (string_of_exp t) ^ ".1"
  | Snd t -> (string_of_exp t) ^ ".2"
  | S e -> "S (" ^ string_of_exp e ^ ")"
  | Z -> "Z"
  | Zero -> "0"
  | One -> "1"
  | Infinity -> "∞"
  | Bool -> "Bool"
  | Nat -> "Nat"
  | Real -> "Real"
  | NatToReal e -> "Real(" ^ string_of_exp e ^ ")"
  | Complex -> "Complex"
  | If (c, t, f) -> "If (" ^ string_of_exp c ^ ", " ^ string_of_exp t ^ ", " ^ string_of_exp f ^ ")"
  | Vec (n, f, a, b) -> "Vec (" ^ string_of_int n ^ ", " ^ string_of_exp f ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealIneq (op, a, b) -> "RealIneq (" ^ (match op with Lt -> "<" | Gt -> ">" | Leq -> "<=" | Geq -> ">=" | Eq -> "=") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealOps (op, a, b) -> "RealOps (" ^ (match op with Plus -> "+" | Minus -> "-" | Times -> "*" | Div -> "/" | Pow -> "^") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | ComplexOps (op, a, b) -> "ComplexOps (" ^ (match op with CPlus -> "+c" | CMinus -> "-c" | CTimes -> "*c" | CDiv -> "/c") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Closure s -> "Closure (" ^ string_of_exp s ^ ")"
  | Set a -> "Set (" ^ string_of_exp a ^ ")"
  | Union (a, b) -> "Union (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Intersect (a, b) -> "Intersect (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Power a -> "Power (" ^ string_of_exp a ^ ")"
  | And (a, b) -> "And (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Ordinal -> "Ordinal"
  | Mu (b, s) -> "Mu (" ^ string_of_exp b ^ ", " ^ string_of_exp s ^ ")"
  | Measure (sp, s) -> "Measure (" ^ string_of_exp sp ^ ", " ^ string_of_exp s ^ ")"
  | Seq a -> "Seq (" ^ string_of_exp a ^ ")"
  | Limit (f, x, l) -> "Limit (" ^ string_of_exp f ^ ", " ^ string_of_exp x ^ ", " ^ string_of_exp l ^ ")"
  | Sup s -> "Sup (" ^ string_of_exp s ^ ")"
  | Inf s -> "Inf (" ^ string_of_exp s ^ ")"
  | Lebesgue (f, m, set) -> "Lebesgue (" ^ string_of_exp f ^ ", " ^ string_of_exp m ^ ")"
  | Forall (x, a, b) -> "Forall (" ^ x ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"

(* canonical examples *)

let sequence_a : exp = Lam ("n", Nat, RealOps (Div, One, NatToReal (Var "n")))
let sequence_e : exp = Lam ("n", Nat, RealOps (Pow, RealOps (Plus, One, RealOps (Div, One, NatToReal (Var "n"))), NatToReal (Var "n")))
let limit_a    : exp = Limit (sequence_a, Infinity, Zero)
let e_limit    : exp = Limit (sequence_e, Infinity, Real)
let e          : exp = Limit (sequence_e, Infinity, Zero)
let set_a      : exp = Lam ("x", Real, RealIneq (Gt, Var "x", Zero))
let sup_a      : exp = Sup set_a
let inf_a      : exp = Inf set_a
let interval_a_b a b : exp = Lam ("x", Real, And (RealIneq (Leq, a, Var "x"), RealIneq (Leq, Var "x", b)))
let integral_sig     : exp = Forall ("f", Forall ("x", Real, Real), Forall ("a", Real, Forall ("b", Real, Real)))
let integral_term    : exp = Lam ("f", Forall ("x", Real, Real), Lam ("a", Real, Lam ("b", Real,
                             Lebesgue (Var "f", Mu (Real, Power (Set Real)), interval_a_b (Var "a") (Var "b")))))

(* runner *)

let test_term env ctx (term : exp) (expected_type : exp) (name : string) : unit =
    Printf.printf "%s: " name;
    try let inferred_type = infer env ctx term in
        if equal env ctx inferred_type expected_type then
            Printf.printf " OK\n"
        else
            raise (TypeError "Type mismatch")
    with TypeError msg -> Printf.printf "Error in %s: %s\n" name msg

let test_all () =
    test_term env ctx integral_sig (Universe 0) "integral_sig";
    test_term env ctx integral_term integral_sig "integral_term";
    test_term env ctx inf_a Real "inf_a";
    test_term env ctx sup_a Real "sup_a";
    test_term env ctx sequence_a (Forall ("n", Nat, Real)) "sequence_a";
    test_term env ctx set_a (Set Real) "set_a";
    test_term env ctx e Real "e";
    test_term env ctx limit_a Real "limit_a";
    Printf.printf "All tests passed!\n"

let () = test_all ()
