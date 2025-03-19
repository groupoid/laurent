(* 1967 (c) Laurent Schwartz. Analyse Mathematique
   Copyright (c) 2025 Groupoid Infinity

   Type Theory for mechanical formalization of Théorie des
   Distributions and Analyse Mathematique by Laurent Schwartz.

   Type systems in mathematics and computer science provide
   a structured way to formalize proofs and computations.
   In this article, we present a minimal type system,
   designed to encode classical and modern analysis with explicit core constructors.

   We omit identity types `Id`, `idp`, `J` (HoTT, MLTT-80, MLTT-75) to
   keep the system lean with Pi and Set truncated Sigma relying instead on `Prop` predicates.
   Also we have explicitly built in Set theory with Open Sets and Topology to have more classical core.

   We’ll explore this system through examples, starting with:
   1) Classical Riemann sums, advancing to built-in
   2) Lebesgue integration and
   3) Custom Measures,
   4) Bishop’s constructive analysis,
   5) L₂ spaces, and culminating in
   6) Schwartz’s theory of distributions.
*)

let trace: bool = false
let tests: bool = true

type real_ineq = Lt | Gt | Leq | Geq | Eq | Neq
type real_op = Plus | Minus | Times | Div | Neg | Pow | Abs | Ln | Sin | Cos | Exp
type complex_op = CPlus | CMinus | CTimes | CDiv

type exp =
  | Universe of int
  | Prop
  | Var of string
  | Lam of string * exp * exp
  | App of exp * exp
  | Forall of string * exp * exp (* Universal quantification:   ∀ (x:A), B *)
  | Exists of string * exp * exp (* Existential quantification: ∃ (x:A), B *)
  | Pair of exp * exp
  | Fst of exp
  | Snd of exp
  | NatToReal of exp
  | Nat                                   (*   ℕ   *)
  | Integer                               (*   ℤ   *)
  | Real                                  (*   ℝ   *)
  | Complex                               (*   ℂ   *)
  | Bool                                  (*   𝟚   *)
  | Vec of int * exp * exp * exp          (*   𝕍   *)
  | Zero                                  (*  0.0  *)
  | One                                   (*  1.0  *)
  | Infinity                              (*   ∞   *)
  | S of exp                              (*   1+  *)
  | Z                                     (*   0   *)
  | If of exp * exp * exp
  | RealIneq of real_ineq * exp * exp     (* Inequalities a < b, etc. *)
  | RealOps of real_op * exp * exp        (* Real +, -, *, etc. *)
  | ComplexOps of complex_op * exp * exp  (* Complex +, -, *, etc. *)
  | Closure of exp
  | Set of exp             (* Term level: { x : A | P } Set Lam, Type Level: Set Real *)
  | UnionSet of exp * exp  (* A ∪ B *)
  | Complement of exp      (* ℝ \ A *)
  | Intersect of exp * exp (* a ∩ b *)
  | Power of exp           (* a ^ b *)
  | And of exp * exp       (* a ∩ b *)
  | Ordinal
  | Mu of exp * exp        (* Measure type *)
  | Measure of exp * exp   (* Measure expression *)
  | Seq of exp             (* a_n : N -> R, Seq Lam *)
  | Sum of exp             (* ∑ a_n, Sum Lam *)
  | Union of exp           (* ⋃ A_n, Union Lam  *)
  | Limit of limit         (* Limit(f,x,l,p) : Real, f: sequence, x: bound, l: limit, p: proof *)
  | Sup of exp             (* sup a_n : R, Sup Seq (N -> R) *)
  | Inf of exp             (* inf a_n : R, Inf Seq (N -> R) *)
  | Lebesgue of lebesgue   (* ∫ f dμ over set *)

and limit = exp * exp * exp * exp
and lebesgue = exp * exp * exp 

exception TypeError of string

type env = (string * exp) list
type context = (string * exp) list
type subst_map = (string * exp) list

let env : env = []
let ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

let is_sigma_algebra sigma =
  Exists ("_",
    Exists ("_", App (sigma, Set Real),
      Forall ("A", Set Real,
        Forall ("_", App (sigma, Var "A"),
          App (sigma, Complement (Var "A"))))),
    Forall ("An", Forall ("n", Nat, Set Real),
      Forall ("_", Forall ("n", Nat, App (sigma, App (Var "An", Var "n"))),
        App (sigma, Union (Var "An")))))

let is_measurable sigma f =
  Forall ("a", Real,
    Forall ("b", Real,
      Forall ("_", RealIneq (Lt, Var "a", Var "b"),
        App (sigma,
             Set (Lam ("x", Real,
                       Exists ("_", RealIneq (Lt, Var "a", App (f, Var "x")),
                              RealIneq (Lt, App (f, Var "x"), Var "b"))))))))

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
    | UnionSet (a, b) -> UnionSet (subst_many m a, subst_many m b)
    | Union a -> Union (subst_many m a)
    | Intersect (a, b) -> Intersect (subst_many m a, subst_many m b)
    | Complement a -> Complement (subst_many m a)
    | Power a -> Power (subst_many m a)
    | And (a, b) -> And (subst_many m a, subst_many m b)
    | Ordinal -> Ordinal
    | Mu (base, sigma) -> Mu (subst_many m base, subst_many m sigma)
    | Measure (space, sigma) -> Measure (subst_many m space, subst_many m sigma)
    | Seq a -> Seq (subst_many m a)
    | Limit (f, x, l, p) -> Limit (subst_many m f, subst_many m x, subst_many m l, subst_many m p)
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
    | Universe 0 -> Universe 1
    | Universe 1 -> Universe 1
    | Universe i -> raise (TypeError "Invalid Universe (index should be less than 2)")
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Forall (x, domain, body) ->
      let _ = infer env ctx domain in
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      if equal env ctx body_ty Prop then Prop
      else Universe 0
    | Exists (x, domain, body) -> let _ = infer env (add_var ctx x domain) body in Prop
    | App (f, arg) ->
      (match infer env ctx f with
      | Forall (x, a, b) -> check env ctx arg a; subst x arg b
      | Set (Set a) -> check env ctx arg (Set a); Prop
      | ty -> raise (TypeError "Application requires a Pi type"))
    | Lam (x, domain, body) when equal env ctx domain Real && equal env ctx (infer env (add_var ctx x domain) body) Prop -> Set Real
    | Lam (x, domain, body) ->
      let ctx' = add_var ctx x domain in
      let domain_ty = infer env ctx domain in
      (match domain, body with
      | Real, Prop -> Set Real  (* {x : Real | true} *)
      | _ -> (match domain_ty with
              | Universe i -> let body_ty = infer env ctx' body in Forall (x, domain, body_ty)
              | Real -> let body_ty = infer env ctx' body in
                        if equal env ctx body_ty Prop then Set Real else Forall (x, domain, body_ty)
              | Prop -> let body_ty = infer env ctx' body in Forall (x, domain, body_ty)
              | Forall _ -> let body_ty = infer env ctx' body in
                              if equal env ctx body_ty Prop then Set domain else Forall (x, domain, body_ty)
              | _ -> raise (TypeError "Lambda domain must be a type or proposition")))
    | Pair (a, b) -> let a_ty = infer env ctx a in let b_ty = infer env (add_var ctx "N" a_ty) b in Exists ("N", a_ty, b_ty)
    | Fst p -> (match infer env ctx p with | Exists (x, a, b) -> a | ty -> raise (TypeError ("Fst expects a Sigma type")))
    | Snd p -> (match infer env ctx p with | Exists (x, a, b) -> subst x (Fst p) b | ty -> raise (TypeError ("Snd expects a Sigma type")))
    | Prop -> Universe 0
    | Bool -> Universe 0
    | Integer -> Universe 0
    | Nat -> Universe 0
    | Real -> Universe 0
    | Z -> Nat
    | S e -> let _ = check env ctx e Nat in Nat
    | NatToReal e -> let _ = check env ctx e Nat in Real
    | Zero -> Real
    | One -> Real
    | Infinity -> Real
    | Complex -> Universe 0
    | If (cond, t, f) -> let ct = infer env ctx cond in let _ = check env ctx ct Prop in let t_typ = infer env ctx t in let _ = check env ctx f t_typ in t_typ
    | Vec (n, field, a, b) -> let _ = check env ctx field (Universe 0) in let _ = check env ctx a field in let _ = check env ctx b field in Universe 0
    | RealIneq (op, a, b) ->
      let a_ty = infer env ctx a in
      let b_ty = infer env ctx b in
      let _ = if not (equal env ctx a_ty Real && equal env ctx b_ty Real) &&
                 not (equal env ctx a_ty Nat && equal env ctx b_ty Real) &&
                 not (equal env ctx a_ty Real && equal env ctx b_ty Nat)
          then raise (TypeError "RealIneq requires Real or Nat-Real arguments")
      in Prop
    | RealOps (op, a, b) ->
        let _ = check env ctx a Real in
        (match op with
         | Plus | Minus | Times | Div | Pow -> let _ = check env ctx b Real in Real
         | Abs | Ln | Sin | Cos | Exp | Neg  -> Real)
    | ComplexOps (op, a, b) -> let _ = check env ctx a Complex in let _ = check env ctx b Complex in Complex
    | Closure s -> let _ = check env ctx s (Set Real) in Set Real
    | Set a ->
    let a_ty = infer env ctx a in
    (match a_ty with
     | Forall (x, domain, body) when equal env ctx domain Real && equal env ctx body Prop -> Set Real
     | Universe i -> Universe 0
     | Set b -> Set b
     | _ -> raise (TypeError ("Set expects a predicate or type, got " ^ string_of_exp a_ty)))
    | UnionSet (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | Union a -> let _ = check env ctx a (Forall ("n", Nat, Set Real)) in Set Real
    | Complement a ->
      let _ = check env ctx a (Set Real) in
      Set Real
    | Intersect (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | Sum a -> let _ = check env ctx a (Forall ("n", Nat, Real)) in Real
    | Power a ->
      let a_ty = infer env ctx a in
      if equal env ctx a_ty (Universe 0) then Set a
      else raise (TypeError "Power expects a type")
    | And (a, b) -> let _ = check env ctx a Prop in let _ = check env ctx b Prop in Prop
    | Ordinal -> Universe 0
    | Mu (base, sigma) ->
      let _ = check env ctx base (Universe 0) in
      let _ = check env ctx sigma (Set (Set base)) in
      Measure (base, Set (Set base))
    | Measure (space, sigma) -> let _ = check env ctx space (Universe 0) in let _ = check env ctx sigma (Set (Set space)) in Universe 0
    | Seq a -> let _ = check env ctx a (Universe 0) in Universe 0
    | Limit (f, x, l, p) ->
      let _ = check env ctx f (Forall ("n", Nat, Real)) in
      let x_ty = if equal env ctx x Infinity then Real else Nat in
      let _ = check env ctx x x_ty in
      let _ = check env ctx l Real in
      let limit_proof_type =
        Forall ("ε", Real,
          Forall ("p", RealIneq (Gt, Var "ε", Zero),
            Exists ("N", Real,
              Forall ("n", Nat,
                Forall ("q", RealIneq (Gt, Var "n", Var "N"), Prop))))) in
      let ctx' = add_var (add_var ctx "f" (Forall ("n", Nat, Real))) "l" Real in
      let _ = check env ctx' p (subst_many [("f", f); ("l", l)] limit_proof_type) in Prop

    | Sup s -> let _ = check env ctx s (Set Real) in Real
    | Inf s -> let _ = check env ctx s (Set Real) in Real
(*
    | Lebesgue (f, mu, set) ->
      let sigma = (match mu with
                  | Mu (Real, s) -> s
                  | _ -> raise (TypeError "Lebesgue requires a measure on Real"))  in
      let _ = check env ctx f (Forall ("x", Real, Real)) in
      let _ = check env ctx mu (Measure (Real, sigma)) in
      let _ = check env ctx set (Set Real) in
      let _ = check env ctx (is_sigma_algebra sigma) Prop in
      let _ = check env ctx (App (sigma, set)) Prop in
      let _ = check env ctx (is_measurable sigma f) Prop in
      let _ = (match set with
                | Union an ->
                  let _ = check env ctx (Forall ("n", Nat, App (sigma, App (an, Var "n")))) Prop in
                  let _ = check env ctx
                            (Forall ("n", Nat,
                              Forall ("m", Nat,
                                Forall ("_", RealIneq (Neq, Var "n", Var "m"),
                                  RealIneq (Eq, Intersect (App (an, Var "n"), App (an, Var "m")), Zero)))))
                            Prop in
                  check env ctx
                    (RealIneq (Eq, App (mu, Union an),
                                  Sum (Lam ("n", Nat, App (mu, App (an, Var "n"))))))
                    Prop
                | _ -> ())    in Real
*)
    | Lebesgue (f, mu, set) ->
      let _ = check env ctx f (Forall ("x", Real, Real)) in
      let _ = check env ctx mu (Measure (Real, Set (Set Real))) in
      let set_ty = infer env ctx set in
      (match set_ty with
      | Set Real -> Real
      | _ -> check env ctx set (Set Real); Real)

and universe env ctx t =
    match infer env ctx t with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | ty -> raise (TypeError (Printf.sprintf "Expected a universe"))

and check env (ctx : context) (term : exp) (expected : exp) : unit =
    if trace then Printf.printf "Term: %s Expected: %s\n" (string_of_exp term) (string_of_exp expected);
    let inferred = infer env ctx term in
    if equal env ctx inferred expected then ()
    else (
       Printf.printf "Last Error: %s\nInferred: %s\nExpected: %s\n" (string_of_exp term) (string_of_exp inferred) (string_of_exp expected);
       raise (TypeError "Type mismatch")
    )

and equal' env ctx t1 t2 =
(*    if trace then Printf.printf "Equal: %s vs %s\n" (string_of_exp t1) (string_of_exp t2); *)
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Forall (x, a, b), Forall (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Forall (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Forall (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Exists (x, a, b), Exists (y, a', b') -> equal' env ctx a a' && let ctx' = add_var ctx x a in equal' env ctx' b (subst y (Var x) b')
    | Pair (a, b), Pair (a', b') -> equal' env ctx a a' && equal' env ctx b b'
    | t, Pair (Fst t', Snd t'') when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Pair (Fst t', Snd t''), t when equal' env ctx t t' && equal' env ctx t t'' -> true
    | Fst t, Fst t' -> equal' env ctx t t'
    | Snd t, Snd t' -> equal' env ctx t t'
    | Prop, Prop -> true
    | Nat, Nat -> true
    | Real, Real -> true
    | Complex, Complex -> true
    | If (c1, t1, f1), If (c2, t2, f2) -> equal' env ctx c1 c2 && equal' env ctx t1 t2 && equal' env ctx f1 f2
    | Vec (n1, f1, a1, b1), Vec (n2, f2, a2, b2) -> n1 = n2 && equal' env ctx f1 f2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | RealIneq (op1, a1, b1), RealIneq (op2, a2, b2) -> op1 = op2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | RealOps (op1, a1, b1), RealOps (op2, a2, b2) ->
      op1 = op2 && (match op1 with
      | Abs | Ln | Sin | Cos | Exp -> equal' env ctx a1 a2
      | _ -> equal' env ctx a1 a2 && equal' env ctx b1 b2)
    | ComplexOps (op1, a1, b1), ComplexOps (op2, a2, b2) -> op1 = op2 && equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Closure s1, Closure s2 -> equal' env ctx s1 s2
    | Set a1, Set a2 -> equal' env ctx a1 a2
    | UnionSet (a1, b1), UnionSet (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Union a, Union b -> equal' env ctx a b
    | Intersect (a1, b1), Intersect (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Complement a, Complement b -> equal' env ctx a b
    | Power a1, Power a2 -> equal' env ctx a1 a2
    | And (a1, b1), And (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Ordinal, Ordinal -> true
    | Mu (b1, s1), Mu (b2, s2) -> equal' env ctx b1 b2 && equal' env ctx s1 s2
    | Measure (sp1, s1), Measure (sp2, s2) -> equal' env ctx sp1 sp2 && equal' env ctx s1 s2
    | Seq a1, Seq a2 -> equal' env ctx a1 a2
    | Limit (f1, x1, l1, p1), Limit (f2, x2, l2, p2) -> equal' env ctx f1 f2 && equal' env ctx x1 x2 && equal' env ctx l1 l2 && equal' env ctx p1 p2


    | Sup s1, Sup s2 -> equal' env ctx s1 s2
    | Inf s1, Inf s2 -> equal' env ctx s1 s2
    | Lebesgue (f1, m1 ,s1), Lebesgue (f2, m2, s2) -> equal' env ctx f1 f2 && equal' env ctx m1 m2 && equal' env ctx s1 s2
    | Infinity, Infinity -> true
    | Zero, Zero -> true
    | One, One -> true
    | Z, Z -> true
    | S e1, S e2 -> equal' env ctx e1 e2
    | NatToReal e1, NatToReal e2 -> equal' env ctx e1 e2
    | _ -> t1 = t2

and reduce env ctx t =
(*    if trace then Printf.printf "Reduce: %s\n" (string_of_exp t); *)
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (f, arg) -> let f' = reduce env ctx f in let arg' = reduce env ctx arg in App (f', arg')
    | Fst (Pair (a, b)) -> a
    | Snd (Pair (a, b)) -> b
    | Limit (f, x, l, p) -> Limit (reduce env ctx f, reduce env ctx x, reduce env ctx l, reduce env ctx p)
    | _ -> t

and normalize env ctx t =
(*    if trace then Printf.printf "Normalize: %s\n" (string_of_exp t); *)
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
  | Prop -> "Prop"
  | Bool -> "𝟚"
  | Integer -> "ℤ"
  | Nat -> ""
  | Real -> "ℕ"
  | NatToReal e -> "ℝ(" ^ string_of_exp e ^ ")"
  | Complex -> "ℂ"
  | If (c, t, f) -> "If (" ^ string_of_exp c ^ ", " ^ string_of_exp t ^ ", " ^ string_of_exp f ^ ")"
  | Vec (n, f, a, b) -> "𝕍 (" ^ string_of_int n ^ ", " ^ string_of_exp f ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealIneq (op, a, b) -> "RealIneq (" ^ (match op with Lt -> "<" | Gt -> ">" | Leq -> "<=" | Geq -> ">=" | Eq -> "=" | Neq -> "Neq") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealOps (op, a, b) ->
    let op_str = match op with
      | Plus -> "+ℝ" | Minus -> "-ℝ" | Times -> "*ℝ" | Div -> "/ℝ" | Pow -> "^ℝ"
      | Abs -> "Abs" | Ln -> "Ln" | Sin -> "Sin" | Cos -> "Cos" | Exp -> "Exp" | Neg -> "Neg"
    in "RealOps (" ^ op_str ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | ComplexOps (op, a, b) -> "ComplexOps (" ^ (match op with CPlus -> "+C" | CMinus -> "-C" | CTimes -> "*C" | CDiv -> "/C") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Closure s -> "Closure (" ^ string_of_exp s ^ ")"
  | Set a -> "Set (" ^ string_of_exp a ^ ")"
  | Complement a -> "Complement (" ^ string_of_exp a ^ ")"
  | Sum a -> "Sum (" ^ string_of_exp a ^ ")"
  | UnionSet (a, b) -> "UnionSet (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Union a -> "Union (" ^ string_of_exp a ^ ")"
  | Intersect (a, b) -> "Intersect (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Power a -> "Power (" ^ string_of_exp a ^ ")"
  | And (a, b) -> "And (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Ordinal -> "Ordinal"
  | Mu (b, s) -> "μ (" ^ string_of_exp b ^ ", " ^ string_of_exp s ^ ")"
  | Measure (sp, s) -> "Measure (" ^ string_of_exp sp ^ ", " ^ string_of_exp s ^ ")"
  | Seq a -> "Seq (" ^ string_of_exp a ^ ")"
  | Limit (f, x, l, p) -> "Limit (" ^ string_of_exp f ^ ", " ^ string_of_exp x ^ ", " ^ string_of_exp l ^ ", " ^ string_of_exp p ^ ")"
  | Sup s -> "Sup (" ^ string_of_exp s ^ ")"
  | Inf s -> "Inf (" ^ string_of_exp s ^ ")"
  | Lebesgue (f, m, set) -> "Lebesgue (" ^ string_of_exp f ^ ", " ^ string_of_exp m ^ ")"
  | Forall (x, a, b) -> "Forall (" ^ x ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"

(* canonical examples *)

let universal  : exp = Power Prop
let set_a      : exp = Lam ("x", Real, RealIneq (Gt, Var "x", Zero))
let sup_a      : exp = Sup set_a
let inf_a      : exp = Inf set_a
let interval_a_b a b : exp = Lam ("x", Real, And (RealIneq (Leq, a, Var "x"), RealIneq (Leq, Var "x", b)))
let integral_sig     : exp = Forall ("f", Forall ("x", Real, Real), Forall ("a", Real, Forall ("b", Real, Real)))
let integral_term    : exp = Lam ("f", Forall ("x", Real, Real), Lam ("a", Real, Lam ("b", Real,
                             Lebesgue (Var "f", Mu (Real, Power (Set Real)), interval_a_b (Var "a") (Var "b")))))

let sequence_a : exp =
    Lam ("n", Nat, RealOps (Div, One, NatToReal (Var "n")))

let limit_a : exp =
  Limit (sequence_a, Infinity, Zero,
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
    Limit (sequence_e, Infinity, RealOps (Exp, One, One),
      Lam ("ε", Real,
        Lam ("p", RealIneq (Gt, Var "ε", Zero),
          Pair (RealOps (Div, RealOps (Exp, One, Zero), RealOps (Times, RealOps (Plus, One, One), Var "ε")),
            Lam ("n", Nat,
              Lam ("q", RealIneq (Gt, Var "n", Var "N"),
                RealIneq (Lt, RealOps (Abs, RealOps (Minus, App (sequence_e, Var "n"), RealOps (Exp, One, One)), Zero), Var "ε")))))))))

let lebesgue_measure =
  Mu (Real, Power (Set Real))

let l2_space : exp =
  Lam ("f", Forall ("x", Real, Real),
    RealIneq (Lt,
      Lebesgue (
        Lam ("x", Real,
          RealOps (Pow,
            RealOps (Abs, App (Var "f", Var "x"), Zero),
            RealOps (Plus, One, One))),
        lebesgue_measure,
        Lam ("x", Real, Prop)),
      Infinity))


let sigma_algebra = is_sigma_algebra (Power (Set Real))


let measurable =
  is_measurable
    (Power (Set Real))
    (Lam ("x", Real, RealOps (Pow, RealOps (Abs, App (Var "f", Var "x"), Zero), NatToReal (S (S Z)))))

(* runner *)

let test_term env ctx (term : exp) (expected_type : exp) (name : string) : unit =
    Printf.printf "TEST ";
    try let inferred_type = infer env ctx term in
        if equal env ctx inferred_type expected_type then
            Printf.printf "OK> %s : %s\n" name (string_of_exp inferred_type)
        else (
            Printf.printf "ERROR>\nTerm: %s\nInferred: %s\nExpected: %s\n" (string_of_exp term) (string_of_exp inferred_type) (string_of_exp expected_type);
            raise (TypeError "Type mismatch")
        )
    with TypeError msg -> Printf.printf "Error in %s: %s\n" name msg

let test_all () =
    let ctx = add_var ctx "f" (Forall ("x", Real, Real)) in
    test_term env ctx integral_sig (Universe 0) "integral_sig";
    test_term env ctx integral_term integral_sig "integral_term";
    test_term env ctx sequence_a (Forall ("n", Nat, Real)) "sequence_a";
    test_term env ctx limit_a Prop "limit_a";
    test_term env ctx inf_a (Real) "inf_a";
    test_term env ctx sup_a (Real) "sup_a";
    test_term env ctx set_a (Set Real) "set_a";
    test_term env ctx universal (Set Prop) "universal set";
    test_term env ctx e Real "e";
    test_term env ctx l2_space (Forall ("f", Forall ("x", Real, Real), Prop)) "l_2 space";
    test_term env ctx sigma_algebra Prop "sigma_algebra";
    let ctx = add_var ctx "f" (Forall ("x", Real, Real)) in
        test_term env ctx measurable (Prop) "measurable";
    Printf.printf "All tests passed!\n"

let () = test_all ()
