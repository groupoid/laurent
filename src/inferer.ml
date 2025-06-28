open Z3

(* LAURENT INNER TOPOS LANGUAGE ∮ *)

let ctx_z3 = mk_context []

let verbose: bool = false
let trace: bool = false
let tests: bool = true

type real_ineq = Lt | Gt | Lte | Gte | Eq | Neq
type real_op = Plus | Minus | Mul | Div | Neg | Pow | Abs | Ln | Sin | Cos | Exp
type complex_op = CPlus | CMinus | CMul | CDiv

type exp =                         (* MLTT-72 Vibe Check                     *)
  | Prop                           (* Prop Universe, Prop : Universe 0       *)
  | Universe of int                (* Universe 0 : Universe 1, no others     *)
  | Var of string                  (* Variable definition                    *)
  | Forall of string * exp * exp   (* Universal quantification:   ∀ (x:A), B *)
  | Lam of string * exp * exp      (* ∀-intro, Implication                   *)
  | App of exp * exp               (* ∀-elim, Modus Ponens                   *)
  | Exists of string * exp * exp   (* Existential quantification: ∃ (x:A), B *)
  | Pair of exp * exp              (* ∃-intro, existence consists of:        *)
  | Fst of exp                     (* ∃-elim-1, witness                      *)
  | Snd of exp                     (* ∃-elim-2, proof                        *)
  | NatToReal of exp               (* Carriers:                              *)
  | Bool                           (*   𝟚   *)
  | Nat                            (*   ℕ   *)
  | Integer                        (*   ℤ   *)
  | Rational                       (*   ℚ   *)
  | Real                           (*   ℝ   *)
  | Complex                        (*   ℂ   *)
  | Quaternionic                   (*   ℍ   *)
  | Octanionic                     (*   𝕆   *)
  | Vec of int * exp * exp * exp   (*   𝕍   *)
  | Zero                           (*  0.0  *)
  | One                            (*  1.0  *)
  | RealConst of float             (*  1.0  *)
  | Infinity                       (*   ∞   *)
  | S of exp                       (*   1+  *)
  | Z                              (*   0   *)
  | If of exp * exp * exp                   (* 𝟚-Eliminator : 𝟚 -> ℝ         *)
  | RealIneq of real_ineq * exp * exp       (* Inequalities a < b, etc.      *)
  | RealOps of real_op * exp * exp          (* Real +, -, *, etc.            *)
  | ComplexOps of complex_op * exp * exp    (* Complex +, -, *, etc.         *)
  | Closure of exp
  | SetEq of exp * exp      (* a = b,       a b : Set  *)
  | True                    (* True : Prop             *)
  | False                   (* False : Prop            *)
  | Set of exp              (* { x : A | P }, A : Set  *)
  | Complement of exp       (* ℝ \ A,         A : Set  *)
  | Intersect of exp * exp  (* a ∩ b,       a b : Set  *)
  | Power of exp            (* a ^ b,       a b : Set  *)
  | And of exp * exp        (* a ∩ b,       a b : Prop *)
  | Or of exp * exp         (* a ∪ b,       a b : Prop *)
  | Ordinal
  | Mu of exp * exp * exp   (* μ (base : U_0, sigma : Set (Set base), f : Set base -> base) : Measure *)
  | Measure of exp * exp    (* Measure (space : U_0, sigma : Set (Set space)) : U_0 *)
  | Seq of exp              (* a_n : N -> R, Seq Lam *)
  | Sum of exp              (* ∑ a_n, Sum Lam, inifinite sum *)
  | Union of exp            (* ⋃ A_n, Union Lam, infinite union *)
  | Limit of limit          (* Limit(f,x,l,p) : Real, f: sequence, x: bound, l: limit, p: proof *)
  | Sup of exp              (* sup a_n : R, Sup Seq (N -> R) *)
  | Inf of exp              (* inf a_n : R, Inf Seq (N -> R) *)
  | Lebesgue of lebesgue    (* ∫ f dμ over set *)

and limit = exp * exp * exp * exp
and lebesgue = exp * exp * exp

exception TypeError of string

type env = (string * exp) list
type context = (string * exp) list
type subst_map = (string * exp) list

let env : env = []
let ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

let iff (p : exp) (q : exp) : exp = Exists ("f", Forall ("x", p, q), Forall ("y", q, p))
let iff_intro (f : exp) (g : exp) : exp = Pair (f, g)

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

let rec string_of_exp = function
  | SetEq (s1, s2) -> string_of_exp s1 ^ " =s " ^ string_of_exp s2
  | True -> "True"
  | False -> "False"
  | Universe i -> "Universe " ^ string_of_int i
  | Var x -> x
  | Forall (x, a, b) -> "Forall (" ^ (x) ^ ", " ^ (string_of_exp a) ^ ", " ^ (string_of_exp b) ^ ")"
  | Exists (x, a, b) -> "Exists (" ^ (x) ^ ", " ^ (string_of_exp a) ^ ", " ^ (string_of_exp b) ^ ")"
  | Lam (x, a, b)    -> "Lam ("    ^ (x) ^ ", " ^ (string_of_exp a) ^ ", " ^ (string_of_exp b) ^ ")"
  | App (f, arg) -> "App (" ^ string_of_exp f ^ ", " ^ string_of_exp arg ^ ")"
  | Pair (a, b) -> "Pair (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Fst t -> (string_of_exp t) ^ ".1"
  | Snd t -> (string_of_exp t) ^ ".2"
  | S e -> "S " ^ string_of_exp e ^ ""
  | Z -> "Z"
  | Zero -> "0"
  | One -> "1"
  | Infinity -> "∞"
  | Prop -> "Prop"
  | Bool -> "𝟚"
  | Integer -> "ℤ"
  | Nat -> "ℕ"
  | Real -> "ℝ"
  | Rational -> "ℚ"
  | Octanionic -> "𝕆"
  | Quaternionic -> "ℍ"
  | NatToReal e -> "ℝ(" ^ string_of_exp e ^ ")"
  | RealConst e -> "ℝ(" ^ string_of_float e ^ ")"
  | Complex -> "ℂ"
  | If (c, t, f) -> "If (" ^ string_of_exp c ^ ", " ^ string_of_exp t ^ ", " ^ string_of_exp f ^ ")"
  | Vec (n, f, a, b) -> "𝕍 (" ^ string_of_int n ^ ", " ^ string_of_exp f ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealIneq (op, a, b) -> "RealIneq (" ^ (match op with Lt -> "<" | Gt -> ">" | Lte -> "<=" | Gte -> ">=" | Eq -> "=" | Neq -> "Neq") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | RealOps (op, a, b) ->
    let op_str = match op with
      | Plus -> "+ℝ" | Minus -> "-ℝ" | Mul -> "*ℝ" | Div -> "/ℝ" | Pow -> "^ℝ"
      | Abs -> "Abs" | Ln -> "Ln" | Sin -> "Sin" | Cos -> "Cos" | Exp -> "Exp" | Neg -> "Neg"
    in "RealOps (" ^ op_str ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | ComplexOps (op, a, b) -> "ComplexOps (" ^ (match op with CPlus -> "+C" | CMinus -> "-C" | CMul -> "*C" | CDiv -> "/C") ^ ", " ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Closure s -> "Closure (" ^ string_of_exp s ^ ")"
  | Set a -> "Set (" ^ string_of_exp a ^ ")"
  | Complement a -> "Complement (" ^ string_of_exp a ^ ")"
  | Sum a -> "Sum (" ^ string_of_exp a ^ ")"
  | Union a -> "Union (" ^ string_of_exp a ^ ")"
  | Intersect (a, b) -> "Intersect (" ^ string_of_exp a ^ ", " ^ string_of_exp b ^ ")"
  | Power a -> "Power (" ^ string_of_exp a ^ ")"
  | Or (a, b) -> "(" ^ string_of_exp a ^ " ∨ " ^ string_of_exp b ^ ")"
  | And (a, b) -> "(" ^ string_of_exp a ^ " ∧ " ^ string_of_exp b ^ ")"
  | Ordinal -> "Ordinal"
  | Mu (b, s, f) -> "μ (" ^ string_of_exp b ^ ", " ^ string_of_exp s ^ ")" ^ ", " ^ string_of_exp f
  | Measure (sp, s) -> "Measure (" ^ string_of_exp sp ^ ", " ^ string_of_exp s ^ ")"
  | Seq a -> "Seq (" ^ string_of_exp a ^ ")"
  | Limit (f, x, l, p) -> "Limit (" ^ string_of_exp f ^ ", " ^ string_of_exp x ^ ", " ^ string_of_exp l ^ ", " ^ string_of_exp p ^ ")"
  | Sup s -> "Sup (" ^ string_of_exp s ^ ")"
  | Inf s -> "Inf (" ^ string_of_exp s ^ ")"
  | Lebesgue (f, m, _) -> "Lebesgue (" ^ string_of_exp f ^ ", " ^ string_of_exp m ^ ")"

let rec subst_many m t =
    match t with
    | SetEq (s1, s2) -> SetEq (subst_many m s1, subst_many m s2)
    | True -> True
    | False -> False
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
    | Or (a, b) -> Or (subst_many m a, subst_many m b)
    | Union a -> Union (subst_many m a)
    | Intersect (a, b) -> Intersect (subst_many m a, subst_many m b)
    | Complement a -> Complement (subst_many m a)
    | Power a -> Power (subst_many m a)
    | And (a, b) -> And (subst_many m a, subst_many m b)
    | Ordinal -> Ordinal
    | Mu (base, sigma, f) -> Mu (subst_many m base, subst_many m sigma, subst_many m f)
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
    | Set a ->
      let a_ty = infer env ctx a in
      (match a_ty with
      | Forall (_, domain, body) when equal env ctx domain Real && equal env ctx body Prop -> Set Real
      | Universe _ -> Universe 0
      | Set b -> Set b
      | _ -> raise (TypeError ("Set expects a predicate or type, got " ^ string_of_exp a_ty)))
    | SetEq (s1, s2) ->
      let s1_ty = infer env ctx s1 in
      let s2_ty = infer env ctx s2 in
      (match s1_ty, s2_ty with
       | Set base1, Set base2 when equal env ctx base1 base2 -> Prop
       | _ -> raise (TypeError "SetEq requires two sets"))
    | True -> Prop
    | False -> Prop
    | Universe 0 -> Universe 1
    | Universe 1 -> Universe 1
    | Universe _ -> raise (TypeError "Invalid Universe (index should be less than 2)")
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Forall (_, Real, Pair (Lam (_, p, q), Lam (_, q', p'))) when equal env ctx p p' && equal env ctx q q' -> Prop
    | Forall (x, domain, body) ->
      let _ = infer env ctx domain in
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      if equal env ctx body_ty Prop then Prop
      else Universe 0
    | Exists (x, domain, body) -> let _ = infer env (add_var ctx x domain) body in Prop
    | App (f, arg) ->
      if verbose then (
         Printf.printf "App function: ";
         Printf.printf "%s\n" (string_of_exp (infer env ctx f))
      );
      (match infer env ctx f with
      | Forall (x, a, b) -> check env ctx arg a; subst x arg b
      | Set (Set a) -> check env ctx arg (Set a); Prop
      | Set Real -> check env ctx arg Real; Prop
      | _ -> raise (TypeError "Application requires a Pi type"))
    | Lam (x, domain, body) ->
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      let domain_ty = infer env ctx domain in
      (match domain, body with
      | Real, Prop -> Set Real
      | _ -> (match domain_ty with
              | Universe _ -> Forall (x, domain, body_ty)
              | Real -> if equal env ctx body_ty Prop then Set Real else Forall (x, domain, body_ty)
              | Prop -> Forall (x, domain, body_ty)
              | _ -> raise (TypeError "Lambda domain must be a type or proposition")))
    | Pair (a, b) -> let a_ty = infer env ctx a in let b_ty = infer env (add_var ctx "N" a_ty) b in Exists ("N", a_ty, b_ty)
    | Fst p -> (match infer env ctx p with | Exists (_, a, _) -> a | _ -> raise (TypeError ("Fst expects a Sigma type")))
    | Snd p -> (match infer env ctx p with | Exists (x, _, b) -> subst x (Fst p) b | _ -> raise (TypeError ("Snd expects a Sigma type")))
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
    | RealConst _ -> Real
    | Infinity -> Real
    | Complex -> Universe 0
    | Quaternionic -> Universe 0
    | Octanionic -> Universe 0
    | Rational -> Universe 0
    | If (cond, t, f) ->
      let ct = infer env ctx cond in
      let _ = check env ctx ct (Universe 0) in
      let t_typ = infer env ctx f in let _ = check env ctx t t_typ in t_typ
    | Vec (_, field, a, b) -> let _ = check env ctx field (Universe 0) in let _ = check env ctx a field in let _ = check env ctx b field in Universe 0
    | RealIneq (_, a, b) ->
      let _ = infer env ctx a in
      let _ = infer env ctx b in
      Prop
    | RealOps (op, a, b) ->
        let _ = check env ctx a Real in
        (match op with
         | Plus | Minus | Mul | Div | Pow -> let _ = check env ctx b Real in Real
         | Abs | Ln | Sin | Cos | Exp | Neg  -> Real)
    | ComplexOps (_, a, b) -> let _ = check env ctx a Complex in let _ = check env ctx b Complex in Complex
    | Closure s -> let _ = check env ctx s (Set Real) in Set Real
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
    | Or (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | And (a, b) -> let a_typ = infer env ctx a in let _ = check env ctx b a_typ in a_typ
    | Ordinal -> Universe 0
    | Seq a ->
      let a_ty = infer env ctx a in
      (match a_ty with
      | Forall ("n", Nat, codomain) when equal env ctx codomain Nat ||
                                         equal env ctx codomain Integer ||
                                         equal env ctx codomain Real ||
                                         equal env ctx codomain Complex -> a_ty
      | _ -> raise (TypeError "Seq expects a function a : N -> ( N | Z | Q | R | C | H | O )"))
    | Limit (Seq f, x, l, p) ->
        let codomain = match infer env ctx f with
                       | Forall ("n", Nat, c) -> c
                       | _ -> raise (TypeError "Limit expects a sequence") in
        let _ = check env ctx f (Forall ("n", Nat, codomain)) in
        let x_ty = if equal env ctx x Infinity then Real else Nat in
        let _ = check env ctx x x_ty in
        let _ = check env ctx l codomain in
        let limit_proof_type =
            Forall ("ε", Real,
              Forall ("p", RealIneq (Gt, Var "ε", Zero),
                Exists ("N", Real,
                  Forall ("n", Nat,
                    Forall ("q", RealIneq (Gt, Var "n", Var "N"), Prop))))) in
        let ctx' = add_var (add_var ctx "f" (Forall ("n", Nat, codomain))) "l" codomain in
        let _ = check env ctx' p (subst_many [("f", f); ("l", l)] limit_proof_type) in Prop
    | Limit _ -> raise (TypeError "Limit expects a Seq argument")
    | Sup s -> let _ = check env ctx s (Set Real) in Real
    | Inf s -> let _ = check env ctx s (Set Real) in Real
    | Mu (base, sigma, measure_func) ->
      let _ = check env ctx base (Universe 0) in
      let _ = check env ctx sigma (Set (Set base)) in
      let _ = check env ctx measure_func (Forall ("A", Set Real, Real)) in
      Measure (base, Set (Set base))
    | Measure (space, sigma) ->
      let _ = check env ctx space (Universe 0) in
      let _ = check env ctx sigma (Set (Set space)) in Universe 0
    | Lebesgue (f, mu, set) ->
      let base = match infer env ctx mu with
        | Measure (b, _) -> b
        | _ -> raise (TypeError "Lebesgue expects a measure") in
      let _ = check env ctx f (Forall ("x", Real, Real)) in
      let _ = check env ctx mu (Measure (Real, Set (Set Real))) in
      let _ = check env ctx set (Set base) in
      Real

and universe env ctx t =
    match infer env ctx t with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | _ -> raise (TypeError (Printf.sprintf "Expected a universe"))

and check env (ctx : context) (term : exp) (expected : exp) : unit =
    if trace then Printf.printf "Check: %s Expected: %s\n" (string_of_exp term) (string_of_exp expected);
    let inferred = infer env ctx term in
    if equal env ctx inferred expected then ()
    else (
       Printf.printf "Last Error: %s\nInferred: %s\nExpected: %s\n" (string_of_exp term) (string_of_exp inferred) (string_of_exp expected);
       raise (TypeError "Type mismatch")
    )

and equal' env ctx t1 t2 =
    if verbose then Printf.printf "Equal: %s vs %s\n" (string_of_exp t1) (string_of_exp t2);
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Forall (x, a, b), Forall (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Forall (_, a, _) -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Forall (_, a, _) -> equal' env ctx a d | _ -> false)
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
    | Union a, Union b -> equal' env ctx a b
    | Intersect (a1, b1), Intersect (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Complement a, Complement b -> equal' env ctx a b
    | Power a1, Power a2 -> equal' env ctx a1 a2
    | Or (a1, b1), Or (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | And (a1, b1), And (a2, b2) -> equal' env ctx a1 a2 && equal' env ctx b1 b2
    | Ordinal, Ordinal -> true
    | Mu (b1, s1, f1), Mu (b2, s2, f2) -> equal' env ctx b1 b2 && equal' env ctx s1 s2 && equal' env ctx f1 f2
    | Measure (sp1, s1), Measure (sp2, s2) -> equal' env ctx sp1 sp2 && equal' env ctx s1 s2
    | Seq a1, Seq a2 -> equal' env ctx a1 a2
    | Limit (f1, x1, l1, p1), Limit (f2, x2, l2, p2) -> equal' env ctx f1 f2 && equal' env ctx x1 x2 && equal' env ctx l1 l2 && equal' env ctx p1 p2
    | Sup s1, Sup s2 -> equal' env ctx s1 s2
    | Inf s1, Inf s2 -> equal' env ctx s1 s2
    | Lebesgue (f1, m1 ,s1), Lebesgue (f2, m2, s2) -> equal' env ctx f1 f2 && equal' env ctx m1 m2 && equal' env ctx s1 s2
    | Infinity, Infinity -> true
    | Zero, Zero -> true
    | One, One -> true
    | RealConst i, RealConst j -> i = j
    | Z, Z -> true
    | S e1, S e2 -> equal' env ctx e1 e2
    | NatToReal e1, NatToReal e2 -> equal' env ctx e1 e2
    | _ -> t1 = t2

and reduce env ctx t =
    if verbose then Printf.printf "Reduce: %s\n" (string_of_exp t);
    match t with
    | SetEq (Set (Lam (_, Real, p1)), Set (Lam (_, Real, p2))) -> smt_verify_iff ctx_z3 p1 p2
    | SetEq (s, s') when equal env ctx s s' -> True
    | Intersect (Set (Lam (x1, Real, p1)), Set (Lam (x2, Real, p2))) ->
      Set (Lam ("x", Real, And (subst x1 (Var "x") p1, subst x2 (Var "x") p2)))
    | Intersect (a, b) -> Intersect (reduce env ctx a, reduce env ctx b)
    | App (Lam (x, _, body), arg) -> subst x arg body
    | Set (Lam _) -> True
    | App (f, arg) -> let f' = reduce env ctx f in let arg' = reduce env ctx arg in App (f', arg')
    | Fst (Pair (a, _)) -> a
    | Snd (Pair (_, b)) -> b
    | Limit (f, x, l, p) -> Limit (reduce env ctx f, reduce env ctx x, reduce env ctx l, reduce env ctx p)
    | RealOps (Abs, RealOps (Minus, a, b), Zero) ->
      let a' = reduce env ctx a in
      let b' = reduce env ctx b in
      if equal env ctx a' b' then Zero else RealOps (Abs, RealOps (Minus, a', b'), Zero)
    | RealIneq (Lt, e1, _) ->
        let in_context = List.exists (fun (_, assum) ->
          match assum with
          | And (_, RealIneq (Lt, e1', _)) when equal env ctx e1 e1' ->  true
          | _ -> false
        ) ctx in
        if in_context then True else t
    | _ -> t

and normalize env ctx t =
    if verbose then Printf.printf "Normalize: %s\n" (string_of_exp t);
    let t' = reduce env ctx t in
    if equal' env ctx t t' then t else normalize env ctx t'

and z3_of_exp ctx = function
  | Var x -> Arithmetic.Real.mk_const_s ctx x
  | RealIneq (Lte, e1, e2) -> Arithmetic.mk_le ctx (z3_of_exp ctx e1) (z3_of_exp ctx e2)
  | RealIneq (Lt, e1, e2) -> Arithmetic.mk_lt ctx (z3_of_exp ctx e1) (z3_of_exp ctx e2)
  | RealIneq (Eq, e1, e2) -> Boolean.mk_eq ctx (z3_of_exp ctx e1) (z3_of_exp ctx e2)
  | And (e1, e2) -> Boolean.mk_and ctx [z3_of_exp ctx e1; z3_of_exp ctx e2]
  | Or (e1, e2) -> Boolean.mk_or ctx [z3_of_exp ctx e1; z3_of_exp ctx e2]
  | One -> Arithmetic.Real.mk_numeral_i ctx 1
  | Zero -> Arithmetic.Real.mk_numeral_i ctx 0
  | RealConst i -> Arithmetic.Real.mk_numeral_i ctx (int_of_float i)
  | Set (Lam (_, Real, body)) -> z3_of_exp ctx body
  | RealOps (Plus, e1, e2) -> Arithmetic.mk_add ctx [z3_of_exp ctx e1; z3_of_exp ctx e2]
  | Intersect (Set (Lam (_, Real, p1)), Set (Lam (_, Real, p2))) -> Boolean.mk_and ctx [z3_of_exp ctx p1; z3_of_exp ctx p2]
  | App (Set (Lam (x, Real, body)), arg) -> z3_of_exp ctx (subst x arg body)
  | x -> failwith ("Unsupported expression in Z3 conversion: " ^ (string_of_exp x))

and smt_verify_iff ctx p q =
  let solver = Solver.mk_solver ctx None in
  let p_z3 = z3_of_exp ctx p in
  let q_z3 = z3_of_exp ctx q in
  let not_iff = Boolean.mk_not ctx (Boolean.mk_iff ctx p_z3 q_z3) in
  Solver.add solver [not_iff];
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> True
  | Solver.SATISFIABLE -> False
  | Solver.UNKNOWN -> failwith "Z3 returned UNKNOWN"

