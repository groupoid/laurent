Laurent Schwartz: Analytical Type Theory
========================================

Type Theory for mechanical formalization of Théorie des
Distributions and Analyse Mathematique by Laurent Schwartz and Foundation of Constructive Analysis by Errett Bishop.

<img src="https://laurent.groupoid.space/img/laurent.png" widht=600>

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

Usage
-----

```
$ ./laurent
TEST OK> integral_sig : Universe 0
TEST OK> integral_term : Forall (f, Forall (x, ℝ, ℝ), Forall (a, ℝ, Forall (b, ℝ, ℝ)))
TEST OK> sequence_a : Forall (n, ℕ, ℝ)
TEST OK> limit_a : Prop
TEST OK> inf_a : ℝ
TEST OK> sup_a : ℝ
TEST OK> set_a : Set (ℝ)
TEST OK> universal set : Set (Prop)
TEST OK> e : ℝ
TEST OK> l_2 space : Forall (f, Forall (x, ℝ, ℝ), Prop)
TEST OK> sigma_algebra : Prop
TEST OK> measurable : Prop
All tests passed!
```

Syntax
------

```
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
  | Infinity                       (*   ∞   *)
  | S of exp                       (*   1+  *)
  | Z                              (*   0   *)
  | If of exp * exp * exp                   (* 𝟚-Eliminator : 𝟚 -> ℝ         *)
  | RealIneq of real_ineq * exp * exp       (* Inequalities a < b, etc.      *)
  | RealOps of real_op * exp * exp          (* Real +, -, *, etc.            *)
  | ComplexOps of complex_op * exp * exp    (* Complex +, -, *, etc.         *)
  | Closure of exp
  | Set of exp              (* Term level: { x : A | P } Set Lam, Type Level: Set Real *)
  | UnionSet of exp * exp   (* A ∪ B *)
  | Complement of exp       (* ℝ \ A *)
  | Intersect of exp * exp  (* a ∩ b *)
  | Power of exp            (* a ^ b *)
  | And of exp * exp        (* a ∩ b *)
  | Ordinal
  | Mu of exp * exp         (* Measure type *)
  | Measure of exp * exp    (* Measure expression *)
  | Seq of exp              (* a_n : N -> R, Seq Lam *)
  | Sum of exp              (* ∑ a_n, Sum Lam *)
  | Union of exp            (* ⋃ A_n, Union Lam  *)
  | Limit of limit          (* Limit(f,x,l,p) : Real, f: sequence, x: bound, l: limit, p: proof *)
  | Sup of exp              (* sup a_n : R, Sup Seq (N -> R) *)
  | Inf of exp              (* inf a_n : R, Inf Seq (N -> R) *)
  | Lebesgue of lebesgue    (* ∫ f dμ over set *)

and real_op = RPlus | RMinus | RMult | RDiv
and real_ineq = RLt | RGt | RLte | RGte
and complex_op = CPlus | CMinus | CMult | CDiv | CExp
```

## Analyse Mathematique

### Taylor’s Theorem with Remainder

* Volume 1: Calculus
* Chapter I: Differential Calculus

If f:R→R is n-times differentiable at a, then f(x) = \Sigma_{k=0}^{n-1}\frac{f^(k)(a)}{k!}(x-a)^k + 𝑅_𝑛(𝑥), where 𝑅_𝑛(𝑥)=𝑜((𝑥−𝑎)^{𝑛−1}) as 𝑥→𝑎.

```
let taylor_theorem = Pi (Real, ("a", Pi (Nat, ("n",
  Pi (Pi (Real, ("x", Real)), ("f",
    And (
      Pi (Nat, ("k", If (RealIneq (RLte, Var "k", Var "n"),
              diff_k (Var "f", Var "a", Var "k"), Bool))),
      Id (Real,
        App (Var "f", Var "x"),
        RealOps (RPlus,
          App (sum (Nat, ("k",
                RealOps (RDiv, App (diff_k (Var "f", Var "a", Var "k")), fact (Var "k")),
                RealOps (RMul, Var "k",
                RealOps (RMinus, Var "x", Var "a")))), zero,
                RealOps (RMinus, Var "n", one)),
          remainder (Var "f", Var "x", Var "a", Var "n")))
      ))
    ))
  ))
```

```
let proof_taylor =
   Lam (Real, ("a", Lam (Nat, ("n", Lam (Pi (Real, ("x", Real)), ("f",
    Pair ("diff_cond", Pi (Nat, ("k", If (RealIneq (RLte, Var "k", Var "n"),
            Refl (diff_k (Var "f", Var "a", Var "k")), Bool))),
    Refl (Id (Real,
      App (Var "f", Var "x"),
      RealOps (RPlus,
        App (sum (Nat, ("k", RealOps (RDiv, App (diff_k (Var "f", Var "a", Var "k")),
               fact (Var "k")),
        RealOps (RMul, Var "k", RealOps (RMinus, Var "x", Var "a")))), 
                    zero, RealOps (RMinus, Var "n", one)),
        remainder (Var "f", Var "x", Var "a", Var "n"))))
    )
  ))))))
```

### Fundamental Theorem of Calculus

* Volume 1: Calculus
* Chapter II: Integral Calculus

If 𝑓 is continuous on [𝑎,𝑏], then 𝐹(𝑥)=∫_𝑎^𝑥{𝑓(𝑡)}𝑑𝑡 is differentiable, and 𝐹′(𝑥)=𝑓(𝑥).

```
let ftc = Pi (Real, ("a", Pi (Real, ("b",
  Pi (Pi (Real, ("x", Real)), ("f",
    And (
      continuous (Set (Lam (Real, ("x",
          And (RealIneq (RGte, Var "x", Var "a"),
               RealIneq (RLte, Var "x", Var "b"))))), Var "f"),
      Id (Real,
        diff (Lam (Real, ("x", Lebesgue (Lam (Real, ("t",
                App (Var "f", Var "t"))), Var "a", Var "x"))), Var "x"),
        App (Var "f", Var "x"))
      ))
    ))
  ))
```

```
let proof_ftc = Lam (Real, ("a", Lam (Real, ("b", Lam (Pi (Real, ("x", Real)), ("f",
  Pair (
    "cont", Refl (continuous (Set (Lam (Real, ("x",
            And (RealIneq (RGte, Var "x", Var "a"),
                 RealIneq (RLte, Var "x", Var "b"))))), Var "f")),
    Refl (Id (Real,
      diff (Lam (Real, ("x", Lebesgue (Lam (Real, ("t",
            App (Var "f", Var "t"))), Var "a", Var "x"))), Var "x"),
      App (Var "f", Var "x")))
    )
  ))))))
```

### Lebesgue Dominated Convergence Theorem

* Volume 2: Topology and Functional Analysis
* Chapter III: Integration

If 𝑓𝑛→𝑓 a.e., ∣𝑓𝑛∣≤𝑔, and ∫𝑔<∞, then ∫𝑓𝑛→∫𝑓.

```
let dominated_convergence = Pi (Seq (Pi (Real, ("x", Real)), ("fn",
  Pi (Pi (Real, ("x", Real)), ("f",
    Pi (Pi (Real, ("x", Real)), ("g",
      And (
        Limit (Nat, Var "fn", Var "f"),
        And (
          Pi (Nat, ("n", Pi (Real, ("x",
               RealIneq (RLte, abs (App (App (Var "fn", Var "n"), Var "x")),
                        App (Var "g", Var "x")))))),
          And (
            integrable (Var "g"),
            Id (Real,
              Limit (Nat, Lam (Nat, ("n", Lebesgue (App (Var "fn", Var "n"), zero, one))),
              Lebesgue (Var "f", zero, one))
            )
          ))
        )
      ))
    ))
  ))
```

```
let proof_dominated = Lam (Seq (Pi (Real, ("x", Real)), ("fn",
  Lam (Pi (Real, ("x", Real)), ("f",
    Lam (Pi (Real, ("x", Real)), ("g",
      Pair (
        "lim", Refl (Limit (Nat, Var "fn", Var "f")),
        Pair (
          "dom", Pi (Nat, ("n", Refl (Pi (Real, ("x",
                RealIneq (RLte, abs (App (App (Var "fn", Var "n"), Var "x")),
                         App (Var "g", Var "x"))))))),
          Pair (
            "int_g", Refl (integrable (Var "g")),
            Refl (Id (Real,
              Limit (Nat, Lam (Nat, ("n", Lebesgue (App (Var "fn", Var "n"), zero, one))),
              Lebesgue (Var "f", zero, one)))
            )
          )
        )
      ))))))
```

### Schwartz Kernel Theorem

* Volume 2. Topology and Functional Analysis
* Chapter VI: Distributions

Every continuous bilinear form 𝐵:𝐷(𝑅^𝑛)×𝐷(𝑅^𝑚)→𝑅 is represented by a distribution 𝐾∈𝐷′(𝑅^𝑛×𝑅^𝑚) via 𝐵(𝜙,𝜓)=⟨𝐾,𝜙⊗𝜓⟩B(ϕ,ψ)=⟨K,ϕ⊗ψ⟩.

```
let kernel_theorem = Pi (Pi (Real, ("x", Real), Pi (Real, ("y", Real)), ("B",
  Sig (Set (Pi (Real, ("x", Pi (Real, ("y", Real)))), ("K",
    Pi (Pi (Real, ("x", Real)), ("phi",
      Pi (Pi (Real, ("y", Real)), ("psi",
        Id (Real,
          App (App (Var "B", Var "phi"), Var "psi"),
          App (Var "K", Lam (Real, ("x",
                        Lam (Real, ("y",
            RealOps (RMul, App (Var "phi", Var "x"),
                           App (Var "psi", Var "y")))))))))))))))
```

Proof. Classical, relies on nuclear space properties of 𝐷: define 𝐾(𝑓)=𝐵(𝑓(⋅,0),𝑓(0,⋅)), extend by density and continuity. 
Verification: 𝐵(𝜙,𝜓)=⟨𝐾,𝜙⊗𝜓⟩ externally tested.

```
let proof_kernel = Lam (Pi (Real, ("x", Real), Pi (Real, ("y", Real)), ("B",
  Pair (
    "K", Lam (Pi (Real, ("x", Pi (Real, ("y", Real))), ("f",
      App (Var "B", Lam (Real, ("x", App (Var "f", Var "x", zero))),
                    Lam (Real, ("y", App (Var "f", zero, Var "y")))))),
    Pi (Pi (Real, ("x", Real)), ("phi",
      Pi (Pi (Real, ("y", Real)), ("psi",
        Refl (Id (Real,
          App (App (Var "B", Var "phi"), Var "psi"),
          App (Var "K", Lam (Real, ("x",
                        Lam (Real, ("y",
           RealOps (RMul, App (Var "phi", Var "x"),
                          App (Var "psi", Var "y")))))))
        ))
      ))
    )
  ))))
```

### Banach Spaces and Duality

* Volume 2. Topology and Functional Analysis
* Chapter V: Banach Spaces

For a Banach space 𝑋, there’s a bijection between closed subspaces of 𝑋 and closed subspaces of 𝑋∗: A↦A^⊥, 𝐵↦^⊥𝐵.
This bijection applies to closed subspaces (vector spaces), not arbitrary closed sets (e.g., singletons, bounded sets).

```
let banach_space x = And (
  normed_space (Var "x"),
  Pi (Seq (Var "x"), ("xn",
    If (cauchy (Var "xn", Var "x"),
        Sig (Var "x", ("l", Limit (Nat, Var "xn", Var "l"))),
        Bool)))
)

let normed_space x = And (
  Pi (Var "x", ("a", Pi (Var "x", ("b",
    RealIneq (RLte, norm (RealOps (RPlus, Var "a", Var "b")),
        RealOps (RPlus, norm (Var "a"), norm (Var "b"))))))),
  Pi (Real, ("c", Pi (Var "x", ("a",
    Id (Real, norm (RealOps (RMult, Var "c", Var "a")), 
         RealOps (RMult, abs (Var "c"), norm (Var "a")))))))
)

let cauchy xn x = Pi (Real, ("eps",
  And (RealIneq (RGt, Var "eps", zero),
    Sig (Nat, ("N",
      Pi (Nat, ("m", Pi (Nat, ("n",
        If (And (RealIneq (RGt, Var "m", Var "N"), RealIneq (RGt, Var "n", Var "N")),
            RealIneq (RLt, norm (RealOps (RMinus, App (Var "xn", Var "m"), 
                    App (Var "xn", Var "n"))), Var "eps"), Bool)))))))))

let norm a = Sup (Lam (Real, ("r", RealIneq (RLte, abs (Var "a"), Var "r"))))
```

M(K)=C(K)^*.

```
let dual_space x = Set (Pi (Var "x", ("a", Real)), ("phi",
  And (
    linear (Var "phi"),
    bounded (Var "phi")
  )))

let linear phi = And (
  Pi (Var "x", ("a", Pi (Var "x", ("b",
    Id (Real, App (Var "phi", RealOps (RPlus, Var "a", Var "b")),
              RealOps (RPlus, App (Var "phi", Var "a"), App (Var "phi", Var "b")))))),
  Pi (Real, ("c", Pi (Var "x", ("a",
    Id (Real, App (Var "phi", RealOps (RMult, Var "c", Var "a")),
              RealOps (RMult, Var "c", App (Var "phi", Var "a")))))))
)

let bounded phi = Sig (Real, ("M",
  And (RealIneq (RGt, Var "M", zero),
    Pi (Var "x", ("a", RealIneq (RLte, abs (App (Var "phi", Var "a")),
                       RealOps (RMult, Var "M", norm (Var "a"))))))))
```

```
let annihilator x s = Set (dual_space (Var "x"), ("phi",
  Pi (Var "s", ("a", Id (Real, App (Var "phi", Var "a"), zero)))))

let pre_annihilator x s = Set (Var "x", ("a",
  Pi (dual_space (Var "x"), ("phi",
    If (App (Var "s", Var "phi"),
      Id (Real, App (Var "phi", Var "a"), zero), Bool)))))
```

```
let closed_subspace x s = And (
  subspace (Var "x", Var "s"),
  Id (Set (Var "x"), Var "s", Closure (Var "s")))

let subspace x s = And (
  Pi (Var "s", ("a", Pi (Var "s", ("b",
    App (Var "s", RealOps (RPlus, Var "a", Var "b")))))),
  Pi (Real, ("c", Pi (Var "s", ("a",
    App (Var "s", RealOps (RMult, Var "c", Var "a")))))))
```

```
let bijection_theorem = Pi (Set Real, ("X",
  If (banach_space (Var "X"),
    And (
      Pi (Set (Var "X"), ("A",
        If (closed_subspace (Var "X", Var "A"),
            Id (Set (Var "X"), Var "A", pre_annihilator (Var "X", 
                    annihilator (Var "X", Var "A"))), Bool))),
      Pi (Set (dual_space (Var "X")), ("B",
        If (closed_subspace (dual_space (Var "X"), Var "B"),
            Id (Set (dual_space (Var "X")), Var "B", annihilator (Var "X",
                    pre_annihilator (Var "X", Var "B"))), Bool))))), Bool)))
```

```
let proof_bijection_theorem = Lam (Set Real, ("X",
  If (Refl (banach_space (Var "X")),
    Pair (
      "fwd", Lam (Set (Var "X"), ("A",
        If (Refl (closed_subspace (Var "X", Var "A")),
          Pair ("sub", Refl (subspace (Var "X", pre_annihilator (Var "X",
             annihilator (Var "X", Var "A")))),
            Pair ("closed", Refl (Id (Set (Var "X"), 
                Closure (pre_annihilator (Var "X", annihilator (Var "X", Var "A"))),
                pre_annihilator (Var "X", annihilator (Var "X", Var "A")))),
              Refl (Id (Set (Var "X"), Var "A", pre_annihilator (Var "X",
                    annihilator (Var "X", Var "A")))))), Bool))),
      Lam (Set (dual_space (Var "X")), ("B",
        If (Refl (closed_subspace (dual_space (Var "X"), Var "B")),
          Pair ("sub", Refl (subspace (dual_space (Var "X"), 
                     annihilator (Var "X", pre_annihilator (Var "X", Var "B")))),
            Pair (
              "closed", Refl (Id (Set (dual_space (Var "X")), 
                Closure (annihilator (Var "X", pre_annihilator (Var "X", Var "B"))),
                annihilator (Var "X", pre_annihilator (Var "X", Var "B")))),
              Refl (Id (Set (dual_space (Var "X")), Var "B", annihilator (Var "X",
                           pre_annihilator (Var "X", Var "B")))))), Bool)))), Bool)))

```

### Banach-Steinhaus Theorem

* Volume 2. Topology and Functional Analysis
* Chapter IV. Topological Vector Spaces

∀x∈X, α∈A sup ∥T α x∥ Y​ <∞⟹∃M∈R,∀α∈A,∥T α​ ∥ X→Y​ ≤M, ∥𝑇𝛼∥ = ∥=sup{∥T α x∥ Y ∣∥x∥ X ≤1}. 

```
let operator x y = Pi (Var "x", ("a", Var "y"))

let continuous_linear x y t = And (
  linear (Var "t"),
  bounded (Var "t")
)

let bounded t = Sig (Real, ("M",
  And (RealIneq (RGt, Var "M", zero),
    Pi (Var "x", ("a",
      RealIneq (RLte, norm (App (Var "t", Var "a")),
       RealOps (RMult, Var "M", norm (Var "a"))))))))

let op_norm x y t = Sup (Lam (Real, ("r",
  Pi (Var "x", ("a",
    If (RealIneq (RLte, norm (Var "a"), one),
        RealIneq (RLte, norm (App (Var "t", Var "a")), Var "r"),
        Bool)))))

let bounded_set s = Sig (Real, ("B",
  And (RealIneq (RGt, Var "B", zero),
    Pi (Var "T", ("t", RealIneq (RLte, App (Var "s", Var "t"), Var "B"))))))

let zero = RealOps (RMinus, Real, Real)

let one = RealOps (RPlus, zero, zero)

```

```
let banach_steinhaus = Pi (Set Real, ("X",
  Pi (Set Real, ("Y",
    If (And (banach_space (Var "X"), normed_space (Var "Y")),
      Pi (Set (operator (Var "X", Var "Y")), ("T",
        If (And (
              Pi (Var "T", ("t", continuous_linear (Var "X", Var "Y", Var "t"))),
              Pi (Var "X", ("x",
                bounded_set (Lam (Var "T", ("t", norm (App (Var "t", Var "x")))))))),
            Sig (Real, ("M",
              And (RealIneq (RGt, Var "M", zero),
                Pi (Var "T", ("t", RealIneq (RLte, 
                op_norm (Var "X", Var "Y", Var "t"), Var "M")))))), Bool))), Bool))))
```

```
let proof_banach_steinhaus = Lam (Set Real, ("X",
  Lam (Set Real, ("Y",
    If (Pair ("banach", Refl (banach_space (Var "X")), "normed", Refl (normed_space (Var "Y"))),
      Lam (Set (operator (Var "X", Var "Y")), ("T",
        If (Pair (
              "cont_lin", Refl (Pi (Var "T", ("t", continuous_linear (Var "X", Var "Y", Var "t")))),
              "pt_bdd", Refl (Pi (Var "X", ("x",
                bounded_set (Lam (Var "T", ("t", norm (App (Var "t", Var "x"))))))))),
          Pair (
            "M", Sup (Lam (Real, ("r",
              Pi (Var "T", ("t", RealIneq (RLte, op_norm (Var "X", Var "Y", Var "t"), Var "r")))))),
            Pair (
              "M_pos", RealIneq (RGt, Var "M", zero),  (* External check *)
              "unif_bdd", Refl (Pi (Var "T", ("t",
                RealIneq (RLte, op_norm (Var "X", Var "Y", Var "t"), Var "M")))))
            )
          ),
          Bool))),
      Bool))))
```

### de Rham Theorem

```
let omega := Set (Vec_n n)

let gamma := 
  Lam (Real, ("t", 
    If (RealIneq (RLte, Var "t", RealConst 0.5), 
        App (Var "gamma_1", RealOps (RMult, RealConst 2, Var "t")), 
        App (Var "gamma_2", RealOps (RMinus, one, RealOps (RMult, 
          RealConst 2, RealOps (RMinus, Var "t", RealConst 0.5)))))))

let is_open omega := 
  Pi (omega, ("x", 
    Sig (Real, ("delta", 
      And (RealIneq (RGt, Var "delta", zero),
        Pi (Vec_n n, ("y", 
          If (RealIneq (RLt, App (norm, 
              RealOps (RMinus, Var "y", Var "x")), Var "delta"), 
              App (omega, Var "y"), 
              Bool))))))))

let c1_form omega n := 
  Sig (one_form omega n, ("w", 
    Pi (omega, ("x", 
      Sig (Vec_n n, ("dw", 
        Pi (Vec_n n, ("v", 
          Id (Real, 
            Limit (Real, Lam (Real, ("h", RealOps (RDiv, RealOps (RMinus,
            App (App (Var "w", RealOps (RPlus, Var "x", Var "h")), Var "v"),
            App (App (Var "w", Var "x"), Var "v"))), Var "h"))), zero), 
            App (Var "dw", Var "v"))))))))))

let loop omega n := 
  Sig (Pi (Set (Lam (Real, ("t", And (RealIneq (RGte, Var "t", zero), 
           RealIneq (RLte, Var "t", one)))), ("t", omega)), ("gamma", 
    And (
      Id (Vec_n n, App (Var "gamma", zero), App (Var "gamma", one)),
      Pi (Nat, ("k", 
        Sig (Pi (Real, ("t", Vec_n n)), ("dgamma_k", 
          Pi (Real, ("t", 
            Id (Vec_n n, 
              Limit (Vec_n n, Lam (Real, ("h", RealOps (RDiv, RealOps (RMinus, 
              App (Var "gamma", RealOps (RPlus, Var "t", Var "h")), 
              App (Var "gamma", Var "t"))), Var "h"))), zero), 
              App (Var "dgamma_k", Var "t")))))))))))

let zero_form omega := Pi (omega, ("x", Real))

let interval_measure := 
  Measure (Set (Lam (Real, ("t", And (RealIneq (RGte, Var "t", zero), 
    RealIneq (RLte, Var "t", one)))), Mu (Var "intervals", Var "sigma"))

let deriv (Var "gamma", Var "t") := 
  Limit (Vec_n n, Lam (Real, ("h", RealOps (RDiv, RealOps (RMinus, 
    App (Var "gamma", RealOps (RPlus, Var "t", Var "h")),
         App (Var "gamma", Var "t"))), Var "h"))), zero)

let integral (Var "w", Var "gamma") := 
  Lebesgue (Lam (Real, ("t", App (App (Var "w", App (Var "gamma", Var "t")), 
        deriv (Var "gamma", Var "t")))), Var "interval_measure")

let rec cm_form Omega n m := 
  Sig (one_form Omega n, ("w", 
    If (Id (Nat, Var "m", zero), 
        True, 
        Sig (Pi (Var "Omega", ("x", Vec_n n)), ("dw", 
          And (
            Pi (Var "Omega", ("x", Pi (Vec_n n, ("v", 
              Id (Real, Limit (Real, Lam (Real, ("h", RealOps (RDiv, RealOps (RMinus,
              App (App (Var "w", RealOps (RPlus, Var "x", Var "h")), Var "v"), 
              App (App (Var "w", Var "x"), Var "v"))), Var "h"))), zero), 
              App (Var "dw", Var "v")))))),
            cm_form Omega n (RealOps (RMinus, Var "m", one)) (Lam (Var "Omega",
             ("x", Lam (Vec_n n, ("v", App (Var "dw", Var "x")))))))))))))

let differential (Var "f") := 
  Lam (Var "Omega", ("x", 
    Lam (Vec_n n, ("v", 
      Limit (Real, Lam (Real, ("h", RealOps (RDiv, RealOps (RMinus, App (Var "f", 
        RealOps (RPlus, Var "x", Var "v")), App (Var "f", Var "x"))), Var "h"))), zero)))))


```

```
let de_rham_theorem =
  Pi (Nat, ("n",   
    Pi (Set (Vec (n, Real, RealOps RPlus, RealOps RMult)),
      Pi (one_form Omega n, ("omega",
        And (c1_form Omega n (Var "omega"),
          And (Pi (loop Omega n, ("gamma",
              Id (Real, integral (Var "omega", Var "gamma"), zero))),
            Sig (zero_form Omega, ("f", And (
                Id (one_form Omega n, Var "omega", differential (Var "f")),
                Pi (Nat, ("m", If (cm_form Omega n (Var "m") (Var "omega"),
                  cm_form Omega n (Var "m") (Var "f"), Bool)))))))))))))))
```

```
let proof : de_rham_theorem =
  Lam (Nat, ("n",
    Lam (Set (Vec (Real, RealOps RPlus, RealOps RMult)), ("Omega",
      Lam (one_form Omega n, ("omega",
        Pair ("f", Lam (Omega, ("x", integral (Var "omega", path Omega n (Var "x0", Var "x")))),
          And (
            Id (one_form Omega n, Var "omega", differential (Var "f")),
            Lam (Nat, ("m", If (cm_form Omega n (Var "m") (Var "omega"),
              cm_form Omega n (Var "m") (Var "f"), Bool)))))))))))
```
