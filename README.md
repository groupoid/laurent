Laurent Schwartz: Analytical Type Theory
========================================

Type Theory for mechanical formalization of Théorie des
Distributions and Analys Mathematique by Laurent Schwartz.

<img src="https://laurent.groupoid.space/img/laurent.png" widht=600>

Type systems in mathematics and computer science provide
a structured way to formalize proofs and computations.
In this article, we present a minimal type system,
designed to encode classical and modern analysis with
just 19 core constructors. Unlike full HoTT,
we omit identity types `Id`, `idp`, `J` to keep the system lean,
\relying instead on `Bool` predicates and external test validation
for equational reasoning. We’ll explore this system through
examples, starting with classical Riemann sums, advancing
to Lebesgue integration, Bishop’s constructive analysis, L_2 spaces,
and culminating in Schwartz’s theory of distributions.

```
type exp =
  | Var of string               (* Variables *)
  | Lam of exp * (string * exp) (* Lambda abstraction *)
  | App of exp * exp            (* Application *)
  | Pi of exp * (string * exp)  (* Dependent function type *)
  | Sig of exp * (string * exp) (* Dependent pair type *)
  | Pair of string * exp * exp  (* Pair constructor *)

  | Nat                         (* Natural numbers *)
  | Real                        (* Real numbers *)
  | Complex                     (* Complex numbers *)
  | Bool                        (* Boolean type *)
  | If of exp * exp * exp       (* Conditional *)
  | Vec of exp * exp * exp      (* Vector space *)
  | RealIneq of real_ineq * exp * exp    (* Real inequalities: <, >, ≤, ≥ *)
  | RealOps of real_op * exp * exp       (* Real operations *)
  | ComplexOps of complex_op * exp * exp (* Complex operations *)
    
  | Seq of exp                  (* Sequences *)
  | Limit of exp * exp * exp    (* Limits *)
  | Sup of exp                  (* Supremum of a set s: Real -> Bool *)
  | Closure of exp              (* Topological closure of a set *)
  | Mu of exp * exp             (* Extend measure from base to sigma-algebra *)
  | Measure of exp * exp        (* Measures *)
  | Lebesgue of exp * exp       (* Lebesgue integral *)
  
  | Set of exp                  (* Sets *)
  | Union of exp * exp          (* Set union *)
  | Intersect of exp * exp      (* Set intersection *)
  | Complement of exp           (* Set complement *)
  | Power of exp                (* Power set *)
  | And of exp * exp            (* Conjunction *)
  | Ordinal                     (* Ordinals *)

  | Id of exp * exp * exp       (* Identity type *)
  | Refl of exp                 (* Reflexivity *)
  
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
let proof_taylor = Lam (Real, ("a", Lam (Nat, ("n", Lam (Pi (Real, ("x", Real)), ("f",
  Pair (
    "diff_cond", Pi (Nat, ("k", If (RealIneq (RLte, Var "k", Var "n"),
            Refl (diff_k (Var "f", Var "a", Var "k")), Bool))),
    Refl (Id (Real,
      App (Var "f", Var "x"),
      RealOps (RPlus,
        App (sum (Nat, ("k", RealOps (RDiv, App (diff_k (Var "f", Var "a", Var "k")), fact (Var "k")),
        RealOps (RMul, Var "k", RealOps (RMinus, Var "x", Var "a")))), zero, RealOps (RMinus, Var "n", one)),
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
    RealIneq (RLte, norm (RealOps (RPlus, Var "a", Var "b")), RealOps (RPlus, norm (Var "a"), norm (Var "b"))))))),
  Pi (Real, ("c", Pi (Var "x", ("a",
    Id (Real, norm (RealOps (RMult, Var "c", Var "a")), RealOps (RMult, abs (Var "c"), norm (Var "a")))))))
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
          Pair ("sub", Refl (subspace (Var "X", pre_annihilator (Var "X", annihilator (Var "X", Var "A")))),
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
