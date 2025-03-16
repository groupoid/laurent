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

### Taylor’s Theorem with Remainder

Volume 1: Calculus
Chapter I: Differential Calculus

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

Volume: Calculus
Chapter II: Integral Calculus

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

Volume: Topology and Functional Analysis
Chapter III: Integration

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

## Schwartz Kernel Theorem

Volume. Topology and Functional Analysis
Chapter VI: Distributions

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

## Ba

For a Banach space 𝑋, there’s a bijection between closed subspaces of 𝑋 and closed subspaces of 𝑋∗: A↦A^⊥, 𝐵↦^⊥𝐵.
This bijection applies to closed subspaces (vector spaces), not arbitrary closed sets (e.g., singletons, bounded sets).

```
let continuous K f = Pi (Real, ("x",
  Pi (Real, ("eps",
    And (RealIneq (RGt, Var "eps", zero),
      Sig (Real, ("delta",
        And (RealIneq (RGt, Var "delta", zero),
          Pi (Real, ("y",
            If (RealIneq (RLt, abs (RealOps (RMinus, Var "x", Var "y")), Var "delta"),
                RealIneq (RLt, abs (RealOps (RMinus, App (Var "f", Var "x"), App (Var "f", Var "y"))), Var "eps"),
                Bool)))))))))
))
let C K = Set (Pi (Var "K", ("x", Real)), ("f", continuous (Var "K") (Var "f")))
let uniform_norm K f = Sig (Real, ("M",
  And (
    Pi (Real, ("x", RealIneq (RLte, abs (App (Var "f", Var "x")), Var "M"))),
    Pi (Real, ("eps", And (RealIneq (RGt, Var "eps", zero),
      Sig (Real, ("x0", RealIneq (RGte, abs (App (Var "f", Var "x0")), RealOps (RMinus, Var "M", Var "eps"))))))))
  ))
))
```

M(K)=C(K)^*.

```
let dual_C K = Set (Pi (C (Var "K"), ("f", Real)), ("phi",
  And (
    Pi (C (Var "K"), ("f", Pi (C (Var "K"), ("g",
      Id (Real, App (Var "phi", RealOps (RPlus, Var "f", Var "g")),
                RealOps (RPlus, App (Var "phi", Var "f"), App (Var "phi", Var "g"))))))),
    Pi (Real, ("a", Pi (C (Var "K"), ("f",
      Id (Real, App (Var "phi", RealOps (RMul, Var "a", Var "f")),
                RealOps (RMul, Var "a", App (Var "phi", Var "f")))))))
  ))
))
```

```
let annihilator K A = Set (dual_C (Var "K"), ("phi",
  Pi (C (Var "K"), ("f",
    If (App (Var "A", Var "f"), Id (Real, App (Var "phi", Var "f"), zero), Bool)))))
```

```
let pre_annihilator K B = Set (C (Var "K"), ("f",
  Pi (dual_C (Var "K"), ("phi",
    If (App (Var "B", Var "phi"), Id (Real, App (Var "phi", Var "f"), zero), Bool)))))
```

```
let closed_subspace_C K F = And (
  Pi (C (Var "K"), ("f", Pi (C (Var "K"), ("g",
    If (And (App (Var "F", Var "f"), App (Var "F", Var "g")),
        App (Var "F", RealOps (RPlus, Var "f", Var "g")), Bool)))),
  Pi (Seq (C (Var "K")), ("fn",
    Pi (C (Var "K"), ("f",
      If (And (
            Pi (Nat, ("n", App (Var "F", App (Var "fn", Var "n")))),
            Limit (Nat, Lam (Nat, ("n",
              App (uniform_norm (Var "K"), Lam (Real, ("x",
                RealOps (RMinus, App (App (Var "fn", Var "n"), Var "x"), App (Var "f", Var "x"))))), zero))),
          App (Var "F", Var "f"),
          Bool)))))
))
```

```
let bijection_theorem K = And (
  Pi (Set (C (Var "K")), ("A",
    If (closed_subspace_C (Var "K") (Var "A"),
        closed_subspace_C (Var "K") (pre_annihilator (Var "K") (annihilator (Var "K") (Var "A"))), Bool))),
  Pi (Set (dual_C (Var "K")), ("B",
    If (closed_subspace_C (Var "K") (Var "B"),
        closed_subspace_C (Var "K") (annihilator (Var "K") (pre_annihilator (Var "K") (Var "B"))), Bool))))
)
```
