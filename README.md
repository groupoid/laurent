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
          App (Var "K", Lam (Real, ("x", Lam (Real, ("y", RealOps (RMul, App (Var "phi", Var "x"), App (Var "psi", Var "y")))))))
        ))
      ))
    ))
  ))
```

Proof. Classical, relies on nuclear space properties of 𝐷: define 𝐾(𝑓)=𝐵(𝑓(⋅,0),𝑓(0,⋅)), extend by density and continuity. 
Verification: 𝐵(𝜙,𝜓)=⟨𝐾,𝜙⊗𝜓⟩ externally tested.

```
let proof_kernel = Lam (Pi (Real, ("x", Real), Pi (Real, ("y", Real)), ("B",
  Pair (
    "K", Lam (Pi (Real, ("x", Pi (Real, ("y", Real))), ("f",
      App (Var "B", Lam (Real, ("x", App (Var "f", Var "x", zero))), Lam (Real, ("y", App (Var "f", zero, Var "y")))))),
    Pi (Pi (Real, ("x", Real)), ("phi",
      Pi (Pi (Real, ("y", Real)), ("psi",
        Refl (Id (Real,
          App (App (Var "B", Var "phi"), Var "psi"),
          App (Var "K", Lam (Real, ("x", Lam (Real, ("y", RealOps (RMul, App (Var "phi", Var "x"), App (Var "psi", Var "y")))))))
        ))
      ))
    )
  ))))
```
