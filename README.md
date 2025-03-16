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
