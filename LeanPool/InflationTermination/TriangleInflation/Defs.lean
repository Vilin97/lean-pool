/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Inflation for the classical triangle: definitions

Definitions for the manuscript *Inflation for the Classical Triangle: Nontermination and
Quantitative Complexity* (`papers/inflation-nontermination`). This file carries definitions
only; the statements live in `Finner.lean`, `Defect.lean`, `Main.lean`, `Fan.lean`,
`Exponent.lean` and `Rate.lean`.

## Representational decisions

* **Laws are bare real weight functions.** A law on a `Fintype` `α` is a function `α → ℝ`
  together with the predicate `IsLaw` (nonnegative, sums to `1`). The unbundled form is used
  here
  because the paper's families `Q(ε,r)`, `P_ε`, `R_p` are written for parameter ranges in
  which normalization is a hypothesis of the statement rather than part of the datum, and
  because the feasibility definitions quantify over witnesses on large index types where
  carrying proof fields through every statement is noise. No Mathlib `Measure` or `PMF` is
  used; all inequalities are real-valued.

* **Latent alphabets are finite.** `TriangleCompatible` quantifies over a `TriangleModel`,
  whose three latent spaces are arbitrary `Fintype`s. The paper (Section 2) allows arbitrary
  measurable latent spaces. Restricting to finite latent alphabets is a formalization
  boundary; it is justified by the theorem of Rosset, Gisin and Wolfe (2018) that latent
  alphabets of bounded finite size suffice for the triangle. That theorem is **not**
  formalized here. Consequently `TriangleCompatible` is a subset of the paper's `C_tri`, and
  a theorem `¬ TriangleCompatible P` is the WEAKER statement: nonmembership in the
  finite-latent set does not by itself give nonmembership in the arbitrary-latent set. The
  arbitrary-latent statement needs either the Rosset–Gisin–Wolfe reduction (quoted, not
  formalized) or a direct measure-theoretic proof of Lemma 5.7; see `FinnerMeasure.lean`
  for the latter where it exists.

* **The recursively expressible set is not formalized.** Definition 2.3 of the paper
  (Definition 2.5, `def:gexp`, the `I^exp_t` hierarchy) needs `d`-separation in the inflated
  causal graph and
  the recursion of Wolfe–Spekkens–Fritz Definition 7. That machinery is deliberately out of
  scope here, so the membership `Q(ε,r) ∈ I^exp_t` of Theorem 5.1 (Lemma 5.10,
  `lem:expressible`)
  is an unformalized boundary. Only the two weaker hierarchies `I^NW_t` (`NWFeasible`) and
  `I^AI_t` (`AIFeasible`) are defined, and every statement that the paper phrases for all
  three hierarchies is formalized for those two. Since `I^exp_t ⊆ I^AI_t ⊆ I^NW_t`, the
  membership theorems formalized here are the weaker halves of the paper's claims and the
  rejection theorems are the stronger halves.

* **Bit convention.** Outcomes are `Bool`; `false` is the paper's `0` and `true` is its `1`.
  So `Bern(r)` has `Bern(r)(true) = r`, matching `Bern(r)(1) = r`.

* **Truncated subtraction.** Exponents `t - 1` are `ℕ` subtraction; every statement using them
  carries the hypothesis `1 ≤ t`, where the two agree.
-/

namespace TriangleInflation

open Finset

/-! ## Laws as weight functions -/

/-- A probability weight function on a finite type: nonnegative and summing to one. -/
def IsLaw {α : Type*} [Fintype α] (w : α → ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1

/-- Pushforward of a weight function along a map of finite types. -/
def pushforward {α β : Type*} [Fintype α] [DecidableEq β] (w : α → ℝ) (F : α → β) : β → ℝ :=
  fun b => ∑ a : α, if F a = b then w a else 0

/-- The product of independent per-coordinate weight functions on `ι → Bool`. -/
def prodLaw {ι : Type*} [Fintype ι] (w : ι → Bool → ℝ) : (ι → Bool) → ℝ :=
  fun x => ∏ i, w i (x i)

/-! ## Three-bit laws -/

/-- The outcome type of the triangle: the three observed bits `(A, B, C)`.
`false` is the paper's outcome `0`. -/
abbrev ThreeBit := Bool × Bool × Bool

/-- The three observed parties of the triangle. -/
inductive Party
  | A | B | C
  deriving DecidableEq, Repr

/-- The bit that a party reads off a three-bit outcome. -/
def partyBit : Party → ThreeBit → Bool
  | .A, w => w.1
  | .B, w => w.2.1
  | .C, w => w.2.2

/-- `P(000)`: the all-zero atom. -/
def atom000 (P : ThreeBit → ℝ) : ℝ := P (false, false, false)

/-- `P_A(0)`: the zero marginal of the first bit. -/
def margA (P : ThreeBit → ℝ) : ℝ := ∑ y : Bool, ∑ z : Bool, P (false, y, z)

/-- `P_B(0)`: the zero marginal of the second bit. -/
def margB (P : ThreeBit → ℝ) : ℝ := ∑ x : Bool, ∑ z : Bool, P (x, false, z)

/-- `P_C(0)`: the zero marginal of the third bit. -/
def margC (P : ThreeBit → ℝ) : ℝ := ∑ x : Bool, ∑ y : Bool, P (x, y, false)

/-- The `t`-fold tensor power `P^{⊗t}`, as a law on `Fin t → ThreeBit`. -/
def tensorPow (t : ℕ) (P : ThreeBit → ℝ) : (Fin t → ThreeBit) → ℝ :=
  fun v => ∏ l : Fin t, P (v l)

/-! ## The copied observations of the order-`t` inflation

Paper Section 2.3. `A^{ij}` has `X`-index `i` and `Z`-index `j`; `B^{ik}` has `X`-index `i`
and `Y`-index `k`; `C^{jk}` has `Z`-index `j` and `Y`-index `k`. -/

/-- The `3t²` copied observations of the order-`t` inflation. -/
inductive Obs (t : ℕ)
  | A (i j : Fin t) : Obs t
  | B (i k : Fin t) : Obs t
  | C (j k : Fin t) : Obs t
  deriving DecidableEq, Fintype

/-- A deterministic assignment of the copied observations, an element of `{0,1}^{3t²}`. -/
abbrev Assign (t : ℕ) := Obs t → Bool

/-- Which party a copied observation is a copy of. -/
def Obs.party {t : ℕ} : Obs t → Party
  | .A _ _ => .A
  | .B _ _ => .B
  | .C _ _ => .C

/-- The copied latent variables of the order-`t` inflation: `X_i`, `Z_j`, `Y_k`. -/
inductive Latent (t : ℕ)
  | X (i : Fin t) : Latent t
  | Z (j : Fin t) : Latent t
  | Y (k : Fin t) : Latent t
  deriving DecidableEq, Fintype

/-- The copied latent ancestors of a copied observation:
`A^{ij} ↦ {X_i, Z_j}`, `B^{ik} ↦ {X_i, Y_k}`, `C^{jk} ↦ {Z_j, Y_k}`. -/
def Obs.ancestors {t : ℕ} : Obs t → Finset (Latent t)
  | .A i j => {Latent.X i, Latent.Z j}
  | .B i k => {Latent.X i, Latent.Y k}
  | .C j k => {Latent.Z j, Latent.Y k}

/-- The copied latent ancestors of a set of copied observations. -/
def ancestorsOf {t : ℕ} (S : Finset (Obs t)) : Finset (Latent t) :=
  S.biUnion Obs.ancestors

/-- Paper Definition 2.4: two sets of copied observations are *ancestrally independent*
when their copied latent ancestors are disjoint. -/
def AncestrallyIndependent {t : ℕ} (S T : Finset (Obs t)) : Prop :=
  Disjoint (ancestorsOf S) (ancestorsOf T)

/-- The copied triangle `Δ_{ijk} = {A^{ij}, B^{ik}, C^{jk}}` (paper Section 2.3). -/
def copiedTriangle {t : ℕ} (i j k : Fin t) : Finset (Obs t) :=
  {Obs.A i j, Obs.B i k, Obs.C j k}

/-- The diagonal triangle `Δ_{lll}` (paper Section 2.3). -/
def diagonalTriangle {t : ℕ} (l : Fin t) : Finset (Obs t) := copiedTriangle l l l

/-- The three-bit outcome that an assignment gives to the copied triangle `Δ_{ijk}`. -/
def readTriangle {t : ℕ} (i j k : Fin t) (ω : Assign t) : ThreeBit :=
  (ω (Obs.A i j), ω (Obs.B i k), ω (Obs.C j k))

/-- The tuple of three-bit outcomes of the `t` diagonal triangles `(Δ_{lll})_{l ∈ [t]}`. -/
def readDiagonal {t : ℕ} (ω : Assign t) : Fin t → ThreeBit :=
  fun l => readTriangle l l l ω

/-! ### The symmetry group -/

/-- The action of `(σ_X, σ_Z, σ_Y) ∈ S_t × S_t × S_t` on copied observations. The first
component permutes `X`-copy indices, the second `Z`-copy indices, the third `Y`-copy
indices, exactly as in Definition 2.3(i). -/
def Obs.perm {t : ℕ} (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Obs t → Obs t
  | .A i j => .A (π.1 i) (π.2.1 j)
  | .B i k => .B (π.1 i) (π.2.2 k)
  | .C j k => .C (π.2.1 j) (π.2.2 k)

/-- Relabelling an assignment by an index permutation. -/
def relabel {t : ℕ} (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (ω : Assign t) : Assign t := fun v => ω (Obs.perm π v)

/-- Paper Definition 2.3(i): invariance under independent permutations of the three
index families. -/
def SymmetricLaw (t : ℕ) (Γ : Assign t → ℝ) : Prop :=
  ∀ π ω, Γ (relabel π ω) = Γ ω

/-! ### Injectable sets

Paper Definition 2.4 and Appendix A. -/

/-- The primitive condition of Wolfe–Spekkens–Fritz Definition 4, specialized to the
triangle: erasing copy indices is injective on the set, and any two members that are copies
of variables sharing a source in the triangle agree in the copy index of that source. -/
def SharedAgree {t : ℕ} : Obs t → Obs t → Prop
  | .A i _, .B i' _ => i = i'
  | .B i' _, .A i _ => i = i'
  | .A _ j, .C j' _ => j = j'
  | .C j' _, .A _ j => j = j'
  | .B _ k, .C _ k' => k = k'
  | .C _ k', .B _ k => k = k'
  | _, _ => True

/-- The primitive definition of an injectable set (paper Appendix A.3). -/
def InjectableRaw {t : ℕ} (S : Finset (Obs t)) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, u.party = v.party → u = v) ∧ (∀ u ∈ S, ∀ v ∈ S, SharedAgree u v)

/-- Paper Definition 2.4 together with Appendix A: for the triangle the injectable sets are
exactly the subsets of copied triangles. This characterization is the working definition
here; `Main.injectable_iff_injectableRaw` records its equivalence with `InjectableRaw`. -/
def Injectable {t : ℕ} (S : Finset (Obs t)) : Prop :=
  ∃ i j k : Fin t, S ⊆ copiedTriangle i j k

/-- The restriction of an assignment to a set of copied observations. -/
def restrictAssign {t : ℕ} (S : Finset (Obs t)) (ω : Assign t) : S → Bool := fun v => ω v.1

/-- The outcome pattern that a three-bit law prescribes on an injectable set: each member
reads the bit of the party it is a copy of. -/
def partyRead {t : ℕ} (S : Finset (Obs t)) (w : ThreeBit) : S → Bool :=
  fun v => partyBit v.1.party w

/-! ### The defect cube (paper Section 5.1)

`Cell t` indexes the cube `[t]³` of defect bits `D_{ijk}`; `Obs t` indexes the private bits
`N_v`. The root bits are indexed by `Root t = Cell t ⊕ Obs t`. -/

/-- The cells `(i,j,k) ∈ [t]³` of the defect cube. -/
abbrev Cell (t : ℕ) := Fin t × Fin t × Fin t

/-- The root bits of the defect cube: defects on cells, private bits on observations. -/
abbrev Root (t : ℕ) := Cell t ⊕ Obs t

/-- `onLine v c` says the cell `c` lies on the line `Λ(v)` read by the observation `v`:
`Λ(A^{ij}) = {(i,j,k) : k ∈ [t]}`, `Λ(B^{ik}) = {(i,j,k) : j ∈ [t]}`,
`Λ(C^{jk}) = {(i,j,k) : i ∈ [t]}` (paper Section 5.1). -/
def onLine {t : ℕ} : Obs t → Cell t → Bool
  | .A i j, c => (c.1 == i) && (c.2.1 == j)
  | .B i k, c => (c.1 == i) && (c.2.2 == k)
  | .C j k, c => (c.2.1 == j) && (c.2.2 == k)

/-- The output map of paper equation (eq:outputs): an observation outputs `1` exactly when
its private bit and every defect on its line are `0`. -/
def outputs {t : ℕ} (d : Cell t → Bool) (N : Obs t → Bool) : Assign t :=
  fun v => decide (N v = false ∧ ∀ c : Cell t, onLine v c = true → d c = false)

/-- The output map read off a joint root assignment. -/
def outputsOf {t : ℕ} (x : Root t → Bool) : Assign t :=
  outputs (fun c => x (Sum.inl c)) (fun v => x (Sum.inr v))

/-- The root bits that a set of copied observations reads: the defect cells on their lines,
together with their own private bits (paper Lemma 5.4, "disjoint inputs"). -/
def rootSupport {t : ℕ} (S : Finset (Obs t)) : Finset (Root t) :=
  (Finset.univ.filter (fun c : Cell t => ∃ v ∈ S, onLine v c = true)).image Sum.inl
    ∪ S.image Sum.inr

/-- `R_l`, the union of the three lines of the diagonal triangle `Δ_{lll}`: the cells with
at least two coordinates equal to `l` (paper equation (eq:Rl)). -/
def inDiagRegion {t : ℕ} (l : Fin t) (c : Cell t) : Bool :=
  onLine (Obs.A l l) c || onLine (Obs.B l l) c || onLine (Obs.C l l) c

noncomputable
section

/-! ## The paper's explicit laws -/

/-- `Bern(r)`, with `Bern(r)(true) = r`. -/
def bern (r : ℝ) : Bool → ℝ := fun b => if b then r else 1 - r

/-- Paper equation (eq:Q): `Q(ε,r) = ε δ_{000} + (1-ε) Bern(r)^{⊗3}`. -/
def Q (ε r : ℝ) : ThreeBit → ℝ := fun w =>
  ε * (if w = (false, false, false) then 1 else 0)
    + (1 - ε) * (bern r w.1 * bern r w.2.1 * bern r w.2.2)

/-- `ε_t = 1/(2t³)` (paper Theorem 5.2). -/
def epsFam (t : ℕ) : ℝ := 1 / (2 * (t : ℝ) ^ 3)

/-- `r_t = (1 - ε_t)^{t-1}` (paper Theorem 5.2). -/
def rFam (t : ℕ) : ℝ := (1 - epsFam t) ^ (t - 1)

/-- The nontermination family `P_t = Q(ε_t, r_t)` (paper Theorem 5.2). -/
def Pfam (t : ℕ) : ThreeBit → ℝ := Q (epsFam t) (rFam t)

/-- The divergent-rejecting-order family `P_ε = Q(ε, 1 - ε^{2/3}/2)` (paper Proposition
5.13). -/
def Peps (ε : ℝ) : ThreeBit → ℝ := Q ε (1 - ε ^ ((2 : ℝ) / 3) / 2)

/-- `R_p = (1-p) δ_{111} + p δ_{000}` (paper Proposition 5.12). -/
def Rlaw (p : ℝ) : ThreeBit → ℝ := fun w =>
  (1 - p) * (if w = (true, true, true) then 1 else 0)
    + p * (if w = (false, false, false) then 1 else 0)

/-- `s = 1 - r/(1-ε)^{t-1}`, the private-bit parameter of paper equation (eq:s). -/
def sParam (t : ℕ) (ε r : ℝ) : ℝ := 1 - r / (1 - ε) ^ (t - 1)

/-! ## Triangle compatibility -/

/-- A triangle model with finite latent alphabets: three latent spaces with weight
functions, and the three response probabilities `f(x,z) = Pr(A = 0 | x,z)`,
`g(x,y) = Pr(B = 0 | x,y)`, `h(z,y) = Pr(C = 0 | z,y)`. -/
structure TriangleModel where
  /-- Latent alphabet shared by parties A and B. -/
  X : Type
  /-- Latent alphabet shared by parties B and C. -/
  Y : Type
  /-- Latent alphabet shared by parties A and C. -/
  Z : Type
  fintypeX : Fintype X
  fintypeY : Fintype Y
  fintypeZ : Fintype Z
  /-- Probability weight of the source shared by A and B. -/
  μX : X → ℝ
  /-- Probability weight of the source shared by B and C. -/
  μY : Y → ℝ
  /-- Probability weight of the source shared by A and C. -/
  μZ : Z → ℝ
  /-- Conditional probability of outcome zero at A, given sources X and Z. -/
  f : X × Z → ℝ
  /-- Conditional probability of outcome zero at B, given sources X and Y. -/
  g : X × Y → ℝ
  /-- Conditional probability of outcome zero at C, given sources Z and Y. -/
  h : Z × Y → ℝ

attribute [instance] TriangleModel.fintypeX TriangleModel.fintypeY TriangleModel.fintypeZ

/-- The response law of a party: probability `q` of the outcome `0 = false`. -/
def respMass (q : ℝ) : Bool → ℝ := fun b => if b then 1 - q else q

/-- A triangle model is valid when the three source weights are laws and the three response
probabilities take values in `[0,1]`. -/
def TriangleModel.Valid (M : TriangleModel) : Prop :=
  IsLaw M.μX ∧ IsLaw M.μY ∧ IsLaw M.μZ ∧
    (∀ p, 0 ≤ M.f p ∧ M.f p ≤ 1) ∧ (∀ p, 0 ≤ M.g p ∧ M.g p ≤ 1) ∧
    (∀ p, 0 ≤ M.h p ∧ M.h p ≤ 1)

/-- The observed law of a triangle model: the sources are independent and the responses are
conditionally independent given the sources (paper Section 2.3). -/
def TriangleModel.law (M : TriangleModel) : ThreeBit → ℝ := fun w =>
  ∑ x : M.X, ∑ y : M.Y, ∑ z : M.Z,
    M.μX x * M.μY y * M.μZ z
      * respMass (M.f (x, z)) w.1 * respMass (M.g (x, y)) w.2.1 * respMass (M.h (z, y)) w.2.2

/-- Paper Section 2.3: the triangle-compatible set `C_tri`, with the finite-latent-alphabet
formalization boundary described in the file header. -/
def TriangleCompatible (P : ThreeBit → ℝ) : Prop :=
  ∃ M : TriangleModel, M.Valid ∧ M.law = P

/-! ## The finite inflation tests -/

/-- Paper Definition 2.3: the Navascués–Wolfe feasible set `I^NW_t`. A law `Γ_t` on the
copied observations, invariant under `S_t³`, whose diagonal law is the tensor power
`P^{⊗t}`. -/
def NWFeasible (t : ℕ) (P : ThreeBit → ℝ) : Prop :=
  ∃ Γ : Assign t → ℝ, IsLaw Γ ∧ SymmetricLaw t Γ ∧
    pushforward Γ readDiagonal = tensorPow t P

/-- The injectable-marginal prescriptions of paper Definition 2.4: every injectable set has
the corresponding marginal of `P`. -/
def InjectableMarginals (t : ℕ) (Γ : Assign t → ℝ) (P : ThreeBit → ℝ) : Prop :=
  ∀ S : Finset (Obs t), Injectable S →
    pushforward Γ (restrictAssign S) = pushforward P (partyRead S)

/-- The ancestral-independence prescriptions of paper Definition 2.4: every union of
pairwise ancestrally independent injectable sets has the product of the corresponding
marginals. The union is presented as a finite family, whose joint restriction law is
required to factor. -/
def AncestralProducts (t : ℕ) (Γ : Assign t → ℝ) (P : ThreeBit → ℝ) : Prop :=
  ∀ (n : ℕ) (S : Fin n → Finset (Obs t)), (∀ m, Injectable (S m)) →
    (∀ m m', m ≠ m' → AncestrallyIndependent (S m) (S m')) →
    pushforward Γ (fun ω m => restrictAssign (S m) ω)
      = fun φ : ∀ m : Fin n, (S m) → Bool =>
          ∏ m : Fin n, pushforward P (partyRead (S m)) (φ m)

/-- Paper Definition 2.4: the ancestral-independence feasible set `I^AI_t`. -/
def AIFeasible (t : ℕ) (P : ThreeBit → ℝ) : Prop :=
  ∃ Γ : Assign t → ℝ, IsLaw Γ ∧ SymmetricLaw t Γ ∧
    pushforward Γ readDiagonal = tensorPow t P ∧
    InjectableMarginals t Γ P ∧ AncestralProducts t Γ P

/-! ## The defect-cube witness -/

/-- The per-root Bernoulli weights: defects are `Bern(ε)`, private bits are `Bern(s)`. -/
def rootWeight (t : ℕ) (ε s : ℝ) : Root t → Bool → ℝ
  | Sum.inl _ => bern ε
  | Sum.inr _ => bern s

/-- The joint law of the independent root bits of the defect cube. -/
def rootLaw (t : ℕ) (ε s : ℝ) : (Root t → Bool) → ℝ := prodLaw (rootWeight t ε s)

/-- Paper Section 5.1: the defect-cube law `Γ_t`, the pushforward of the independent defect
and private bits under the output map (eq:outputs). Unfolding `pushforward` and `prodLaw`
gives the explicit finite sum of product weights of paper equation (eq:table):
`Γ_t(w) = ∑_{x : outputsOf x = w} ∏_{roots} bern _ (x _)`. -/
def defectLaw (t : ℕ) (ε s : ℝ) : Assign t → ℝ :=
  pushforward (rootLaw t ε s) outputsOf

/-! ## First rejecting order

Paper Section 2.3: `t_min^H(P) = min {t ≥ 1 : P ∉ I^H_t}`. Formalized as `Nat.sInf`, which
returns the junk value `0` when the set is empty. The set is nonempty exactly when some
finite order rejects `P`; that this happens for every incompatible `P` is the asymptotic
completeness of the hierarchy, which is quoted from Navascués–Wolfe in the paper and is not
formalized here. Every statement about `t_min` below therefore either exhibits a rejecting
order or assumes one. -/

/-- `t_min^NW(P)`, the first order of the Navascués–Wolfe hierarchy that rejects `P`. -/
def tminNW (P : ThreeBit → ℝ) : ℕ := sInf {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t P}

/-- `t_min^AI(P)`, the first order of the ancestral-independence hierarchy that rejects `P`. -/
def tminAI (P : ThreeBit → ℝ) : ℕ := sInf {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t P}

end

end TriangleInflation
