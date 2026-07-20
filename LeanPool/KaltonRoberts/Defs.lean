/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Definitions for the Kalton–Roberts formalization

This file contains the core definitions used throughout the formalization of
the companion paper.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Aesop

/-!
# Definitions for the Kalton-Roberts formalization

Core definitions used throughout the formalization of the companion paper.
-/

namespace KaltonRoberts

open Finset BigOperators

/-! ## Basic definitions from Section 1 -/

/-- A function `f : Finset U → ℝ` is `Δ`-additive if `f ∅ = 0` and
`|f A + f B − f (A ∪ B)| ≤ Δ` for every pair of disjoint finite subsets `A, B`.
**Reference**: Equation (1) in Section 1 of the companion paper. -/
def IsApproxAdditive {U : Type*} [DecidableEq U]
    (f : Finset U → ℝ) (Δ : ℝ) : Prop :=
  f ∅ = 0 ∧ ∀ A B : Finset U, Disjoint A B → |f A + f B - f (A ∪ B)| ≤ Δ

/-- A function on an abstract Boolean algebra is `Δ`-additive if it vanishes at
bottom and is additive up to `Δ` on disjoint joins.

This is the set-algebra formulation from Equation (1), with a set algebra
represented by its Boolean algebra of events. A concrete algebra of subsets is
the subtype of a `BooleanSubalgebra (Set Ω)`. -/
def IsApproxAdditiveBA {α : Type*} [BooleanAlgebra α]
    (f : α → ℝ) (Δ : ℝ) : Prop :=
  f ⊥ = 0 ∧ ∀ A B : α, Disjoint A B → |f A + f B - f (A ⊔ B)| ≤ Δ

/-- A finitely additive signed measure on a Boolean algebra. -/
def IsFinitelyAdditiveBA {α : Type*} [BooleanAlgebra α] (μ : α → ℝ) : Prop :=
  μ ⊥ = 0 ∧ ∀ A B : α, Disjoint A B → μ (A ⊔ B) = μ A + μ B

/-- An additive signed measure on `2^U` is identified with a function
`A ↦ ∑ i ∈ A, a i` for some weight function `a : U → ℝ`.
**Reference**: paragraph after Lemma 1.2 in Section 1 of
the companion paper. -/
def additiveFunction {U : Type*} (a : U → ℝ) :
    Finset U → ℝ :=
  fun A => ∑ i ∈ A, a i

/-- The `ℓ∞`-distance from `f` to the subspace of additive signed measures
on `2^U`.
**Reference**: last paragraph of Section 1 in the companion paper,
where `M := ‖f‖_∞ = dist_∞(f, L)` after subtracting a closest additive
approximant. -/
noncomputable def distToAdditive {U : Type*}
    (f : Finset U → ℝ) : ℝ :=
  ⨅ a : U → ℝ, ⨆ S : Finset U, |f S - additiveFunction a S|

/-- The deficit of a set `A` relative to `f` and the value `M`: this is
`M − f(A)`. Used throughout Section 2–5 of the companion paper. -/
def deficit {U : Type*}
    (f : Finset U → ℝ) (M : ℝ) (A : Finset U) : ℝ := M - f A

/-- The surplus of a set `A` relative to `f` and the value `M`: this is
`M + f(A)`. Used throughout Section 2–5 of the companion paper. -/
def surplus {U : Type*}
    (f : Finset U → ℝ) (M : ℝ) (A : Finset U) : ℝ := M + f A

/-- The Kalton–Roberts constant `K_KR` is the infimum of all `C ≥ 0` such that
for every Boolean algebra of sets/events and every `1`-additive function
`f : α → ℝ`, there exists a finitely additive signed measure `μ` with
`sup |f − μ| ≤ C`.

This abstract Boolean-algebra formulation captures the paper's statement for
arbitrary set algebras: a set algebra is a Boolean subalgebra of `Set Ω`.
**Reference**: paragraph after Equation (1) in Section 1 of
the companion paper. -/
noncomputable def krConstant : ℝ :=
  sInf { C : ℝ | 0 ≤ C ∧
    ∀ (α : Type) [BooleanAlgebra α] (f : α → ℝ),
      IsApproxAdditiveBA f 1 →
        ∃ μ : α → ℝ, IsFinitelyAdditiveBA μ ∧ ∀ A : α, |f A - μ A| ≤ C }

/-! ## Expander definition from Section 3 -/

/-- An `(α, r, θ)`-expander for parameter `k` is a bipartite multigraph
`G = (V, W; E)` with `|V| = 2k`, `|W| = 2θk`, every vertex in `V` having
degree `r`, such that every subset `S ⊆ V` with `|S| ≤ 2αk` has at least
`|S|` distinct neighbours in `W`.

`ExpandersExist α r θ` asserts that such expanders exist for all sufficiently
large admissible `k`.

**Reference**: paragraph before Lemma 3.2 in Section 3 of
the companion paper. -/
def ExpandersExist (α : ℚ) (r : ℕ) (θ : ℚ) : Prop :=
  ∀ᶠ (k : ℕ) in Filter.atTop,
    ∃ (V W : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype W) (_ : DecidableEq W)
      (neighbors : V → Finset W),
      Fintype.card V = 2 * k ∧
      Fintype.card W = ⌈(2 : ℚ) * θ * ↑k⌉₊ ∧
      (∀ v : V, (neighbors v).card = r) ∧
      ∀ (S : Finset V),
        S.card ≤ ⌈(2 : ℚ) * α * ↑k⌉₊ →
          (S.biUnion neighbors).card ≥ S.card

/-! ## Strong expander witness (Section 3, refined interface) -/

/-- Edge-neighbor set of vertex `v` in a bipartite graph with labelled edges. -/
def edgeNeighbors {V W : Type*} [DecidableEq W]
    {r : ℕ} (edge : V → Fin r → W) (v : V) : Finset W :=
  Finset.univ.image (edge v)

/-- A concrete finite expander witness with `r` labelled edges per left vertex.

This represents a bipartite multigraph `G = (V, W; E)` where each left vertex
`v ∈ V` has exactly `r` labelled edges `edge v 0, …, edge v (r-1)` going to
right vertices in `W`. The expansion property guarantees that small left-subsets
have many distinct right-neighbors.

**Reference**: paragraph before Lemma 3.2 in Section 3 of
the companion paper. -/
structure FiniteExpanderWitness (r : ℕ) where
  /-- Left vertex type. -/
  V : Type
  /-- Right vertex type. -/
  W : Type
  /-- Fintype instance for V. -/
  instFintypeV : Fintype V
  /-- DecidableEq instance for V. -/
  instDecEqV : DecidableEq V
  /-- Fintype instance for W. -/
  instFintypeW : Fintype W
  /-- DecidableEq instance for W. -/
  instDecEqW : DecidableEq W
  /-- The `r` labelled edges from each left vertex to right vertices. -/
  edge : V → Fin r → W
  /-- V is nonempty. -/
  hV_pos : 0 < @Fintype.card V instFintypeV
  /-- Right coverage: every right vertex is hit by at least one edge. -/
  right_coverage : ∀ w : W, ∃ v : V, ∃ e : Fin r, edge v e = w
  /-- Expansion threshold (typically `⌈2αk⌉`). -/
  expansionThreshold : ℕ
  /-- Expansion property: every subset of `V` of size at most `expansionThreshold`
      has at least as many distinct right-neighbors. -/
  expansion : ∀ (S : Finset V),
    S.card ≤ expansionThreshold →
    (@Finset.biUnion _ _ instDecEqW S
      (fun v => @edgeNeighbors V W instDecEqW r edge v)).card ≥ S.card

attribute [instance] FiniteExpanderWitness.instFintypeV FiniteExpanderWitness.instDecEqV
  FiniteExpanderWitness.instFintypeW FiniteExpanderWitness.instDecEqW

/-- `StrongExpandersExist α r θ` asserts that there exists a positive
admissibility step `step` such that for all sufficiently large `k`
divisible by `step`, there exists a `FiniteExpanderWitness` with:
- `|V| = 2k`,
- `|W| = 2θk` (exact integer, requiring admissibility),
- expansion threshold `⌈2αk⌉₊`,
- right coverage,
- labelled `r`-edges.

The step/divisibility formulation corresponds to the paper's assertion
that expanders exist for all sufficiently large *admissible* `k`, where
admissible sizes form an infinite arithmetic progression.

**Reference**: Section 3 and Lemma 4.1 of the companion paper. -/
def StrongExpandersExist (α : ℚ) (r : ℕ) (θ : ℚ) : Prop :=
  ∃ (step : ℕ), 0 < step ∧ ∀ᶠ (k : ℕ) in Filter.atTop,
    step ∣ k →
    ∃ (E : FiniteExpanderWitness r),
      @Fintype.card E.V E.instFintypeV = 2 * k ∧
      (@Fintype.card E.W E.instFintypeW : ℚ) = 2 * θ * ↑k ∧
      E.expansionThreshold = ⌈(2 : ℚ) * α * ↑k⌉₊

/-
Note: `StrongExpandersExist` does NOT directly imply `ExpandersExist` because
the labelled-edge model allows parallel edges (`edge v e₁ = edge v e₂`),
so the number of distinct neighbors may be less than `r`. The original
`ExpandersExist` required `(neighbors v).card = r` (r distinct neighbors).

In practice, the pipeline should be updated to use `StrongExpandersExist`
directly. The original `ExpandersExist` is retained only for backward
compatibility with the existing spine proofs.
-/

/-! ## Entropy function from Section 4 -/

/-- The function `h(a, b) = a log a − b log b − (a − b) log(a − b)` used in
the definition of `Φ_{r,θ}`.
**Reference**: paragraph before Equation (6) in Section 4 of
the companion paper. -/
noncomputable def hEntropy (a b : ℝ) : ℝ :=
  a * Real.log a - b * Real.log b - (a - b) * Real.log (a - b)

/-- The function `Φ_{r,θ}(x) = h(1,x) + h(θ,x) + h(rx/θ, rx) − h(r, rx)` from
Equation (6) in Section 4 of the companion paper. -/
noncomputable def Phi (r θ x : ℝ) : ℝ :=
  hEntropy 1 x + hEntropy θ x + hEntropy (r * x / θ) (r * x) - hEntropy r (r * x)

/-- The second derivative `Φ''_{r,θ}(x) = (r−2)/x + (r−1)/(1−x) − 1/(θ−x)`,
from Equation (8) in Section 4 of the companion paper. -/
noncomputable def Phi'' (r θ x : ℝ) : ℝ :=
  (r - 2) / x + (r - 1) / (1 - x) - 1 / (θ - x)

/-! ## Numerical constants from Section 5 -/

/-- The case-split parameter `q₀ = 7437/15625`.
**Reference**: Equation (9) in Section 5 of the companion paper. -/
def q₀ : ℚ := 7437 / 15625

/-- The complementary parameter `p₀ = 1 − q₀ = 8188/15625`.
**Reference**: Equation (9) in Section 5 of the companion paper. -/
def p₀ : ℚ := 8188 / 15625

/-- The frequency cap in Case 1: `α₁ = 1003/10000`.
**Reference**: Equation (9) in Section 5 of the companion paper. -/
def α₁ : ℚ := 1003 / 10000

/-- The frequency cap in Case 2: `α₂ = 47/625`.
**Reference**: Equation (9) in Section 5 of the companion paper. -/
def α₂ : ℚ := 47 / 625

/-- The mixing parameter `τ₁` from Equation (10) in Section 5 of
the companion paper. Satisfies
`(1 − τ₁) q₀³ + τ₁ q₀⁴ = α₁`. -/
def τ₁ : ℚ := (q₀ ^ 3 - α₁) / (q₀ ^ 3 - q₀ ^ 4)

/-- The mixing parameter `τ₂` from Equation (10) in Section 5 of
the companion paper. Satisfies
`(1 − τ₂) p₀⁴ + τ₂ p₀⁵ = α₂`. -/
def τ₂ : ℚ := (p₀ ^ 4 - α₂) / (p₀ ^ 4 - p₀ ^ 5)

/-- The Case 1 bound `C₁` from Equation (14) in Section 5 of
the companion paper. -/
def C₁ : ℚ := 23662339508853784054849 / 1192830849380162250000

/-- The Case 2 bound `C₂`, which is the final headline constant, from
Equation (17) in Section 5 of the companion paper. -/
def C₂ : ℚ := 694198146664396294486127753 / 34994834677886019996000000

/-- The simplified upper bound `9919/500 = 19.838`, from the statement of
Theorem 1.1 in Section 1 of the companion paper. -/
def krUpper : ℚ := 9919 / 500

/-! ## Dual certificate structure (Section 2) -/

/-- A dual certificate `λ` for best `ℓ∞`-approximation.
**Reference**: Lemma 2.1 in Section 2 of the companion paper. -/
structure DualCertificate {U : Type*} [DecidableEq U] [Fintype U]
    (f : Finset U → ℝ) (M : ℝ) where
  /-- The signed measure `λ` on `2^U`. -/
  lam : Finset U → ℝ
  /-- (i) `‖λ‖₁ = 1`. -/
  norm_one : ∑ S : Finset U, |lam S| = 1
  /-- (ii) Zero item marginals: `∑_{A ∋ i} λ_A = 0` for all `i ∈ U`. -/
  zero_marginals : ∀ i : U,
    (Finset.univ.filter (fun S => i ∈ S)).sum lam = 0
  /-- (iii) `λ_A > 0` only when `f(A) = M`. -/
  pos_support : ∀ S : Finset U, 0 < lam S → f S = M
  /-- (iii) `λ_A < 0` only when `f(A) = −M`. -/
  neg_support : ∀ S : Finset U, lam S < 0 → f S = -M

end KaltonRoberts
