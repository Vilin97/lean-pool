/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt

/-!
# Polydiscs and distinguished boundaries

Geometry for the polydisc Cauchy formula. Equal-radius polydiscs use the supremum norm; these
are not Euclidean balls. Origin-centred open and closed polydiscs are complete Reinhardt sets.
Containment of the closed polydisc determined by each point's moduli characterizes the complete
Reinhardt property.

## Notation

`polydisc c r` and `closedPolydisc c r` are products of coordinate balls of radii `r i`. The
definitions and their elementary topology allow any family of pseudo-metric spaces as factors; the
Reinhardt and torus statements are specific to `ℂ`. The equal-radius case `r = fun _ => R` coincides
with the sup-norm ball; see `polydisc_const_eq_ball` and `closedPolydisc_eq_closedBall`. The
distinguished boundary is parametrized by `torusMap`.

## Main results

`isCompleteReinhardt_iff_closedPolydisc_subset` characterizes complete Reinhardt sets.
`polydisc_const_eq_ball` identifies equal positive radii with the open sup-norm ball.
`closure_polydisc` identifies the closure of a positive-radius open polydisc with the
corresponding closed polydisc.
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-!
### Closed polydiscs
-/

/-- An open polydisc with a separate radius in each coordinate: the product of the open balls
`ball (c i) (r i)`. The factors may be any pseudo-metric spaces; the several-complex-variables
theory uses `X i = ℂ`. -/
@[expose] def polydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    (c : ∀ i, X i) (r : ι → ℝ) : Set (∀ i, X i) :=
  Set.pi univ fun i => ball (c i) (r i)

/-- A closed polydisc with a separate radius in each coordinate: the product of the closed balls
`closedBall (c i) (r i)`. -/
@[expose] def closedPolydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    (c : ∀ i, X i) (r : ι → ℝ) : Set (∀ i, X i) :=
  Set.pi univ fun i => closedBall (c i) (r i)

/-- Membership in a polydisc is a coordinatewise strict distance bound. -/
@[simp] lemma mem_polydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    {c z : ∀ i, X i} {r : ι → ℝ} :
    z ∈ polydisc c r ↔ ∀ i, dist (z i) (c i) < r i := by
  simp [polydisc, mem_ball]

/-- Membership in a closed polydisc is a coordinatewise non-strict distance bound. -/
@[simp] lemma mem_closedPolydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    {c z : ∀ i, X i} {r : ι → ℝ} :
    z ∈ closedPolydisc c r ↔ ∀ i, dist (z i) (c i) ≤ r i := by
  simp [closedPolydisc, mem_closedBall]

/-- Every origin-centred open polydisc is complete Reinhardt, even with nonpositive radii. -/
theorem isCompleteReinhardt_polydisc {ι : Type*} (r : ι → ℝ) :
    IsCompleteReinhardt (polydisc (0 : ι → ℂ) r) := by
  intro z hz w hw
  simp only [mem_polydisc, Pi.zero_apply, dist_zero_right] at hz ⊢
  exact fun i => (hw i).trans_lt (hz i)

/-- Every origin-centred closed polydisc is complete Reinhardt, including degenerate ones. -/
theorem isCompleteReinhardt_closedPolydisc {ι : Type*} (r : ι → ℝ) :
    IsCompleteReinhardt (closedPolydisc (0 : ι → ℂ) r) := by
  intro z hz w hw
  simp only [mem_closedPolydisc, Pi.zero_apply, dist_zero_right] at hz ⊢
  exact fun i => (hw i).trans (hz i)

/-- Completeness means containing the closed polydisc determined by each point's moduli. -/
theorem isCompleteReinhardt_iff_closedPolydisc_subset {ι : Type*}
    {U : Set (ι → ℂ)} :
    IsCompleteReinhardt U ↔
      ∀ z ∈ U, closedPolydisc 0 (fun i => ‖z i‖) ⊆ U := by
  simp only [IsCompleteReinhardt, Set.subset_def, mem_closedPolydisc,
    Pi.zero_apply, dist_zero_right]

/-- An origin-centred open polydisc has independent coordinate rotation symmetry. -/
theorem isReinhardt_polydisc {ι : Type*} (r : ι → ℝ) :
    IsReinhardt (polydisc (0 : ι → ℂ) r) :=
  (isCompleteReinhardt_polydisc r).isReinhardt

/-- An origin-centred closed polydisc has independent coordinate rotation symmetry. -/
theorem isReinhardt_closedPolydisc {ι : Type*} (r : ι → ℝ) :
    IsReinhardt (closedPolydisc (0 : ι → ℂ) r) :=
  (isCompleteReinhardt_closedPolydisc r).isReinhardt

/-- Open origin-centred polydiscs are logarithmically convex, with arbitrary real radii. -/
theorem isLogarithmicallyConvex_polydisc {ι : Type*} (r : ι → ℝ) :
    IsLogarithmicallyConvex (polydisc (0 : ι → ℂ) r) := by
  intro x hx y hy a b ha hb hab
  simp only [logarithmicImage, Set.mem_ofPred_eq, mem_polydisc,
    Pi.zero_apply, dist_zero_right] at hx hy ⊢
  intro i
  have h := (convexOn_exp.convex_lt (r i))
    ⟨Set.mem_univ _, by simpa using hx i⟩ ⟨Set.mem_univ _, by simpa using hy i⟩ ha hb hab
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.norm_of_nonneg (Real.exp_nonneg _)] using h.2

/-- Closed origin-centred polydiscs are logarithmically convex, including degenerate ones. -/
theorem isLogarithmicallyConvex_closedPolydisc {ι : Type*} (r : ι → ℝ) :
    IsLogarithmicallyConvex (closedPolydisc (0 : ι → ℂ) r) := by
  intro x hx y hy a b ha hb hab
  simp only [logarithmicImage, Set.mem_ofPred_eq, mem_closedPolydisc,
    Pi.zero_apply, dist_zero_right] at hx hy ⊢
  intro i
  have h := (convexOn_exp.convex_le (r i))
    ⟨Set.mem_univ _, by simpa using hx i⟩ ⟨Set.mem_univ _, by simpa using hy i⟩ ha hb hab
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.norm_of_nonneg (Real.exp_nonneg _)] using h.2

/-- A finite-dimensional polydisc is open. -/
theorem isOpen_polydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    [Finite ι] (c : ∀ i, X i) (r : ι → ℝ) :
    IsOpen (polydisc c r) := by
  change IsOpen (Set.pi univ fun i => ball (c i) (r i))
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_ball)

/-- A closed polydisc in a product of proper spaces is compact, by the product compactness
theorem. -/
theorem isCompact_closedPolydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    [∀ i, ProperSpace (X i)] (c : ∀ i, X i) (r : ι → ℝ) :
    IsCompact (closedPolydisc c r) :=
  isCompact_univ_pi fun i => isCompact_closedBall (c i) (r i)

/-- The closure of a positive-radius polydisc is the corresponding closed polydisc. -/
theorem closure_polydisc {ι : Type*} (c : ι → ℂ) {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) :
    closure (polydisc c r) = closedPolydisc c r := by
  simp only [polydisc, closedPolydisc, closure_pi_set,
    closure_ball _ (ne_of_gt (hr _))]

/-- In finite coordinates, equal positive radii give the open ball for the supremum norm. -/
theorem polydisc_const_eq_ball {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    [Fintype ι] (c : ∀ i, X i) {R : ℝ} (hR : 0 < R) : polydisc c (fun _ => R) = ball c R :=
  (ball_pi c hR).symm

/-- Enlarging every radius enlarges the polydisc. -/
theorem polydisc_mono {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    (c : ∀ i, X i) {r s : ι → ℝ} (hrs : ∀ i, r i ≤ s i) : polydisc c r ⊆ polydisc c s := by
  intro z hz
  exact mem_polydisc.mpr fun i => (mem_polydisc.mp hz i).trans_le (hrs i)

/-- Strictly smaller closed coordinate discs lie in the larger open polydisc. -/
theorem closedPolydisc_subset_polydisc {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    (c : ∀ i, X i) {r s : ι → ℝ} (hrs : ∀ i, r i < s i) :
    closedPolydisc c r ⊆ polydisc c s := by
  intro z hz
  exact mem_polydisc.mpr fun i => (mem_closedPolydisc.mp hz i).trans_lt (hrs i)

/-- The torus parametrization with separate coordinate radii is continuous. -/
theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap c r) := by
  apply continuous_pi
  intro i
  simp only [torusMap]
  fun_prop

/-- Each torus coordinate has the prescribed nonnegative radius. -/
theorem norm_torusMap_sub {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c r θ i - c i‖ = r i := by
  simp [torusMap, abs_of_nonneg (hr i)]

/-- A torus with nonnegative radii belongs to its closed polydisc. -/
theorem torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) (θ : Fin n → ℝ) :
    torusMap c r θ ∈ closedPolydisc c r := by
  exact mem_closedPolydisc.mpr fun i => by
    rw [dist_eq_norm, norm_torusMap_sub hr]

/-- A Cauchy kernel has no pole on a coordinate circle when evaluated inside the polydisc. -/
theorem torusMap_apply_ne_of_norm_sub_lt {n : ℕ} {c w : Fin n → ℂ}
    {r : Fin n → ℝ} {θ : Fin n → ℝ} {i : Fin n}
    (hr : ∀ i, 0 < r i) (hw : ‖w i - c i‖ < r i) : torusMap c r θ i ≠ w i := by
  intro h
  have H := norm_torusMap_sub (c := c) (fun j => (hr j).le) θ i
  rw [h] at H
  exact hw.ne H

/-- Membership of a coordinate and the tail gives membership of the full polydisc. -/
theorem cons_mem_closedPolydisc {n : ℕ} {c : Fin (n + 1) → ℂ}
    {r : Fin (n + 1) → ℝ} {x : ℂ} {y : Fin n → ℂ}
    (hx : x ∈ closedBall (c 0) (r 0))
    (hy : y ∈ closedPolydisc (c ∘ Fin.succ) (r ∘ Fin.succ)) :
    Fin.cons x y ∈ closedPolydisc c r := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simpa using hx
  · intro j
    simpa using hy j (mem_univ _)

/-- An equal-radius closed polydisc is the closed ball for the supremum norm. -/
theorem closedPolydisc_eq_closedBall {ι : Type*} {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)]
    [Fintype ι] {c : ∀ i, X i} {R : ℝ} (hR : 0 ≤ R) :
    closedPolydisc c (fun _ => R) = closedBall c R :=
  (closedBall_pi c hR).symm

/-- The standard equal-radius torus parametrization is continuous. -/
theorem continuous_torusMap_const {n : ℕ} (c : Fin n → ℂ) (R : ℝ) :
    Continuous (torusMap c (fun _ => R)) :=
  continuous_pi fun i => by
    simp only [torusMap]
    fun_prop

/-- No natural-number power of `2 * π * I` vanishes. -/
theorem _root_.Complex.two_pi_I_pow_ne_zero (n : ℕ) : ((2 * π * I : ℂ) ^ n) ≠ 0 :=
  pow_ne_zero _ two_pi_I_ne_zero

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
