/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# Polydiscs and distinguished boundaries

Geometry for the polydisc Cauchy formula. Equal-radius polydiscs use the supremum norm;
these are not Euclidean balls.
-/

@[expose] public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Classical ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ### Closed polydiscs -/

/-- The closed polydisc of equal radii.  For `0 ≤ R` this coincides with the closed ball for the
sup-norm. -/
def closedPolydisc {ι : Type*} (c : ι → ℂ) (R : ℝ) : Set (ι → ℂ) :=
  Set.pi univ fun i => closedBall (c i) R

/-- An open polydisc with a separate radius in each coordinate. -/
def polydiscWithRadii {ι : Type*} (c : ι → ℂ) (r : ι → ℝ) : Set (ι → ℂ) :=
  Set.pi univ fun i => ball (c i) (r i)

/-- A closed polydisc with a separate radius in each coordinate. -/
def closedPolydiscWithRadii {ι : Type*} (c : ι → ℂ) (r : ι → ℝ) : Set (ι → ℂ) :=
  Set.pi univ fun i => closedBall (c i) (r i)

/-- Membership in a polydisc is a coordinatewise strict distance bound. -/
@[simp] lemma mem_polydiscWithRadii {ι : Type*} {c z : ι → ℂ} {r : ι → ℝ} :
    z ∈ polydiscWithRadii c r ↔ ∀ i, dist (z i) (c i) < r i := by
  simp [polydiscWithRadii, mem_ball]

/-- Membership in a closed polydisc is a coordinatewise weak distance bound. -/
@[simp] lemma mem_closedPolydiscWithRadii {ι : Type*} {c z : ι → ℂ} {r : ι → ℝ} :
    z ∈ closedPolydiscWithRadii c r ↔ ∀ i, dist (z i) (c i) ≤ r i := by
  simp [closedPolydiscWithRadii, mem_closedBall]

/-- A finite-dimensional polydisc is open. -/
lemma isOpen_polydiscWithRadii {ι : Type*} [Finite ι] (c : ι → ℂ) (r : ι → ℝ) :
    IsOpen (polydiscWithRadii c r) := by
  change IsOpen (Set.pi univ fun i => ball (c i) (r i))
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_ball)

/-- A closed polydisc is compact, by the product compactness theorem. -/
lemma isCompact_closedPolydiscWithRadii {ι : Type*} (c : ι → ℂ) (r : ι → ℝ) :
    IsCompact (closedPolydiscWithRadii c r) :=
  isCompact_univ_pi fun i => isCompact_closedBall (c i) (r i)

/-- The closure of a positive-radius polydisc is the corresponding closed polydisc. -/
lemma closure_polydiscWithRadii {ι : Type*} (c : ι → ℂ) {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) :
    closure (polydiscWithRadii c r) = closedPolydiscWithRadii c r := by
  simp only [polydiscWithRadii, closedPolydiscWithRadii, closure_pi_set,
    closure_ball _ (ne_of_gt (hr _))]

/-- Equal coordinate radii recover the original closed-polydisc definition. -/
@[simp] lemma closedPolydiscWithRadii_const {ι : Type*} (c : ι → ℂ) (R : ℝ) :
    closedPolydiscWithRadii c (fun _ => R) = closedPolydisc c R := rfl

/-- In finite coordinates, equal positive radii give the open ball for the supremum norm. -/
lemma polydiscWithRadii_const_eq_ball {ι : Type*} [Fintype ι] (c : ι → ℂ)
    {R : ℝ} (hR : 0 < R) : polydiscWithRadii c (fun _ => R) = ball c R :=
  (ball_pi c hR).symm

/-- Enlarging every radius enlarges the polydisc. -/
lemma polydiscWithRadii_mono {ι : Type*} (c : ι → ℂ) {r s : ι → ℝ}
    (hrs : ∀ i, r i ≤ s i) : polydiscWithRadii c r ⊆ polydiscWithRadii c s := by
  intro z hz
  exact mem_polydiscWithRadii.mpr fun i => (mem_polydiscWithRadii.mp hz i).trans_le (hrs i)

/-- Strictly smaller closed coordinate discs lie in the larger open polydisc. -/
lemma closedPolydiscWithRadii_subset_polydiscWithRadii {ι : Type*} (c : ι → ℂ)
    {r s : ι → ℝ} (hrs : ∀ i, r i < s i) :
    closedPolydiscWithRadii c r ⊆ polydiscWithRadii c s := by
  intro z hz
  exact mem_polydiscWithRadii.mpr fun i => (mem_closedPolydiscWithRadii.mp hz i).trans_lt (hrs i)

/-- The torus parametrization with separate coordinate radii is continuous. -/
lemma continuous_torusMapWithRadii {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap c r) := by
  apply continuous_pi
  intro i
  simp only [torusMap]
  fun_prop

/-- Each torus coordinate has the prescribed nonnegative radius. -/
lemma torusMap_coord_normWithRadii {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c r θ i - c i‖ = r i := by
  simp [torusMap, abs_of_nonneg (hr i)]

/-- A torus with nonnegative radii belongs to its closed polydisc. -/
lemma torusMap_mem_closedPolydiscWithRadii {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) (θ : Fin n → ℝ) :
    torusMap c r θ ∈ closedPolydiscWithRadii c r := by
  exact mem_closedPolydiscWithRadii.mpr fun i => by
    rw [dist_eq_norm, torusMap_coord_normWithRadii hr]

/-- A Cauchy kernel has no pole on a coordinate circle when evaluated inside the polydisc. -/
lemma cauchyKernel_ne_zero_on_torusWithRadii {n : ℕ} {c w : Fin n → ℂ}
    {r : Fin n → ℝ} {θ : Fin n → ℝ} {i : Fin n}
    (hr : ∀ i, 0 < r i) (hw : ‖w i - c i‖ < r i) : torusMap c r θ i ≠ w i := by
  intro h
  have H := torusMap_coord_normWithRadii (c := c) (fun j => (hr j).le) θ i
  rw [h] at H
  exact hw.ne H

/-- Membership of a coordinate and the tail gives membership of the full polydisc. -/
lemma cons_mem_closedPolydiscWithRadii {n : ℕ} {c : Fin (n + 1) → ℂ}
    {r : Fin (n + 1) → ℝ} {x : ℂ} {y : Fin n → ℂ}
    (hx : x ∈ closedBall (c 0) (r 0))
    (hy : y ∈ closedPolydiscWithRadii (c ∘ Fin.succ) (r ∘ Fin.succ)) :
    Fin.cons x y ∈ closedPolydiscWithRadii c r := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simpa using hx
  · intro j
    simpa using hy j (mem_univ _)

/-- Membership in an equal-radius closed polydisc is coordinatewise membership in the
corresponding closed balls. -/
lemma mem_closedPolydisc {n : ℕ} {c z : Fin n → ℂ} {R : ℝ} :
    z ∈ closedPolydisc c R ↔ ∀ i, z i ∈ closedBall (c i) R := by
  simp [closedPolydisc]

/-- An equal-radius closed polydisc is the closed ball for the supremum norm. -/
lemma closedPolydisc_eq_closedBall {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    closedPolydisc c R = closedBall c R :=
  (closedBall_pi c hR).symm

/-- The standard torus with nonnegative radius lies in its associated closed polydisc. -/
lemma torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) : torusMap c (fun _ => R) θ ∈ closedPolydisc c R := by
  intro i _
  simp [torusMap, mem_closedBall, dist_eq_norm, abs_of_nonneg hR]

/-- Adjoining a point in the first coordinate ball to a point in the tail polydisc produces a
point in the full polydisc. -/
lemma cons_mem_closedPolydisc {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ}
    {y : Fin n → ℂ} (hx : x ∈ closedBall (c 0) R)
    (hy : y ∈ closedPolydisc (c ∘ Fin.succ) R) :
    Fin.cons x y ∈ closedPolydisc c R := by
  intro i _
  refine Fin.cases ?_ ?_ i
  · simpa [Fin.cons_zero] using hx
  · intro j
    simpa [Fin.cons_succ] using hy j (mem_univ _)

/-- The standard equal-radius torus parametrization is continuous. -/
lemma continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (R : ℝ) :
    Continuous (torusMap c (fun _ => R)) :=
  continuous_pi fun i => by
    simp only [torusMap]
    fun_prop

/-- No natural-number power of `2 * π * I` vanishes. -/
lemma two_pi_I_pow_ne_zero (n : ℕ) : ((2 * π * I : ℂ) ^ n) ≠ 0 :=
  pow_ne_zero _ two_pi_I_ne_zero

/-- Every coordinate of the standard equal-radius torus has the prescribed distance from its
center. -/
lemma torusMap_coord_norm {n : ℕ} {c : Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => R) θ i - c i‖ = R := by
  simp [torusMap, abs_of_nonneg hR]

/-- A point strictly inside a coordinate disc does not meet the corresponding coordinate circle,
so its Cauchy kernel has no pole on the torus. -/
lemma cauchyKernel_ne_zero_on_torus {n : ℕ} {c w : Fin n → ℂ} {R : ℝ} {θ : Fin n → ℝ}
    {i : Fin n} (hR : 0 < R) (hw : ‖w i - c i‖ < R) :
    torusMap c (fun _ => R) θ i ≠ w i := by
  intro h
  have : ‖torusMap c (fun _ => R) θ i - c i‖ = R := torusMap_coord_norm hR.le θ i
  rw [h] at this
  exact hw.not_ge this.ge

end SeveralComplexVariables

end
