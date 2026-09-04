/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The full-dimensional model of the standard simplex

The standard simplex on `Option ι` naturally lives in the affine hyperplane
whose coordinates sum to one.  For measure-theoretic arguments it is more
convenient to delete the coordinate indexed by `none`.  The resulting
full-dimensional simplex consists of the nonnegative vectors whose coordinate
sum is at most one; the deleted coordinate is `1 - ∑ i, x i`.

This file records the elementary geometry needed to state the simplex
halfspace argument: the simplex, its centroid, and the value at that centroid
of the linear functional determined by a coefficient vector.
-/

open scoped BigOperators ENNReal

open MeasureTheory Set

namespace Feige

variable {ι : Type*} [Fintype ι]

/-- The full-dimensional standard simplex in `ι → ℝ`, obtained by deleting
one coordinate from the standard simplex on `Option ι`. -/
def fullSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

theorem mem_fullSimplex_iff {x : ι → ℝ} :
    x ∈ fullSimplex ι ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 :=
  Iff.rfl

theorem convex_fullSimplex : Convex ℝ (fullSimplex ι) := by
  intro x hx y hy a b ha hb hab
  rw [mem_fullSimplex_iff] at hx hy ⊢
  constructor
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa using hab

theorem isClosed_fullSimplex : IsClosed (fullSimplex ι) := by
  let coordinateSum : (ι → ℝ) → ℝ := fun x ↦ ∑ i, x i
  have hsum : Continuous coordinateSum :=
    continuous_finsetSum _ fun i _ ↦ continuous_apply i
  have hnonneg : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [← Set.mem_Ici]
    exact isClosed_Ici
  have hsum_le : IsClosed {x : ι → ℝ | ∑ i, x i ≤ 1} :=
    isClosed_Iic.preimage hsum
  exact hnonneg.inter hsum_le

theorem fullSimplex_subset_Icc :
    fullSimplex ι ⊆ Set.Icc (0 : ι → ℝ) 1 := by
  intro x hx
  rw [mem_fullSimplex_iff] at hx
  constructor
  · exact hx.1
  · intro i
    calc
      x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)
      _ ≤ 1 := hx.2

theorem isCompact_fullSimplex : IsCompact (fullSimplex ι) :=
  IsCompact.of_isClosed_subset isCompact_Icc isClosed_fullSimplex fullSimplex_subset_Icc

theorem measurableSet_fullSimplex : MeasurableSet (fullSimplex ι) :=
  isClosed_fullSimplex.measurableSet

theorem volume_fullSimplex_lt_top :
    volume (fullSimplex ι) < ∞ :=
  isCompact_fullSimplex.measure_lt_top

/-- The centroid of the full-dimensional standard simplex.  Its `ι`
coordinates, as well as the deleted coordinate, all equal
`1 / (card ι + 1)`. -/
noncomputable def simplexCentroid (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ ↦ ((Fintype.card ι : ℝ) + 1)⁻¹

@[simp]
theorem simplexCentroid_apply (i : ι) :
    simplexCentroid ι i = ((Fintype.card ι : ℝ) + 1)⁻¹ :=
  rfl

theorem sum_simplexCentroid :
    ∑ i : ι, simplexCentroid ι i =
      (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) := by
  simp [simplexCentroid, div_eq_mul_inv]

theorem simplexCentroid_mem_fullSimplex :
    simplexCentroid ι ∈ fullSimplex ι := by
  rw [mem_fullSimplex_iff]
  constructor
  · intro i
    simp only [simplexCentroid_apply]
    positivity
  · rw [sum_simplexCentroid]
    exact div_le_one (by positivity : 0 < (Fintype.card ι : ℝ) + 1) |>.2
      (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)])

/-- The coordinate box from zero to the centroid is contained in the
simplex.  It supplies a simple positive-volume subset without requiring the
exact volume formula for a simplex. -/
theorem Icc_zero_centroid_subset_fullSimplex :
    Set.Icc (0 : ι → ℝ) (simplexCentroid ι) ⊆ fullSimplex ι := by
  intro x hx
  rw [mem_fullSimplex_iff]
  constructor
  · exact hx.1
  · calc
      ∑ i, x i ≤ ∑ i, simplexCentroid ι i :=
        Finset.sum_le_sum fun i _ ↦ hx.2 i
      _ ≤ 1 := simplexCentroid_mem_fullSimplex (ι := ι) |>.2

theorem volume_fullSimplex_pos :
    0 < volume (fullSimplex ι) := by
  apply lt_of_lt_of_le (b := volume (Set.Icc (0 : ι → ℝ) (simplexCentroid ι)))
  · rw [Real.volume_Icc_pi]
    rw [pos_iff_ne_zero]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [ENNReal.ofReal_ne_zero_iff]
    simp only [simplexCentroid_apply, Pi.zero_apply, sub_zero]
    positivity
  · exact measure_mono Icc_zero_centroid_subset_fullSimplex

/-- The linear functional cutting out the simplex halfspace associated to
the coefficient vector `y`. -/
def simplexLinearForm (y x : ι → ℝ) : ℝ :=
  ∑ i, y i * x i

theorem simplexLinearForm_apply (y x : ι → ℝ) :
    simplexLinearForm y x = ∑ i, y i * x i :=
  rfl

/-- Evaluation of `L_y` at the centroid. -/
theorem simplexLinearForm_centroid (y : ι → ℝ) :
    simplexLinearForm y (simplexCentroid ι) =
      (∑ i, y i) / ((Fintype.card ι : ℝ) + 1) := by
  simp [simplexLinearForm, simplexCentroid, div_eq_mul_inv, Finset.sum_mul]

/-- In the `δ = 1` normalization used in §2.2, `∑ i, y i ≥ card ι + 1`
means that the centroid lies in the upper halfspace `1 ≤ L_y`. -/
theorem one_le_simplexLinearForm_centroid (y : ι → ℝ)
    (hy : (Fintype.card ι : ℝ) + 1 ≤ ∑ i, y i) :
    1 ≤ simplexLinearForm y (simplexCentroid ι) := by
  rw [simplexLinearForm_centroid]
  exact (le_div_iff₀ (by positivity : 0 < (Fintype.card ι : ℝ) + 1)).2
    (by simpa using hy)

end Feige
