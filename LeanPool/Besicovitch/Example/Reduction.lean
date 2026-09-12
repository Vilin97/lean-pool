/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Hull
public import LeanPool.Besicovitch.Example.Measurable
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Reduction from Lipschitz curves to Lipschitz pieces of `g`

If a Lipschitz curve `f : ℝ → ℝ²` meets Besicovitch's set `Π` in positive `μH[1]`-measure,
then `g` is Lipschitz on a subset of `[0, 1]` of positive Lebesgue measure.

Let `f₁ = π₁ ∘ f` be the first coordinate of the curve and `B = f ⁻¹ Π`.  By Rademacher's
theorem `f₁` is differentiable almost everywhere, and the curve over the null set of
non-differentiability points carries no `μH[1]`-measure.  Over the points where `f₁' = 0` the
image of `f₁` is Lebesgue-null (the one-dimensional area formula), so the graph over it, which
contains the curve there, is `μH[1]`-null by `LeanPool.Besicovitch.Example.Hull`.  Hence the curve over
the points with `f₁' ≠ 0` has positive measure; a countable partition of these into pieces on
which `f₁` is well approximated by a nonzero linear map produces a piece `P` on which `f₁` is
bi-Lipschitz.  On `A = f₁ '' P` the function `g` is then Lipschitz, since `g (f₁ t) = f₂ t`
is Lipschitz in `t` and `t` is Lipschitz in `f₁ t`; and `A` has positive Lebesgue measure since
the graph over `A` contains `f '' P`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-! ### Besicovitch's set as a graph -/

/-- A point whose second coordinate is `g` of its first lies on the graph over that first
coordinate. -/
theorem graphMap_eq_of_apply_one {p : Plane} (h : p 1 = besicovitchFun (p 0)) :
    graphMap (p 0) = p := by
  refine PiLp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp
  · simpa using h.symm

/-- Membership in Besicovitch's set in terms of coordinates. -/
theorem mem_besicovitchSet_iff {p : Plane} :
    p ∈ besicovitchSet ↔ p 0 ∈ Icc (0:ℝ) 1 ∧ p 1 = besicovitchFun (p 0) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · rintro ⟨h0, h1⟩
    exact ⟨p 0, h0, graphMap_eq_of_apply_one h1⟩

/-- A point of Besicovitch's set is the graph point over its first coordinate. -/
theorem graphMap_eq_of_mem {p : Plane} (hp : p ∈ besicovitchSet) : graphMap (p 0) = p :=
  graphMap_eq_of_apply_one (mem_besicovitchSet_iff.mp hp).2

/-- Besicovitch's set is measurable. -/
theorem measurableSet_besicovitchSet : MeasurableSet besicovitchSet := by
  have hset : besicovitchSet =
      {p : Plane | p 0 ∈ Icc (0:ℝ) 1} ∩ {p : Plane | p 1 = besicovitchFun (p 0)} :=
    Set.ext fun _ ↦ mem_besicovitchSet_iff
  have h0 : Measurable fun p : Plane ↦ p 0 := (PiLp.continuous_apply 2 _ 0).measurable
  have h1 : Measurable fun p : Plane ↦ p 1 := (PiLp.continuous_apply 2 _ 1).measurable
  rw [hset]
  exact (h0 measurableSet_Icc).inter
    (measurableSet_eq_fun h1 (measurable_besicovitchFun.comp h0))

/-! ### Coordinates of a Lipschitz curve -/

/-- Each coordinate of the plane is `1`-Lipschitz. -/
theorem lipschitzWith_coord (i : Fin 2) : LipschitzWith 1 (fun p : Plane ↦ p i) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  simpa using PiLp.norm_apply_le (p - q) i

/-- A coordinate of a `K`-Lipschitz curve is `K`-Lipschitz. -/
theorem lipschitzWith_curve_coord {K : ℝ≥0} {f : ℝ → Plane} (hf : LipschitzWith K f)
    (i : Fin 2) : LipschitzWith K fun t ↦ f t i := by
  have := (lipschitzWith_coord i).comp hf
  rwa [one_mul] at this

/-- The curve over a set of its preimage of `Π` lies in the graph over the first coordinates. -/
theorem image_subset_graphMap_image {f : ℝ → Plane} {S : Set ℝ}
    (hS : S ⊆ f ⁻¹' besicovitchSet) :
    f '' S ⊆ graphMap '' ((fun t ↦ f t 0) '' S) := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨f t 0, ⟨t, ht, rfl⟩, graphMap_eq_of_mem (hS ht)⟩

/-- The curve over a piece of its preimage of `Π` has `μH[1]`-measure at most twice the Lebesgue
measure of the first coordinates. -/
theorem hausdorffMeasure_image_le_volume_image {f : ℝ → Plane} {S : Set ℝ}
    (hS : S ⊆ f ⁻¹' besicovitchSet) :
    μH[1] (f '' S) ≤ 2 * volume ((fun t ↦ f t 0) '' S) :=
  (measure_mono (image_subset_graphMap_image hS)).trans
    (hausdorffMeasure_graphMap_image_le _)

/-- A Lipschitz curve over a Lebesgue-null set is `μH[1]`-null. -/
theorem hausdorffMeasure_image_eq_zero_of_volume_eq_zero {K : ℝ≥0} {f : ℝ → Plane}
    (hf : LipschitzWith K f) {N : Set ℝ} (hN : volume N = 0) : μH[1] (f '' N) = 0 := by
  have h := hf.hausdorffMeasure_image_le zero_le_one N
  rw [hausdorffMeasure_real, hN, mul_zero] at h
  exact nonpos_iff_eq_zero.mp h

/-- The image of a set on which a real function has zero derivative is Lebesgue-null. -/
theorem volume_image_eq_zero_of_fderiv_eq_zero {f₁ : ℝ → ℝ} {S : Set ℝ}
    (hS : ∀ t ∈ S, DifferentiableAt ℝ f₁ t ∧ fderiv ℝ f₁ t = 0) :
    volume (f₁ '' S) = 0 :=
  addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun t ↦ fderiv ℝ f₁ t)
    (fun t ht ↦ (hS t ht).1.hasFDerivAt.hasFDerivWithinAt)
    (fun t ht ↦ by rw [(hS t ht).2]; simp)

/-! ### Pieces on which the first coordinate is bi-Lipschitz -/

/-- A linear map `ℝ → ℝ` is multiplication by its value at `1`. -/
theorem clm_apply_eq_mul (A : ℝ →L[ℝ] ℝ) (z : ℝ) : A z = z * A 1 := by
  simpa using A.map_smul z 1

/-- The operator norm of a linear map `ℝ → ℝ` is at most its value at `1`. -/
theorem clm_norm_le_abs_apply_one (A : ℝ →L[ℝ] ℝ) : ‖A‖ ≤ |A 1| :=
  A.opNorm_le_bound (abs_nonneg _) fun z ↦ by
    rw [clm_apply_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]

/-- A nonzero linear map `ℝ → ℝ` has nonzero value at `1`. -/
theorem clm_abs_apply_one_pos {A : ℝ →L[ℝ] ℝ} (hA : A ≠ 0) : 0 < |A 1| := by
  refine abs_pos.mpr fun h ↦ hA ?_
  ext
  rw [clm_apply_eq_mul, h]
  simp

/-- A function approximated by a nonzero linear map `A` on `P` within `‖A‖ / 2` is bi-Lipschitz
from below on `P` with constant `|A 1| / 2`. -/
theorem abs_sub_le_of_approximatesLinearOn {f₁ : ℝ → ℝ} {A : ℝ →L[ℝ] ℝ}
    {P : Set ℝ} (happ : ApproximatesLinearOn f₁ A P (‖A‖₊ / 2)) {x y : ℝ}
    (hx : x ∈ P) (hy : y ∈ P) :
    |A 1| / 2 * |x - y| ≤ |f₁ x - f₁ y| := by
  have h1 := happ x hx y hy
  have hc : ((‖A‖₊ / 2 : ℝ≥0) : ℝ) = ‖A‖ / 2 := by push_cast; rfl
  rw [hc, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  have h2 : |A (x - y)| = |x - y| * |A 1| := by rw [clm_apply_eq_mul, abs_mul]
  have h3 := clm_norm_le_abs_apply_one A
  have h4 := abs_sub_abs_le_abs_sub (A (x - y)) (f₁ x - f₁ y)
  have h5 := mul_le_mul_of_nonneg_right h3 (abs_nonneg (x - y))
  have h6 := abs_sub_comm (A (x - y)) (f₁ x - f₁ y)
  linarith

/-- The conclusion on a single piece: if the curve over `P ⊆ f ⁻¹' Π` has positive
`μH[1]`-measure and the first coordinate is well approximated on `P` by a nonzero linear map,
then `g` is Lipschitz on the first coordinates of `P`, a set of positive measure. -/
theorem exists_lipschitzOnWith_of_piece {K : ℝ≥0} {f : ℝ → Plane} (hf : LipschitzWith K f)
    {P : Set ℝ} (hP : P ⊆ f ⁻¹' besicovitchSet) {A : ℝ →L[ℝ] ℝ} (hA : A ≠ 0)
    (happ : ApproximatesLinearOn (fun t ↦ f t 0) A P (‖A‖₊ / 2))
    (hpos : 0 < μH[1] (f '' P)) :
    ∃ (L : ℝ≥0) (S : Set ℝ), S ⊆ Icc 0 1 ∧ 0 < volume S ∧
      LipschitzOnWith L besicovitchFun S := by
  set a := |A 1|
  have ha : 0 < a := clm_abs_apply_one_pos hA
  refine ⟨⟨2 * K / a, by positivity⟩, (fun t ↦ f t 0) '' P, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (mem_besicovitchSet_iff.mp (hP ht)).1
  · by_contra h
    rw [not_lt, nonpos_iff_eq_zero] at h
    have := hausdorffMeasure_image_le_volume_image hP
    rw [h, mul_zero] at this
    exact absurd (hpos.trans_le this) (lt_irrefl _)
  · refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    show |besicovitchFun (f s 0) - besicovitchFun (f s' 0)| ≤ 2 * K / a * |f s 0 - f s' 0|
    rw [← (mem_besicovitchSet_iff.mp (hP hs)).2, ← (mem_besicovitchSet_iff.mp (hP hs')).2]
    have hK := (lipschitzWith_curve_coord hf 1).dist_le_mul s s'
    rw [Real.dist_eq, Real.dist_eq] at hK
    have hl := abs_sub_le_of_approximatesLinearOn happ hs hs'
    calc |f s 1 - f s' 1| ≤ K * |s - s'| := hK
      _ = 2 * K / a * (a / 2 * |s - s'|) := by field_simp
      _ ≤ 2 * K / a * |f s 0 - f s' 0| := by gcongr

/-! ### The reduction -/

/-- **Reduction.** A Lipschitz curve meeting Besicovitch's set in positive `μH[1]`-measure
yields a subset of `[0, 1]` of positive Lebesgue measure on which `g` is Lipschitz. -/
theorem exists_lipschitzOnWith_of_hausdorffMeasure_pos {K : ℝ≥0} {f : ℝ → Plane}
    (hf : LipschitzWith K f) (hpos : 0 < μH[1] (range f ∩ besicovitchSet)) :
    ∃ (L : ℝ≥0) (A : Set ℝ), A ⊆ Icc 0 1 ∧ 0 < volume A ∧
      LipschitzOnWith L besicovitchFun A := by
  classical
  rw [← image_preimage_eq_range_inter] at hpos
  set B := f ⁻¹' besicovitchSet
  set f₁ : ℝ → ℝ := fun t ↦ f t 0
  have hf₁lip : LipschitzWith K f₁ := lipschitzWith_curve_coord hf 0
  set D := {t | DifferentiableAt ℝ f₁ t}
  have hDc : volume {t | ¬ DifferentiableAt ℝ f₁ t} = 0 :=
    ae_iff.mp (hf₁lip.ae_differentiableAt (μ := volume))
  set B₀ := B ∩ D ∩ {t | fderiv ℝ f₁ t = 0}
  set B₁ := B ∩ D ∩ {t | fderiv ℝ f₁ t ≠ 0}
  -- the curve over the non-differentiability points is null
  have h1 : μH[1] (f '' (B \ D)) = 0 :=
    hausdorffMeasure_image_eq_zero_of_volume_eq_zero hf
      (measure_mono_null (fun t ht ↦ ht.2) hDc)
  -- the curve over the zero-derivative points is null
  have h2 : μH[1] (f '' B₀) = 0 := by
    refine measure_mono_null (image_subset_graphMap_image fun t ht ↦ ht.1.1)
      (hausdorffMeasure_graphMap_image_eq_zero ?_)
    exact volume_image_eq_zero_of_fderiv_eq_zero fun t ht ↦ ⟨ht.1.2, ht.2⟩
  -- so the curve over the nonzero-derivative points has positive measure
  have hcover : B ⊆ (B \ D) ∪ B₀ ∪ B₁ := by
    intro t ht
    by_cases hDt : t ∈ D
    · by_cases h0 : fderiv ℝ f₁ t = 0
      · exact Or.inl (Or.inr ⟨⟨ht, hDt⟩, h0⟩)
      · exact Or.inr ⟨⟨ht, hDt⟩, h0⟩
    · exact Or.inl (Or.inl ⟨ht, hDt⟩)
  have hpos' : 0 < μH[1] (f '' B₁) := by
    by_contra h
    rw [not_lt, nonpos_iff_eq_zero] at h
    have hle : μH[1] (f '' B) ≤
        μH[1] (f '' (B \ D)) + μH[1] (f '' B₀) + μH[1] (f '' B₁) :=
      calc μH[1] (f '' B) ≤ μH[1] (f '' ((B \ D) ∪ B₀ ∪ B₁)) :=
            measure_mono (image_mono hcover)
        _ = μH[1] (f '' (B \ D) ∪ f '' B₀ ∪ f '' B₁) := by rw [image_union, image_union]
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    rw [h1, h2, h, add_zero, add_zero] at hle
    exact absurd (hpos.trans_le hle) (lt_irrefl _)
  -- partition the nonzero-derivative points into pieces with good linear approximations
  have hderiv : ∀ t ∈ B₁, HasFDerivWithinAt f₁ (fderiv ℝ f₁ t) B₁ t :=
    fun t ht ↦ ht.1.2.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨t, A, -, -, hcov, happrox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f₁ B₁
      (fun t ↦ fderiv ℝ f₁ t) hderiv (fun A ↦ if A = 0 then 1 else ‖A‖₊ / 2)
      fun A ↦ by
        split_ifs with h
        · exact one_ne_zero
        · exact div_ne_zero (nnnorm_ne_zero_iff.mpr h) two_ne_zero
  -- some piece carries positive measure
  obtain ⟨n, hn⟩ : ∃ n, 0 < μH[1] (f '' (B₁ ∩ t n)) := by
    by_contra h
    have hsum : ∑' n, μH[1] (f '' (B₁ ∩ t n)) = 0 :=
      ENNReal.tsum_eq_zero.mpr fun n ↦
        nonpos_iff_eq_zero.mp (not_lt.mp (not_exists.mp h n))
    have hle : μH[1] (f '' B₁) ≤ ∑' n, μH[1] (f '' (B₁ ∩ t n)) :=
      calc μH[1] (f '' B₁) ≤ μH[1] (f '' ⋃ n, B₁ ∩ t n) := by
            refine measure_mono (image_mono ?_)
            rw [← inter_iUnion]
            exact subset_inter subset_rfl hcov
        _ = μH[1] (⋃ n, f '' (B₁ ∩ t n)) := by rw [image_iUnion]
        _ ≤ _ := measure_iUnion_le _
    rw [hsum] at hle
    exact absurd (hpos'.trans_le hle) (lt_irrefl _)
  -- the linear map of that piece is nonzero
  have hne : B₁.Nonempty :=
    (Set.image_nonempty.mp (nonempty_of_measure_ne_zero hn.ne')).mono inter_subset_left
  obtain ⟨y, hy, hAy⟩ := hA hne n
  have hAne : A n ≠ 0 := by rw [hAy]; exact hy.2
  have happ := happrox n
  simp only [hAne, ↓reduceIte] at happ
  exact exists_lipschitzOnWith_of_piece hf (fun s hs ↦ hs.1.1.1) hAne happ hn

end LeanPool.Besicovitch.Example
