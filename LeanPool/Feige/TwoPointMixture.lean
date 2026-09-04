/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Algebraic core of the two-point mixture lemma

This file develops the two-point mixture decomposition used in the proof of
Theorem 2.1.  It isolates the equality of the lower and upper first moments
and constructs the mean-one two-point law `Q_{x,y}`.
-/

open MeasureTheory Set

namespace Feige

noncomputable section

/-- The lower absolute first moment around one. -/
def belowMoment (μ : Measure ℝ) : ℝ :=
  ∫ x, (|x - 1| - (x - 1)) / 2 ∂μ

/-- The upper absolute first moment around one. -/
def aboveMoment (μ : Measure ℝ) : ℝ :=
  ∫ x, (|x - 1| + (x - 1)) / 2 ∂μ

theorem integrable_sub_one {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ x - 1) μ :=
  hμ.sub (integrable_const 1)

theorem integrable_abs_sub_one {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ |x - 1|) μ :=
  (integrable_sub_one hμ).abs

/-- The two expressions for `M` agree whenever the law has mean one.  No
support assumption is needed for this algebraic identity. -/
theorem belowMoment_eq_aboveMoment {μ : Measure ℝ}
    [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    belowMoment μ = aboveMoment μ := by
  have hsub : (∫ x : ℝ, x - 1 ∂μ) = 0 := by
    rw [integral_sub hμ (integrable_const 1), hmean]
    simp
  unfold belowMoment aboveMoment
  rw [integral_div, integral_div, integral_sub (integrable_abs_sub_one hμ)
    (integrable_sub_one hμ), integral_add (integrable_abs_sub_one hμ)
    (integrable_sub_one hμ), hsub]
  ring

/-- Lower weight in the mean-one law supported on `x < 1 < y`. -/
def twoPointLowerWeight (x y : ℝ) : ℝ :=
  (y - 1) / (y - x)

/-- Upper weight in the mean-one law supported on `x < 1 < y`. -/
def twoPointUpperWeight (x y : ℝ) : ℝ :=
  (1 - x) / (y - x)

theorem twoPointWeights_nonneg {x y : ℝ} (hxy : x < y)
    (hx : x ≤ 1) (hy : 1 ≤ y) :
    0 ≤ twoPointLowerWeight x y ∧ 0 ≤ twoPointUpperWeight x y := by
  constructor
  · unfold twoPointLowerWeight
    exact div_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hxy.le)
  · unfold twoPointUpperWeight
    exact div_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hxy.le)

theorem twoPointWeights_add {x y : ℝ} (hxy : x ≠ y) :
    twoPointLowerWeight x y + twoPointUpperWeight x y = 1 := by
  unfold twoPointLowerWeight twoPointUpperWeight
  field_simp
  ring

/-- The mean-one two-point law, expressed as a genuine nonnegative measure. -/
def twoPointMeasure (x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (twoPointLowerWeight x y) • Measure.dirac x +
    ENNReal.ofReal (twoPointUpperWeight x y) • Measure.dirac y

theorem twoPointMeasure_isProbability {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y) :
    IsProbabilityMeasure (twoPointMeasure x y) := by
  constructor
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply]
  simp only [measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (twoPointWeights_nonneg hxy hx hy).1
      (twoPointWeights_nonneg hxy hx hy).2,
    twoPointWeights_add hxy.ne]
  norm_num

theorem twoPointMeasure_mean {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y) :
    (∫ z : ℝ, z ∂(twoPointMeasure x y)) = 1 := by
  have hw := twoPointWeights_nonneg hxy hx hy
  have hIx : Integrable (fun z : ℝ ↦ z)
      (ENNReal.ofReal (twoPointLowerWeight x y) • Measure.dirac x) :=
    (integrable_dirac' stronglyMeasurable_id (by simp)).smul_measure (by simp)
  have hIy : Integrable (fun z : ℝ ↦ z)
      (ENNReal.ofReal (twoPointUpperWeight x y) • Measure.dirac y) :=
    (integrable_dirac' stronglyMeasurable_id (by simp)).smul_measure (by simp)
  rw [twoPointMeasure, integral_add_measure hIx hIy,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hw.1, ENNReal.toReal_ofReal hw.2]
  simp only [smul_eq_mul]
  unfold twoPointLowerWeight twoPointUpperWeight
  calc
    ((y - 1) / (y - x)) * x + ((1 - x) / (y - x)) * y =
        (y - x) * (y - x)⁻¹ := by field_simp [sub_ne_zero.mpr hxy.ne']; ring
    _ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hxy.ne')

/-- Pointwise algebra behind the two-point mixture formula. -/
theorem twoPointMeasure_scaled_apply {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y)
    (B : Set ℝ) :
    ENNReal.ofReal (y - x) * twoPointMeasure x y B =
      ENNReal.ofReal (y - 1) * Measure.dirac x B +
        ENNReal.ofReal (1 - x) * Measure.dirac y B := by
  rw [twoPointMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, mul_add]
  have hw := twoPointWeights_nonneg hxy hx hy
  change
    ENNReal.ofReal (y - x) *
          (ENNReal.ofReal (twoPointLowerWeight x y) * Measure.dirac x B) +
        ENNReal.ofReal (y - x) *
          (ENNReal.ofReal (twoPointUpperWeight x y) * Measure.dirac y B) =
      ENNReal.ofReal (y - 1) * Measure.dirac x B +
        ENNReal.ofReal (1 - x) * Measure.dirac y B
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sub_nonneg.2 hxy.le),
    ← mul_assoc, ← ENNReal.ofReal_mul (sub_nonneg.2 hxy.le)]
  congr 1
  · apply congrArg₂ (· * ·) _ rfl
    apply congrArg ENNReal.ofReal
    unfold twoPointLowerWeight
    field_simp [sub_ne_zero.mpr hxy.ne']
  · apply congrArg₂ (· * ·) _ rfl
    apply congrArg ENNReal.ofReal
    unfold twoPointUpperWeight
    field_simp [sub_ne_zero.mpr hxy.ne']

/-- The measure obtained after expanding the double integral in the
two-point mixture formula.

The first restricted measure is multiplied by the upper moment (integration
in `y`), and the second by the lower moment (integration in `x`). -/
def expandedTwoPointMixture (μ : Measure ℝ) (M : ℝ) : Measure ℝ :=
  μ {1} • Measure.dirac 1 +
    (ENNReal.ofReal M)⁻¹ •
      (ENNReal.ofReal (aboveMoment μ) • μ.restrict (Iio 1) +
        ENNReal.ofReal (belowMoment μ) • μ.restrict (Ioi 1))

/-- Splitting a measure at one into its below, atom, and above pieces. -/
theorem restrict_below_add_atom_add_above (μ : Measure ℝ) :
    μ.restrict (Iio 1) + μ {1} • Measure.dirac 1 + μ.restrict (Ioi 1) = μ := by
  rw [← Measure.restrict_singleton]
  have h₁ := Measure.restrict_add_restrict_compl
    (μ := μ) (s := Iio (1 : ℝ)) measurableSet_Iio
  have h₂ := Measure.restrict_add_restrict_compl
    (μ := μ.restrict (Iio (1 : ℝ))ᶜ) (s := {1}) (measurableSet_singleton 1)
  rw [MeasureTheory.Measure.restrict_restrict (measurableSet_singleton 1),
    MeasureTheory.Measure.restrict_restrict (measurableSet_singleton 1).compl] at h₂
  have hc : {1} ∩ (Iio (1 : ℝ))ᶜ = {1} := by ext x; simp
  have ha : {1}ᶜ ∩ (Iio (1 : ℝ))ᶜ = Ioi 1 := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_Iio, mem_Ioi]
    constructor <;> intro h
    · rcases h with ⟨hne, hle⟩
      exact lt_of_le_of_ne (le_of_not_gt hle) (Ne.symm hne)
    · exact ⟨ne_of_gt h, not_lt_of_ge h.le⟩
  rw [hc, ha] at h₂
  calc
    μ.restrict (Iio 1) + μ.restrict {1} + μ.restrict (Ioi 1) =
        μ.restrict (Iio 1) + (μ.restrict {1} + μ.restrict (Ioi 1)) := add_assoc ..
    _ = μ.restrict (Iio 1) + μ.restrict (Iio 1)ᶜ := by rw [h₂]
    _ = μ := h₁

/-- The two-point mixture formula after evaluating its two product integrals.
The support assumption is not needed for this final algebraic identity; it
is needed only to ensure that the sampled lower point is nonnegative. -/
theorem expandedTwoPointMixture_eq
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    expandedTwoPointMixture μ (belowMoment μ) = μ := by
  have heq := belowMoment_eq_aboveMoment hμ hmean
  have hne : ENNReal.ofReal (belowMoment μ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hM)
  rw [expandedTwoPointMixture, ← heq]
  rw [smul_add]
  rw [← mul_smul, ← mul_smul, ENNReal.inv_mul_cancel hne (by simp), one_smul]
  rw [one_smul ENNReal]
  calc
    μ {1} • Measure.dirac 1 + (μ.restrict (Iio 1) + μ.restrict (Ioi 1)) =
        μ.restrict (Iio 1) + μ {1} • Measure.dirac 1 + μ.restrict (Ioi 1) := by abel
    _ = μ := restrict_below_add_atom_add_above μ

/-- Version of the preceding theorem retaining the nonnegative-support
hypothesis required by Theorem 2.1. -/
theorem twoPointMixture_formula42
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (_hsupport : μ (Iio 0) = 0)
    (hM : 0 < belowMoment μ) :
    expandedTwoPointMixture μ (belowMoment μ) = μ :=
  expandedTwoPointMixture_eq hμ hmean hM

/-- The lower moment is nonnegative. -/
theorem belowMoment_nonneg {μ : Measure ℝ} :
    0 ≤ belowMoment μ := by
  unfold belowMoment
  apply integral_nonneg
  intro x
  exact div_nonneg (sub_nonneg.mpr (le_abs_self (x - 1))) (by norm_num)

/-- The degenerate branch of the mixture decomposition: if `M = 0`, a
mean-one probability law is concentrated at one. -/
theorem eq_dirac_one_of_belowMoment_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (_hsupport : μ (Iio 0) = 0)
    (hM : belowMoment μ = 0) :
    μ = Measure.dirac 1 := by
  have hsub := integrable_sub_one hμ
  have habs := integrable_abs_sub_one hμ
  have hdefInt :
      Integrable (fun x : ℝ ↦ (|x - 1| - (x - 1)) / 2) μ :=
    (habs.sub hsub).div_const 2
  have hdefNonneg :
      ∀ x : ℝ, 0 ≤ (|x - 1| - (x - 1)) / 2 := by
    intro x
    have := le_abs_self (x - 1)
    linarith
  have hzero :
      (fun x : ℝ ↦ (|x - 1| - (x - 1)) / 2) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg hdefNonneg hdefInt).1
    simpa [belowMoment] using hM
  have hone_le : (fun _ : ℝ ↦ (1 : ℝ)) ≤ᵐ[μ] fun x ↦ x := by
    filter_upwards [hzero] with x hx
    change (|x - 1| - (x - 1)) / 2 = 0 at hx
    have habseq : |x - 1| = x - 1 := by linarith
    have : 0 ≤ x - 1 := habseq ▸ abs_nonneg (x - 1)
    linarith
  have hone_ae : (fun _ : ℝ ↦ (1 : ℝ)) =ᵐ[μ] fun x ↦ x := by
    apply (integral_eq_iff_of_ae_le (integrable_const 1) hμ hone_le).1
    simp [hmean]
  apply Measure.ext
  intro B hB
  by_cases h1 : (1 : ℝ) ∈ B
  · have hBae : (B : Set ℝ) =ᵐ[μ] Set.univ := by
      filter_upwards [hone_ae] with x hx
      apply propext
      constructor
      · intro
        exact Set.mem_univ x
      · intro
        change B 1 at h1
        rwa [← hx]
    rw [measure_congr hBae, measure_univ]
    simp [Measure.dirac_apply' _ hB, Set.indicator_of_mem h1]
  · have hBae : (B : Set ℝ) =ᵐ[μ] (∅ : Set ℝ) := by
      filter_upwards [hone_ae] with x hx
      apply propext
      constructor
      · intro hxB
        exfalso
        apply h1
        change B 1
        change B x at hxB
        rwa [← hx] at hxB
      · intro hxE
        exact False.elim hxE
    rw [measure_congr hBae, measure_empty]
    simp [Measure.dirac_apply' _ hB, Set.indicator_of_notMem h1]

/-- Full mixture dichotomy: either the law is the degenerate law at one, or
its positive lower moment gives the two-point mixture formula. -/
theorem twoPointMixture_dichotomy
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hsupport : μ (Iio 0) = 0) :
    μ = Measure.dirac 1 ∨
      (0 < belowMoment μ ∧
        expandedTwoPointMixture μ (belowMoment μ) = μ) := by
  rcases (belowMoment_nonneg (μ := μ)).eq_or_lt with hzero | hpos
  · exact Or.inl (eq_dirac_one_of_belowMoment_eq_zero hμ hmean hsupport hzero.symm)
  · exact Or.inr ⟨hpos, twoPointMixture_formula42 hμ hmean hsupport hpos⟩

end

end Feige
