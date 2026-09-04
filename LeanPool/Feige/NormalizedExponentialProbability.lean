/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.NormalizedExponential
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Probability normalization for independent unit exponentials

This module supplies the product-density normalization needed to turn the
normalized-exponential integral identity into a probability-law statement.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace Feige

variable {n : ℕ}

theorem integrable_unitExponentialDensity :
    Integrable unitExponentialDensity := by
  change Integrable ((Ici (0 : ℝ)).indicator
    (fun t ↦ Real.exp (-t)))
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa using Real.GammaIntegral_convergent
    (s := (1 : ℝ)) (by positivity)

/-- The product density of `n` independent unit exponentials is
integrable on the coordinate function space. -/
theorem integrable_pi_unitExponentialDensity :
    Integrable
      (fun x : Fin n → ℝ ↦ ∏ i, unitExponentialDensity (x i)) := by
  rw [volume_pi]
  exact Integrable.fintype_prod fun _ ↦ integrable_unitExponentialDensity

/-- Real-valued joint density on `ℝ × (Fin n → ℝ)`. -/
noncomputable def jointUnitExponentialDensity
    (e : ℝ × (Fin n → ℝ)) : ℝ :=
  unitExponentialDensity e.1 *
    ∏ i, unitExponentialDensity (e.2 i)

theorem integrable_jointUnitExponentialDensity :
    Integrable (jointUnitExponentialDensity :
      (ℝ × (Fin n → ℝ)) → ℝ) := by
  rw [Measure.volume_eq_prod]
  exact Integrable.mul_prod integrable_unitExponentialDensity
    integrable_pi_unitExponentialDensity

theorem integral_jointUnitExponentialDensity :
    ∫ e : ℝ × (Fin n → ℝ), jointUnitExponentialDensity e = 1 := by
  change ∫ e : ℝ × (Fin n → ℝ),
    unitExponentialDensity e.1 *
      (∏ i, unitExponentialDensity (e.2 i)) = 1
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from
    Measure.volume_eq_prod ℝ (Fin n → ℝ)]
  rw [integral_prod_mul unitExponentialDensity
    (fun x : Fin n → ℝ ↦ ∏ i, unitExponentialDensity (x i))]
  rw [integral_unitExponentialDensity,
    integral_pi_unitExponentialDensity, one_mul]

theorem jointUnitExponentialDensity_nonneg
    (e : ℝ × (Fin n → ℝ)) :
    0 ≤ jointUnitExponentialDensity e := by
  apply mul_nonneg
  · unfold unitExponentialDensity
    exact (indicator_nonneg fun _ _ ↦ (Real.exp_pos _).le) e.1
  · exact Finset.prod_nonneg fun _ _ ↦
      (by
        unfold unitExponentialDensity
        exact (indicator_nonneg fun _ _ ↦ (Real.exp_pos _).le) (e.2 _))

/-- `ENNReal` form of normalization of the full independent exponential
product density. -/
theorem lintegral_ofReal_jointUnitExponentialDensity :
    ∫⁻ e : ℝ × (Fin n → ℝ),
        ENNReal.ofReal (jointUnitExponentialDensity e) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    integrable_jointUnitExponentialDensity
    (Filter.Eventually.of_forall jointUnitExponentialDensity_nonneg)]
  rw [integral_jointUnitExponentialDensity]
  simp

/-- The sole point removed when passing from the closed nonnegative
orthant to `positiveExponentialOrthant` is Lebesgue-null. -/
theorem volume_singleton_zeroExponentialVector :
    (volume : Measure (ℝ × (Fin n → ℝ)))
      ({(0, fun _ ↦ 0)} : Set (ℝ × (Fin n → ℝ))) = 0 := by
  rw [Measure.volume_eq_prod ℝ (Fin n → ℝ)]
  rw [show ({(0, fun _ ↦ 0)} : Set (ℝ × (Fin n → ℝ))) =
      ({0} : Set ℝ) ×ˢ
        ({fun _ ↦ 0} : Set (Fin n → ℝ)) by
    ext
    simp]
  rw [Measure.prod_prod, Real.volume_singleton]
  exact zero_mul _

theorem nonnegative_nonzero_exponentialTotal_pos
    {e : ℝ × (Fin n → ℝ)} (h0 : 0 ≤ e.1)
    (hi : ∀ i, 0 ≤ e.2 i) (hne : e ≠ (0, fun _ ↦ 0)) :
    0 < exponentialTotal e := by
  have hs0 : 0 ≤ ∑ i, e.2 i :=
    Finset.sum_nonneg fun i _ ↦ hi i
  have ht0 : 0 ≤ exponentialTotal e := by
    unfold exponentialTotal
    linarith
  rcases lt_or_eq_of_le ht0 with ht | ht
  · exact ht
  · exfalso
    have he1 : e.1 = 0 := by
      unfold exponentialTotal at ht
      nlinarith
    have hs : ∑ i, e.2 i = 0 := by
      unfold exponentialTotal at ht
      nlinarith
    have hei : ∀ i, e.2 i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ hi j)).mp hs i (Finset.mem_univ i)
    apply hne
    ext <;> simp [he1, hei]

theorem jointUnitExponentialDensity_eq_exp_neg_total
    (e : ℝ × (Fin n → ℝ)) (h0 : 0 ≤ e.1)
    (hi : ∀ i, 0 ≤ e.2 i) :
    jointUnitExponentialDensity e =
      Real.exp (-exponentialTotal e) := by
  unfold jointUnitExponentialDensity unitExponentialDensity
  simp only [Set.indicator, mem_Ici, h0, hi, ite_true]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  unfold exponentialTotal
  rw [Finset.sum_neg_distrib]
  ring

theorem jointUnitExponentialDensity_eq_zero_of_neg
    (e : ℝ × (Fin n → ℝ))
    (hneg : e.1 < 0 ∨ ∃ i, e.2 i < 0) :
    jointUnitExponentialDensity e = 0 := by
  unfold jointUnitExponentialDensity unitExponentialDensity
  rcases hneg with hneg | ⟨i, hneg⟩
  · simp [Set.indicator, not_le_of_gt hneg]
  · rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [Set.indicator, not_le_of_gt hneg]

theorem lintegral_positiveExponentialOrthant_exp_neg_total :
    ∫⁻ e in positiveExponentialOrthant (n := n),
        ENNReal.ofReal (Real.exp (-exponentialTotal e)) ∂volume = 1 := by
  rw [← lintegral_indicator
    isMeasurableSet_positiveExponentialOrthant]
  calc
    _ = ∫⁻ e : ℝ × (Fin n → ℝ),
        ENNReal.ofReal (jointUnitExponentialDensity e) := by
      apply lintegral_congr_ae
      have hne : ∀ᵐ e : ℝ × (Fin n → ℝ) ∂volume,
          e ≠ (0, fun _ ↦ 0) := by
        rw [ae_iff]
        simpa using
          (volume_singleton_zeroExponentialVector (n := n))
      filter_upwards [hne] with e hne
      by_cases hnonneg : 0 ≤ e.1 ∧ ∀ i, 0 ≤ e.2 i
      · have ht := nonnegative_nonzero_exponentialTotal_pos
          hnonneg.1 hnonneg.2 hne
        have hm : e ∈ positiveExponentialOrthant (n := n) :=
          ⟨hnonneg.1, hnonneg.2, ht⟩
        rw [Set.indicator_of_mem hm]
        rw [jointUnitExponentialDensity_eq_exp_neg_total
          e hnonneg.1 hnonneg.2]
      · have hnmem : e ∉ positiveExponentialOrthant (n := n) := by
          intro he
          exact hnonneg ⟨he.1, he.2.1⟩
        simp only [Set.indicator, ite_eq_right hnmem]
        have hjoint : jointUnitExponentialDensity e = 0 := by
          apply jointUnitExponentialDensity_eq_zero_of_neg
          by_cases hfirst : 0 ≤ e.1
          · have hcoord : ¬ ∀ i, 0 ≤ e.2 i := by
              intro hi
              exact hnonneg ⟨hfirst, hi⟩
            push Not at hcoord
            exact Or.inr hcoord
          · exact Or.inl (lt_of_not_ge hfirst)
        rw [hjoint]
        simp
    _ = 1 := lintegral_ofReal_jointUnitExponentialDensity

theorem factorial_mul_volume_fullSimplex :
    (n.factorial : ℝ≥0∞) * volume (fullSimplex (Fin n)) = 1 := by
  have h := lintegral_normalizedExponential_eq_simplex (n := n)
    (fun _ : Fin n → ℝ ↦ (1 : ℝ≥0∞)) measurable_const
  have hl :=
    lintegral_positiveExponentialOrthant_exp_neg_total (n := n)
  simp only [mul_one] at h
  rw [hl] at h
  simpa [normalizedExponentialSimplexMeasure] using h.symm

/-- Exact Lebesgue volume of the standard full simplex. -/
theorem volume_fullSimplex_eq_factorial_inv :
    volume (fullSimplex (Fin n)) =
      (n.factorial : ℝ≥0∞)⁻¹ := by
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [mul_comm]
  exact factorial_mul_volume_fullSimplex (n := n)

noncomputable instance
    instIsProbabilityMeasureNormalizedExponentialSimplexMeasure :
    IsProbabilityMeasure
      (normalizedExponentialSimplexMeasure (n := n)) where
  measure_univ := by
    rw [normalizedExponentialSimplexMeasure, Measure.smul_apply]
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter]
    exact factorial_mul_volume_fullSimplex (n := n)

end Feige
