/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Lemma43Relations
import LeanPool.Feige.TransferProbability23

/-!
# Endpoint tail identities for the local transfer step
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige
namespace Lemma43Endpoints

open ProbabilityTheory TransferStein TransferTestFunctions

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem expMeasure_one_Iic (t : ℝ) :
    expMeasure 1 (Iic t) =
      ENNReal.ofReal (if 0 ≤ t then 1 - exp (-t) else 0) := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos]
  simp

/-- Subtracting `bE` and taking the nonnegative tail applies the
`φ_b` endpoint transform to the original law. -/
theorem F_zMinusLaw_eq_A
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    Lemma43.F (zMinusLaw μ b) = Lemma43.A μ b := by
  rw [Lemma43.F, Lemma43.A, zMinusLaw,
    Measure.map_apply (measurable_zMinusMap b) measurableSet_Ici]
  have hs : MeasurableSet
      ((fun p : ℝ × ℝ => p.1 - b * p.2) ⁻¹' Ici 0) :=
    (measurable_zMinusMap b) measurableSet_Ici
  rw [Measure.prod_apply hs]
  have hsection : ∀ y : ℝ,
      Prod.mk y ⁻¹' ((fun p : ℝ × ℝ => p.1 - b * p.2) ⁻¹' Ici 0) =
        Iic (y / b) := by
    intro y
    ext e
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro h
    · apply (le_div_iff₀ hb).2
      linarith
    · have := (le_div_iff₀ hb).1 h
      linarith
  simp_rw [hsection, expMeasure_one_Iic]
  have hpoint : ∀ y : ℝ,
      (if 0 ≤ y / b then 1 - exp (-(y / b)) else 0) =
        transferPhi b y := by
    intro y
    by_cases hy : 0 ≤ y
    · rw [ite_eq_left (div_nonneg hy hb.le), transferPhi_of_nonneg hb hy]
      congr 2
      ring
    · have hy' : y ≤ 0 := le_of_not_ge hy
      rw [ite_eq_right (not_le.mpr (div_neg_of_neg_of_pos (lt_of_not_ge hy) hb)),
        transferPhi_of_nonpos hb hy']
  simp_rw [hpoint]
  have hi := Lemma43.integrable_transferPhi μ hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall
      (fun y => transferPhi_nonneg b y))]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (transferPhi_nonneg b))

theorem expMeasure_one_Ici_all (t : ℝ) :
    expMeasure 1 (Ici t) =
      ENNReal.ofReal (if t < 0 then 1 else exp (-t)) := by
  by_cases ht : t < 0
  · rw [ite_eq_left ht]
    have hsub : Ici 0 ⊆ Ici t := fun x hx => le_trans ht.le hx
    have hge : 1 ≤ expMeasure 1 (Ici t) := by
      have hz := ExponentialTransfer.expMeasure_one_Ici
        (x := 0) le_rfl
      norm_num at hz
      rw [← hz]
      exact measure_mono hsub
    have hle : expMeasure 1 (Ici t) ≤ 1 := by
      rw [← measure_univ (μ := expMeasure 1)]
      exact measure_mono (subset_univ _)
    have hone : expMeasure 1 (Ici t) = 1 := le_antisymm hle hge
    rw [hone]
    simp
  · rw [ite_eq_right ht]
    rw [ExponentialTransfer.expMeasure_one_Ici (le_of_not_gt ht)]

/-- Adding `aE` and taking the nonnegative tail applies the `ψ_a`
endpoint transform to the original law. -/
theorem F_zPlusLaw_eq_B
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a) :
    Lemma43.F (zPlusLaw μ a) = Lemma43.B μ a := by
  rw [Lemma43.F, Lemma43.B, zPlusLaw,
    Measure.map_apply (measurable_zPlusMap a) measurableSet_Ici]
  have hs : MeasurableSet
      ((fun p : ℝ × ℝ => p.1 + a * p.2) ⁻¹' Ici 0) :=
    (measurable_zPlusMap a) measurableSet_Ici
  rw [Measure.prod_apply hs]
  have hsection : ∀ y : ℝ,
      Prod.mk y ⁻¹' ((fun p : ℝ × ℝ => p.1 + a * p.2) ⁻¹' Ici 0) =
        Ici (-y / a) := by
    intro y
    ext e
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro h
    · apply (div_le_iff₀ ha).2
      linarith
    · have := (div_le_iff₀ ha).1 h
      linarith
  simp_rw [hsection, expMeasure_one_Ici_all]
  have hpoint : ∀ y : ℝ,
      (if -y / a < 0 then 1 else exp (-(-y / a))) =
        transferPsi a y := by
    intro y
    by_cases hy : 0 < y
    · rw [ite_eq_left (div_neg_of_neg_of_pos (neg_neg_of_pos hy) ha),
        transferPsi_of_nonneg ha hy.le]
    · have hy' : y ≤ 0 := le_of_not_gt hy
      rw [ite_eq_right (not_lt.mpr
          (div_nonneg (neg_nonneg.mpr hy') ha.le)),
        transferPsi_of_nonpos ha hy']
      congr 2
      ring
  simp_rw [hpoint]
  have hi := Lemma43.integrable_transferPsi μ a
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall
      (fun y => transferPsi_nonneg a y))]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (transferPsi_nonneg a))

end Lemma43Endpoints
end Feige
