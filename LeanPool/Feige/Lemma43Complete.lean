/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Lemma43Relations
import LeanPool.Feige.Lemma43Density

/-!
# Fully automatic local exponential transfer interface

This file discharges the bounded-integrability hypotheses in the transfer
Stein identities and assembles the probability relations and density
identifications.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige
namespace Lemma43Complete

open TransferStein TransferTestFunctions ProbabilityTheory

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem integrable_affine_prod_of_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {g : ℝ → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ x, ‖g x‖ ≤ C) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ g (p.1 + r * p.2))
      (μ.prod (expMeasure 1)) := by
  apply Integrable.of_bound
    (hg.comp (measurable_fst.add
      (measurable_const.mul measurable_snd))).aestronglyMeasurable C
  filter_upwards with p
  exact hC _

theorem integrable_phiPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ} (hd : 0 < d) (a : ℝ) :
    Integrable (phiPlus d a) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (continuous_transferPhi d).measurable 1
    (norm_transferPhi_le_one hd) a
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  rfl

theorem integrable_phiMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ} (hd : 0 < d) (b : ℝ) :
    Integrable (phiMinus d b) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (continuous_transferPhi d).measurable 1
    (norm_transferPhi_le_one hd) (-b)
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  simp only [phiMinus, neg_mul, sub_eq_add_neg]

theorem integrable_psiPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c a : ℝ) :
    Integrable (psiPlus c a) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (continuous_transferPsi c).measurable 1
    (norm_transferPsi_le_one c) a
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  rfl

theorem integrable_psiMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c b : ℝ) :
    Integrable (psiMinus c b) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (continuous_transferPsi c).measurable 1
    (norm_transferPsi_le_one c) (-b)
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  simp only [psiMinus, neg_mul, sub_eq_add_neg]

theorem integrable_phiDerivPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ} (hd : 0 < d) (a : ℝ) :
    Integrable (phiDerivPlus d a) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (measurable_const.mul (measurable_transferPhiDeriv d))
    (|a| / d) (fun x ↦ by
      change ‖a * transferPhiDeriv d x‖ ≤ |a| / d
      rw [norm_mul, Real.norm_eq_abs]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left
          (norm_transferPhiDeriv_le hd x) (abs_nonneg a)) a
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  rfl

theorem integrable_phiDerivMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {d : ℝ} (hd : 0 < d) (b : ℝ) :
    Integrable (phiDerivMinus d b) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (measurable_const.mul (measurable_transferPhiDeriv d))
    (|b| / d) (fun x ↦ by
      change ‖b * transferPhiDeriv d x‖ ≤ |b| / d
      rw [norm_mul, Real.norm_eq_abs]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left
          (norm_transferPhiDeriv_le hd x) (abs_nonneg b)) (-b)
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  simp only [phiDerivMinus, neg_mul, sub_eq_add_neg, Pi.mul_apply]

theorem integrable_psiDerivPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Integrable (psiDerivPlus c a) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (measurable_const.mul (measurable_transferPsiDeriv c))
    (|a| / c) (fun x ↦ by
      change ‖a * transferPsiDeriv c x‖ ≤ |a| / c
      rw [norm_mul, Real.norm_eq_abs]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left
          (norm_transferPsiDeriv_le hc x) (abs_nonneg a)) a
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  rfl

theorem integrable_psiDerivMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Integrable (psiDerivMinus c b) μ := by
  have hjoint := integrable_affine_prod_of_bound μ
    (measurable_const.mul (measurable_transferPsiDeriv c))
    (|b| / c) (fun x ↦ by
      change ‖b * transferPsiDeriv c x‖ ≤ |b| / c
      rw [norm_mul, Real.norm_eq_abs]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left
          (norm_transferPsiDeriv_le hc x) (abs_nonneg b)) (-b)
  have houter := hjoint.integral_prod_left
  convert houter using 1
  funext y
  rw [integral_expMeasure_one]
  simp only [psiDerivMinus, neg_mul, sub_eq_add_neg, Pi.mul_apply]

/-- The lower-test transfer identity, with all bounded-integrability
hypotheses discharged. -/
theorem equation23_A_probability_auto
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    d * ((∫ z, transferPhi d z ∂zPlusLaw μ a) -
      ∫ z, transferPhi d z ∂zMinusLaw μ b) =
      a * uProbability (zPlusLaw μ a) d +
        b * uProbability (zMinusLaw μ b) d := by
  apply equation23_A_probability μ hd ha hb
  · exact integrable_phiPlus μ hd a
  · exact integrable_phiMinus μ hd b
  · exact integrable_phiDerivPlus μ hd a
  · exact integrable_phiDerivMinus μ hd b
  · exact integrable_affine_prod_of_bound μ
      (measurable_transferPhiDeriv d) (1 / d)
      (norm_transferPhiDeriv_le hd) a
  · simpa only [neg_mul, sub_eq_add_neg] using
      integrable_affine_prod_of_bound μ
        (measurable_transferPhiDeriv d) (1 / d)
        (norm_transferPhiDeriv_le hd) (-b)

/-- The upper-test transfer identity, again with no integrability inputs. -/
theorem equation23_B_probability_auto
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c * ((∫ z, transferPsi c z ∂zPlusLaw μ a) -
      ∫ z, transferPsi c z ∂zMinusLaw μ b) =
      a * vProbability (zPlusLaw μ a) c +
        b * vProbability (zMinusLaw μ b) c := by
  apply equation23_B_probability μ hc ha hb
  · exact integrable_psiPlus μ c a
  · exact integrable_psiMinus μ c b
  · exact integrable_psiDerivPlus μ hc a
  · exact integrable_psiDerivMinus μ hc b
  · exact integrable_affine_prod_of_bound μ
      (measurable_transferPsiDeriv c) (1 / c)
      (norm_transferPsiDeriv_le hc) a
  · simpa only [neg_mul, sub_eq_add_neg] using
      integrable_affine_prod_of_bound μ
        (measurable_transferPsiDeriv c) (1 / c)
        (norm_transferPsiDeriv_le hc) (-b)

/-- The local transfer result for the actual positive and negative
exponential shifts of an arbitrary probability density.  Probability
relations, Stein integrability, density identification, denominator
positivity, and the likelihood-ratio order are all discharged internally. -/
theorem complete_for_density
    {f : ℝ → ENNReal} (hf : Measurable f)
    (hflc : LikelihoodRatio.FourPointLogConcave f)
    [IsProbabilityMeasure (volume.withDensity f)]
    {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let νP := zPlusLaw (volume.withDensity f) a
    let νM := zMinusLaw (volume.withDensity f) b
    ((1 - Lemma43.theta νM c d) *
          (Lemma43.A νP d - Lemma43.A νM d) -
          (c / (c + d)) * (Lemma43.F νP - Lemma43.F νM) =
        ((a - c) / (c + d)) * Lemma43.w νP c d *
          (Lemma43.theta νP c d - Lemma43.theta νM c d)) ∧
      Lemma43.theta νM c d ≤ Lemma43.theta νP c d ∧
      0 < Lemma43.w νP c d ∧ 0 < Lemma43.w νM c d := by
  dsimp only
  let : IsProbabilityMeasure
      (zPlusLaw (volume.withDensity f) a) := by
    constructor
    rw [zPlusLaw, Measure.map_apply (measurable_zPlusMap a)
      MeasurableSet.univ]
    simp
  let : IsProbabilityMeasure
      (zMinusLaw (volume.withDensity f) b) := by
    constructor
    rw [zMinusLaw, Measure.map_apply (measurable_zMinusMap b)
      MeasurableSet.univ]
    simp
  apply Lemma43.complete hf hflc _ _ ha.le hb.le hc hd
  · exact Lemma43.probabilityRelations _ _ hc hd
  · simpa only [Lemma43.A, Lemma43.u] using
      equation23_A_probability_auto (volume.withDensity f) ha hb hd
  · simpa only [Lemma43.B, Lemma43.v] using
      equation23_B_probability_auto (volume.withDensity f) ha hb hc
  · exact Lemma43Density.densityIdentification_zPlus_zMinus hf hc hd

end Lemma43Complete
end Feige
