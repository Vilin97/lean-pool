/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TransferStein

/-!
# Probability-law formulation of the transfer Stein identities
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige
namespace TransferStein

open TransferTestFunctions ProbabilityTheory

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Law of `Z₊ = Y + aE`, where `E` is an independent rate-one exponential. -/
noncomputable def zPlusLaw (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + a * p.2) (μ.prod (expMeasure 1))

/-- Law of `Z₋ = Y - bE`, where `E` is an independent rate-one exponential. -/
noncomputable def zMinusLaw (μ : Measure ℝ) (b : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 - b * p.2) (μ.prod (expMeasure 1))

theorem measurable_zPlusMap (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => p.1 + a * p.2) := by fun_prop

theorem measurable_zMinusMap (b : ℝ) :
    Measurable (fun p : ℝ × ℝ => p.1 - b * p.2) := by fun_prop

instance zPlusLaw_isFinite (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    IsFiniteMeasure (zPlusLaw μ a) := by
  unfold zPlusLaw
  infer_instance

instance zMinusLaw_isFinite (μ : Measure ℝ) [IsFiniteMeasure μ] (b : ℝ) :
    IsFiniteMeasure (zMinusLaw μ b) := by
  unfold zMinusLaw
  infer_instance

/-- Expectations under the pushforward law reduce to product-space expectations. -/
theorem integral_zPlusLaw
    (μ : Measure ℝ) (a : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (zPlusLaw μ a)) :
    ∫ z, f z ∂zPlusLaw μ a =
      ∫ p : ℝ × ℝ, f (p.1 + a * p.2) ∂μ.prod (expMeasure 1) := by
  rw [zPlusLaw, MeasureTheory.integral_map (measurable_zPlusMap a).aemeasurable hf]

theorem integral_zMinusLaw
    (μ : Measure ℝ) (b : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (zMinusLaw μ b)) :
    ∫ z, f z ∂zMinusLaw μ b =
      ∫ p : ℝ × ℝ, f (p.1 - b * p.2) ∂μ.prod (expMeasure 1) := by
  rw [zMinusLaw, MeasureTheory.integral_map (measurable_zMinusMap b).aemeasurable hf]

/-- Adding a nondegenerate exponential variable removes every atom. -/
theorem zPlusLaw_singleton
    (μ : Measure ℝ) {a x : ℝ} (ha : a ≠ 0) :
    zPlusLaw μ a {x} = 0 := by
  rw [zPlusLaw, Measure.map_apply (μ := μ.prod (expMeasure 1))
    (measurable_zPlusMap a) (measurableSet_singleton x)]
  have hs : MeasurableSet
      ((fun p : ℝ × ℝ => p.1 + a * p.2) ⁻¹' {x}) :=
    (measurable_zPlusMap a) (measurableSet_singleton x)
  rw [Measure.prod_apply hs]
  calc
    _ = ∫⁻ _y : ℝ, 0 ∂μ := by
      apply lintegral_congr
      intro y
      have hsection :
          Prod.mk y ⁻¹' ((fun p : ℝ × ℝ => p.1 + a * p.2) ⁻¹' {x}) =
            {(x - y) / a} := by
        ext e
        simp only [mem_preimage, mem_singleton_iff]
        constructor <;> intro h
        · apply (eq_div_iff ha).2
          linarith
        · rw [h]
          field_simp
          ring
      rw [hsection, ExponentialTransfer.expMeasure_one_singleton]
    _ = 0 := lintegral_zero

/-- Subtracting a nondegenerate exponential variable likewise removes every atom. -/
theorem zMinusLaw_singleton
    (μ : Measure ℝ) {b x : ℝ} (hb : b ≠ 0) :
    zMinusLaw μ b {x} = 0 := by
  rw [zMinusLaw, Measure.map_apply (μ := μ.prod (expMeasure 1))
    (measurable_zMinusMap b) (measurableSet_singleton x)]
  have hs : MeasurableSet
      ((fun p : ℝ × ℝ => p.1 - b * p.2) ⁻¹' {x}) :=
    (measurable_zMinusMap b) (measurableSet_singleton x)
  rw [Measure.prod_apply hs]
  calc
    _ = ∫⁻ _y : ℝ, 0 ∂μ := by
      apply lintegral_congr
      intro y
      have hsection :
          Prod.mk y ⁻¹' ((fun p : ℝ × ℝ => p.1 - b * p.2) ⁻¹' {x}) =
            {(y - x) / b} := by
        ext e
        simp only [mem_preimage, mem_singleton_iff]
        constructor <;> intro h
        · apply (eq_div_iff hb).2
          linarith
        · rw [h]
          field_simp
          ring
      rw [hsection, ExponentialTransfer.expMeasure_one_singleton]
    _ = 0 := lintegral_zero

theorem measurable_uTailIntegrand (d : ℝ) :
    Measurable (uTailIntegrand d) := by
  unfold uTailIntegrand
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem measurable_vTailIntegrand (c : ℝ) :
    Measurable (vTailIntegrand c) := by
  unfold vTailIntegrand
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem uTailIntegrand_nonneg (d z : ℝ) :
    0 ≤ uTailIntegrand d z := by
  unfold uTailIntegrand
  split_ifs <;> positivity

theorem vTailIntegrand_nonneg (c z : ℝ) :
    0 ≤ vTailIntegrand c z := by
  unfold vTailIntegrand
  split_ifs <;> positivity

theorem uTailIntegrand_le_one {d : ℝ} (hd : 0 < d) (z : ℝ) :
    uTailIntegrand d z ≤ 1 := by
  unfold uTailIntegrand
  split_ifs with hz
  · exact exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hd.le)
  · norm_num

theorem vTailIntegrand_le_one {c : ℝ} (hc : 0 < c) (z : ℝ) :
    vTailIntegrand c z ≤ 1 := by
  unfold vTailIntegrand
  split_ifs with hz
  · exact exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hz.le hc.le)
  · norm_num

theorem integrable_uTailIntegrand
    (ν : Measure ℝ) [IsFiniteMeasure ν] {d : ℝ} (hd : 0 < d) :
    Integrable (uTailIntegrand d) ν := by
  apply Integrable.of_bound (measurable_uTailIntegrand d).aestronglyMeasurable 1
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (uTailIntegrand_nonneg d z)]
  exact uTailIntegrand_le_one hd z

theorem integrable_vTailIntegrand
    (ν : Measure ℝ) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    Integrable (vTailIntegrand c) ν := by
  apply Integrable.of_bound (measurable_vTailIntegrand c).aestronglyMeasurable 1
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (vTailIntegrand_nonneg c z)]
  exact vTailIntegrand_le_one hc z

/-- The probability `P(0 ≤ Z < dE')`, represented on the canonical
independent product space. -/
noncomputable def uProbability (ν : Measure ℝ) (d : ℝ) : ℝ :=
  ENNReal.toReal
    (ν.prod (expMeasure 1) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < d * p.2})

/-- The probability `P(-cE' ≤ Z < 0)`. -/
noncomputable def vProbability (ν : Measure ℝ) (c : ℝ) : ℝ :=
  ENNReal.toReal
    (ν.prod (expMeasure 1) {p : ℝ × ℝ | p.1 < 0 ∧ -c * p.2 ≤ p.1})

theorem uProbability_eq_integral
    (ν : Measure ℝ) [IsFiniteMeasure ν] {d : ℝ} (hd : 0 < d) :
    uProbability ν d = ∫ z, uTailIntegrand d z ∂ν := by
  unfold uProbability
  rw [ExponentialTransfer.prod_measure_u ν d hd]
  change (∫⁻ z, ENNReal.ofReal (uTailIntegrand d z) ∂ν).toReal =
    ∫ z, uTailIntegrand d z ∂ν
  have hi := integrable_uTailIntegrand ν hd
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (uTailIntegrand_nonneg d))]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (uTailIntegrand_nonneg d))

theorem vProbability_eq_integral
    (ν : Measure ℝ) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    vProbability ν c = ∫ z, vTailIntegrand c z ∂ν := by
  unfold vProbability
  rw [ExponentialTransfer.prod_measure_v ν c hc]
  change (∫⁻ z, ENNReal.ofReal (vTailIntegrand c z) ∂ν).toReal =
    ∫ z, vTailIntegrand c z ∂ν
  have hi := integrable_vTailIntegrand ν hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (vTailIntegrand_nonneg c))]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (vTailIntegrand_nonneg c))

/-- Rate-one exponential integration is integration against
`exp (-e)` on the positive half-line. -/
theorem integral_expMeasure_one (f : ℝ → ℝ) :
    ∫ e, f e ∂expMeasure 1 =
      ∫ e in Ioi 0, f e * exp (-e) := by
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul]
  · rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    have hzero : ∀ᵐ e : ℝ ∂volume, e ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using
        (Real.volume_singleton (a := 0))
    filter_upwards [hzero] with e hne
    by_cases he : 0 < e
    · have hcoef :
          (gammaPDF 1 1 e).toReal = exp (-e) := by
        simp [gammaPDF, gammaPDFReal, he.le, (exp_pos (-e)).le]
      simp [hcoef, he, mul_comm, Set.indicator]
    · have hlt : e < 0 := lt_of_le_of_ne (le_of_not_gt he) hne
      have hcoef : (gammaPDF 1 1 e).toReal = 0 := by
        simp [gammaPDF, gammaPDFReal, not_le.mpr hlt]
      simp [hcoef, he, Set.indicator]
  · exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1)
  · filter_upwards with e
    simp [gammaPDF]

theorem integral_zPlusLaw_eq_nested
    (μ : Measure ℝ) [SFinite μ] (a : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (zPlusLaw μ a))
    (hprod : Integrable
      (fun p : ℝ × ℝ => f (p.1 + a * p.2)) (μ.prod (expMeasure 1))) :
    ∫ z, f z ∂zPlusLaw μ a =
      ∫ y, (∫ e in Ioi 0, f (y + a * e) * exp (-e) ∂volume) ∂μ := by
  rw [integral_zPlusLaw μ a f hf, integral_prod _ hprod]
  simp_rw [integral_expMeasure_one]

theorem integral_zMinusLaw_eq_nested
    (μ : Measure ℝ) [SFinite μ] (b : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (zMinusLaw μ b))
    (hprod : Integrable
      (fun p : ℝ × ℝ => f (p.1 - b * p.2)) (μ.prod (expMeasure 1))) :
    ∫ z, f z ∂zMinusLaw μ b =
      ∫ y, (∫ e in Ioi 0, f (y - b * e) * exp (-e) ∂volume) ∂μ := by
  rw [integral_zMinusLaw μ b f hf, integral_prod _ hprod]
  simp_rw [integral_expMeasure_one]

theorem integrable_transferPhi_zPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d : ℝ} (hd : 0 < d) (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => transferPhi d (p.1 + a * p.2))
      (μ.prod (expMeasure 1)) := by
  apply Integrable.of_bound
    ((continuous_transferPhi d).comp (by fun_prop)).aestronglyMeasurable 1
  filter_upwards with p
  exact norm_transferPhi_le_one hd _

theorem integrable_transferPhi_zMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d : ℝ} (hd : 0 < d) (b : ℝ) :
    Integrable (fun p : ℝ × ℝ => transferPhi d (p.1 - b * p.2))
      (μ.prod (expMeasure 1)) := by
  apply Integrable.of_bound
    ((continuous_transferPhi d).comp (by fun_prop)).aestronglyMeasurable 1
  filter_upwards with p
  exact norm_transferPhi_le_one hd _

theorem integrable_transferPsi_zPlus
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c a : ℝ) :
    Integrable (fun p : ℝ × ℝ => transferPsi c (p.1 + a * p.2))
      (μ.prod (expMeasure 1)) := by
  apply Integrable.of_bound
    ((continuous_transferPsi c).comp (by fun_prop)).aestronglyMeasurable 1
  filter_upwards with p
  exact norm_transferPsi_le_one c _

theorem integrable_transferPsi_zMinus
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c b : ℝ) :
    Integrable (fun p : ℝ × ℝ => transferPsi c (p.1 - b * p.2))
      (μ.prod (expMeasure 1)) := by
  apply Integrable.of_bound
    ((continuous_transferPsi c).comp (by fun_prop)).aestronglyMeasurable 1
  filter_upwards with p
  exact norm_transferPsi_le_one c _

theorem APlus_eq_law
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d : ℝ} (hd : 0 < d) (a : ℝ) :
    APlus μ d a = ∫ z, transferPhi d z ∂zPlusLaw μ a := by
  symm
  rw [integral_zPlusLaw_eq_nested μ a (transferPhi d)
    (continuous_transferPhi d).aestronglyMeasurable
    (integrable_transferPhi_zPlus μ hd a)]
  change _ = ∫ y, phiPlus d a y ∂μ
  unfold phiPlus
  rfl

theorem AMinus_eq_law
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d : ℝ} (hd : 0 < d) (b : ℝ) :
    AMinus μ d b = ∫ z, transferPhi d z ∂zMinusLaw μ b := by
  symm
  rw [integral_zMinusLaw_eq_nested μ b (transferPhi d)
    (continuous_transferPhi d).aestronglyMeasurable
    (integrable_transferPhi_zMinus μ hd b)]
  change _ = ∫ y, phiMinus d b y ∂μ
  unfold phiMinus
  rfl

theorem BPlus_eq_law
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c a : ℝ) :
    BPlus μ c a = ∫ z, transferPsi c z ∂zPlusLaw μ a := by
  symm
  rw [integral_zPlusLaw_eq_nested μ a (transferPsi c)
    (continuous_transferPsi c).aestronglyMeasurable
    (integrable_transferPsi_zPlus μ c a)]
  change _ = ∫ y, psiPlus c a y ∂μ
  unfold psiPlus
  rfl

theorem BMinus_eq_law
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c b : ℝ) :
    BMinus μ c b = ∫ z, transferPsi c z ∂zMinusLaw μ b := by
  symm
  rw [integral_zMinusLaw_eq_nested μ b (transferPsi c)
    (continuous_transferPsi c).aestronglyMeasurable
    (integrable_transferPsi_zMinus μ c b)]
  change _ = ∫ y, psiMinus c b y ∂μ
  unfold psiMinus
  rfl

/-- On any atomless finite law, the lower-tail transfer probability `u` is
exactly `d E[φ'(Z)]`. -/
theorem uProbability_eq_derivative
    (ν : Measure ℝ) [IsFiniteMeasure ν] {d : ℝ}
    (hd : 0 < d) (hzero : ν {0} = 0) :
    uProbability ν d = d * ∫ z, transferPhiDeriv d z ∂ν := by
  rw [uProbability_eq_integral ν hd]
  exact (d_mul_integral_transferPhiDeriv ν hd hzero).symm

/-- The corresponding identity `v = c E[ψ'(Z)]`. -/
theorem vProbability_eq_derivative
    (ν : Measure ℝ) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    vProbability ν c = c * ∫ z, transferPsiDeriv c z ∂ν := by
  rw [vProbability_eq_integral ν hc]
  exact (c_mul_integral_transferPsiDeriv ν hc).symm

theorem uProbability_zPlus_eq_derivative
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a d : ℝ}
    (ha : 0 < a) (hd : 0 < d) :
    uProbability (zPlusLaw μ a) d =
      d * ∫ z, transferPhiDeriv d z ∂zPlusLaw μ a :=
  uProbability_eq_derivative _ hd (zPlusLaw_singleton μ ha.ne')

theorem uProbability_zMinus_eq_derivative
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b d : ℝ}
    (hb : 0 < b) (hd : 0 < d) :
    uProbability (zMinusLaw μ b) d =
      d * ∫ z, transferPhiDeriv d z ∂zMinusLaw μ b :=
  uProbability_eq_derivative _ hd (zMinusLaw_singleton μ hb.ne')

theorem vProbability_zPlus_eq_derivative
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (_ha : 0 < a) (hc : 0 < c) :
    vProbability (zPlusLaw μ a) c =
      c * ∫ z, transferPsiDeriv c z ∂zPlusLaw μ a :=
  vProbability_eq_derivative _ hc

theorem vProbability_zMinus_eq_derivative
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b c : ℝ}
    (_hb : 0 < b) (hc : 0 < c) :
    vProbability (zMinusLaw μ b) c =
      c * ∫ z, transferPsiDeriv c z ∂zMinusLaw μ b :=
  vProbability_eq_derivative _ hc

theorem uPlus_eq_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a d : ℝ}
    (ha : 0 < a) (hd : 0 < d)
    (hprod : Integrable
      (fun p : ℝ × ℝ => transferPhiDeriv d (p.1 + a * p.2))
      (μ.prod (expMeasure 1))) :
    uPlus μ d a = uProbability (zPlusLaw μ a) d := by
  have hnest := integral_zPlusLaw_eq_nested μ a (transferPhiDeriv d)
    ((measurable_transferPhiDeriv d).aestronglyMeasurable) hprod
  unfold uPlus phiDerivPlus
  have hinner : ∀ y : ℝ,
      (∫ e in Ioi 0,
          a * transferPhiDeriv d (y + a * e) * exp (-e)) =
        a * ∫ e in Ioi 0,
          transferPhiDeriv d (y + a * e) * exp (-e) := by
    intro y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with e
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hscale : (d / a) * a = d := by field_simp
  rw [← mul_assoc, hscale, ← hnest]
  exact (uProbability_zPlus_eq_derivative μ ha hd).symm

theorem uMinus_eq_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b d : ℝ}
    (hb : 0 < b) (hd : 0 < d)
    (hprod : Integrable
      (fun p : ℝ × ℝ => transferPhiDeriv d (p.1 - b * p.2))
      (μ.prod (expMeasure 1))) :
    uMinus μ d b = uProbability (zMinusLaw μ b) d := by
  have hnest := integral_zMinusLaw_eq_nested μ b (transferPhiDeriv d)
    ((measurable_transferPhiDeriv d).aestronglyMeasurable) hprod
  unfold uMinus phiDerivMinus
  have hinner : ∀ y : ℝ,
      (∫ e in Ioi 0,
          b * transferPhiDeriv d (y - b * e) * exp (-e)) =
        b * ∫ e in Ioi 0,
          transferPhiDeriv d (y - b * e) * exp (-e) := by
    intro y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with e
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hscale : (d / b) * b = d := by field_simp
  rw [← mul_assoc, hscale, ← hnest]
  exact (uProbability_zMinus_eq_derivative μ hb hd).symm

theorem vPlus_eq_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hprod : Integrable
      (fun p : ℝ × ℝ => transferPsiDeriv c (p.1 + a * p.2))
      (μ.prod (expMeasure 1))) :
    vPlus μ c a = vProbability (zPlusLaw μ a) c := by
  have hnest := integral_zPlusLaw_eq_nested μ a (transferPsiDeriv c)
    ((measurable_transferPsiDeriv c).aestronglyMeasurable) hprod
  unfold vPlus psiDerivPlus
  have hinner : ∀ y : ℝ,
      (∫ e in Ioi 0,
          a * transferPsiDeriv c (y + a * e) * exp (-e)) =
        a * ∫ e in Ioi 0,
          transferPsiDeriv c (y + a * e) * exp (-e) := by
    intro y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with e
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hscale : (c / a) * a = c := by field_simp
  rw [← mul_assoc, hscale, ← hnest]
  exact (vProbability_zPlus_eq_derivative μ ha hc).symm

theorem vMinus_eq_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hprod : Integrable
      (fun p : ℝ × ℝ => transferPsiDeriv c (p.1 - b * p.2))
      (μ.prod (expMeasure 1))) :
    vMinus μ c b = vProbability (zMinusLaw μ b) c := by
  have hnest := integral_zMinusLaw_eq_nested μ b (transferPsiDeriv c)
    ((measurable_transferPsiDeriv c).aestronglyMeasurable) hprod
  unfold vMinus psiDerivMinus
  have hinner : ∀ y : ℝ,
      (∫ e in Ioi 0,
          b * transferPsiDeriv c (y - b * e) * exp (-e)) =
        b * ∫ e in Ioi 0,
          transferPsiDeriv c (y - b * e) * exp (-e) := by
    intro y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with e
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hscale : (c / b) * b = c := by field_simp
  rw [← mul_assoc, hscale, ← hnest]
  exact (vProbability_zMinus_eq_derivative μ hb hc).symm

/-- The lower-test identity with `A±` expressed as expectations under the
actual laws of `Z±` and `u±` as event probabilities. -/
theorem equation23_A_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (phiPlus d a) μ)
    (hMinus : Integrable (phiMinus d b) μ)
    (hDerivPlus : Integrable (phiDerivPlus d a) μ)
    (hDerivMinus : Integrable (phiDerivMinus d b) μ)
    (hLawDerivPlus : Integrable
      (fun p : ℝ × ℝ => transferPhiDeriv d (p.1 + a * p.2))
      (μ.prod (expMeasure 1)))
    (hLawDerivMinus : Integrable
      (fun p : ℝ × ℝ => transferPhiDeriv d (p.1 - b * p.2))
      (μ.prod (expMeasure 1))) :
    d * ((∫ z, transferPhi d z ∂zPlusLaw μ a) -
      ∫ z, transferPhi d z ∂zMinusLaw μ b) =
      a * uProbability (zPlusLaw μ a) d +
        b * uProbability (zMinusLaw μ b) d := by
  rw [← APlus_eq_law μ hd a, ← AMinus_eq_law μ hd b,
    ← uPlus_eq_probability μ ha hd hLawDerivPlus,
    ← uMinus_eq_probability μ hb hd hLawDerivMinus]
  exact equation23_A μ hd ha hb hPlus hMinus hDerivPlus hDerivMinus

/-- The corresponding upper-test probability identity. -/
theorem equation23_B_probability
    (μ : Measure ℝ) [IsFiniteMeasure μ] {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hPlus : Integrable (psiPlus c a) μ)
    (hMinus : Integrable (psiMinus c b) μ)
    (hDerivPlus : Integrable (psiDerivPlus c a) μ)
    (hDerivMinus : Integrable (psiDerivMinus c b) μ)
    (hLawDerivPlus : Integrable
      (fun p : ℝ × ℝ => transferPsiDeriv c (p.1 + a * p.2))
      (μ.prod (expMeasure 1)))
    (hLawDerivMinus : Integrable
      (fun p : ℝ × ℝ => transferPsiDeriv c (p.1 - b * p.2))
      (μ.prod (expMeasure 1))) :
    c * ((∫ z, transferPsi c z ∂zPlusLaw μ a) -
      ∫ z, transferPsi c z ∂zMinusLaw μ b) =
      a * vProbability (zPlusLaw μ a) c +
        b * vProbability (zMinusLaw μ b) c := by
  rw [← BPlus_eq_law μ c a, ← BMinus_eq_law μ c b,
    ← vPlus_eq_probability μ ha hc hLawDerivPlus,
    ← vMinus_eq_probability μ hb hc hLawDerivMinus]
  exact equation23_B μ hc ha hb hPlus hMinus hDerivPlus hDerivMinus

end TransferStein
end Feige
