/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteCanonicalEnvelopeL2

/-! Quantitative L2 normal ordering with exact finite jet budgets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Canonical L2 jets and source velocity-gradient jets control every ordered
word at the same weighted budget and material level. The finite envelope is
integrated after pointwise normal ordering, so no pointwise temperature bound
is assumed. -/
theorem amnr_word_L2_le_on_of_finite_mixed_bounds_and_lower_gradients
    {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {N cut : ℕ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiffOn ℝ N f U) {S H G Cb : ℝ} (hS : 0 < S) (hH : 0 <
        H) (hCb : 0 ≤ Cb)
    (hfb : ∀ α n, α.length + 2 * n ≤ N → n ≤ cut →
      eLpNorm (amnrWord b (amnrMixedWord α n) f) 2 μ ≤
        ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α n)))
    (hBb : ∀ p i α n, n < cut → α.length + 2 * n + 2 ≤ N → ∀ z ∈ U,
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (w : List (Option (Fin 2))) (hbudget : amnrBudget w ≤ N)
    (hcut : amnrMaterialCount w ≤ cut) :
    eLpNorm (amnrWord b w f) 2 μ ≤
      ENNReal.ofReal (amnrNormalOrderConstant N Cb N *
        (amnrCanonicalSamples N cut).card * G * amnrWeight S H w) := by
  let E := amnrCanonicalEnvelope N cut S H b f
  let K := amnrNormalOrderConstant N Cb N * amnrWeight S H w
  have hK : 0 ≤ K := mul_nonneg
    (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb N))
    (amnrWeight_nonneg hS.le hH.le w)
  have hlen := (amnrBudget_length_le w).trans hbudget
  have hm := ((amnrWord_contDiffOn hU (hb.of_le (by simp)).contDiffOn hf w
    (n := 0) (by omega)).continuousOn.aestronglyMeasurable
    hU.measurableSet (μ := volume)).mono_ac hμ
  have hpoint : ∀ᵐ z ∂μ, ‖amnrWord b w f z‖ ≤ ‖(K • E) z‖ := by
    apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
    intro z hz
    have hEn : 0 ≤ E z := amnrCanonicalEnvelope_nonneg hS.le hH.le N cut b f z
    have hh := amnr_word_abs_le_on_of_finite_mixed_bounds_and_lower_gradients hU hb hf
      hS.le hH.le hEn hCb hz
      (fun α n hbudget hcut => amnrCanonicalEnvelope_dominates hS hH N cut b f z α n hbudget hcut)
      (fun p i α n hn hbudget => hBb p i α n hn hbudget z hz) w hbudget hcut
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hK, abs_of_nonneg hEn]
    exact hh.trans_eq (by dsimp [K, E]; ring)
  have he := amnrCanonicalEnvelope_finite_L2_le hU hμ (hb.of_le (by simp)).contDiffOn hf hS hH hfb
  have hh := eLpNorm_mono_ae hm hpoint (p := 2)
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg hK] at hh
  refine (hh.trans (mul_le_mul_right he _)).trans_eq ?_
  rw [← ENNReal.ofReal_mul hK]
  congr 1
  dsimp [K]
  ring

end AVenhance.Infra.Section4
