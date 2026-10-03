/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.LocalFiniteNormalOrderL2

/-! A normal-ordering constant independent of the lower material cutoff. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

theorem amnrCanonicalSamples_card_le {N cut : ℕ} (hc : cut ≤ N) :
    (amnrCanonicalSamples N cut).card ≤ (amnrCanonicalSamples N N).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqB, hqC⟩ := (amnrCanonicalSamples_mem q.1 q.2 N cut).mp hq
  exact (amnrCanonicalSamples_mem q.1 q.2 N N).mpr ⟨hqB, hqC.trans hc⟩

/-- A lower-material canonical estimate controls any ordered word with the
same total budget using one constant for all cutoffs up to N. -/
theorem amnr_word_L2_le_uniform_cut {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ} {N cut : ℕ} (hcutN : cut ≤ N)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiffOn ℝ N f U)
    {S H G Cb : ℝ} (hS : 0 < S) (hH : 0 < H) (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hfb : ∀ α n, α.length + 2 * n ≤ N → n ≤ cut →
      eLpNorm (amnrWord b (amnrMixedWord α n) f) 2 μ ≤
        ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α n)))
    (hBb : ∀ p i α n, n < cut → α.length + 2 * n + 2 ≤ N → ∀ z ∈ U,
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N) (hc : amnrMaterialCount w ≤ cut) :
    eLpNorm (amnrWord b w f) 2 μ ≤
      ENNReal.ofReal (amnrNormalOrderConstant N Cb N *
        (amnrCanonicalSamples N N).card * G * amnrWeight S H w) := by
  refine (amnr_word_L2_le_on_of_finite_mixed_bounds_and_lower_gradients hU hμ hb hf
    hS hH hCb hfb hBb w hw hc).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : ((amnrCanonicalSamples N cut).card : ℝ) ≤ (amnrCanonicalSamples N N).card :=
    Nat.cast_le.mpr (amnrCanonicalSamples_card_le hcutN)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard
      (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb N))) hG)
    (amnrWeight_nonneg hS.le hH.le w)

end AVenhance.Infra.Section4
