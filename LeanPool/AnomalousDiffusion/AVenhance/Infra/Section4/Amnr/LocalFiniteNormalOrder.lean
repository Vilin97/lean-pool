/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteNormalOrderInduction

/-! Normal ordering on the source's open positive-time domain. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Local temperature smoothness suffices for the quantitative normal-order
estimate. The weighted budget and material cutoff are unchanged. -/
theorem amnr_word_abs_le_on_of_finite_mixed_bounds_and_lower_gradients
    {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {N cut : ℕ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiffOn ℝ N f U) {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) {z : AmnrSpace} (hz : z ∈ U)
    (hfb : ∀ α n, α.length + 2 * n ≤ N → n ≤ cut →
      |amnrWord b (amnrMixedWord α n) f z| ≤ F * amnrWeight S H (amnrMixedWord α n))
    (hBb : ∀ p i α n, n < cut → α.length + 2 * n + 2 ≤ N →
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (w : List (Option (Fin 2))) (hbudget : amnrBudget w ≤ N)
    (hcut : amnrMaterialCount w ≤ cut) :
    |amnrWord b w f z| ≤ amnrNormalOrderConstant N Cb N * F * amnrWeight S H w := by
  obtain ⟨g, hg, hgf⟩ := amnr_finite_smooth_local_representative hU hf hz
  have he (v : List (Option (Fin 2))) : amnrWord b v g z = amnrWord b v f z :=
    (amnrWord_eventuallyEq hgf b v).eq_of_nhds
  rw [← he w]
  exact amnr_word_abs_le_of_finite_mixed_bounds_and_lower_gradients hb hg hS hH hF hCb z
    (fun α n hbudget hcut => by rw [he]; exact hfb α n hbudget hcut)
    hBb w hbudget hcut

end AVenhance.Infra.Section4
