/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CorrectionSumBounds

/-! Ordered correction estimates from canonical lower-level jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Canonical lower-level jets suffice for the actual material correction.
The normal-order induction preserves every budget and needs only lower gradients. -/
theorem amnrMaterialError_spatial_abs_le_of_canonical_lower_bounds
    {b c : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ} {S H V Cv Cf Cb : ℝ} {N : ℕ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hV : 0 ≤ V) (hCv : 1 ≤ Cv) (hCf : 0 ≤ Cf) (hCb : 0 ≤ Cb)
    (hVS : V * S = H) (α : List (Fin 2)) (n : ℕ) (hn : 1 ≤ n)
    (hbudget : α.length + 2 * n ≤ N) (z : AmnrSpace)
    (hv : ∀ p η r, η.length + 2 * r + 1 ≤ N → r < n →
      |amnrWord c (amnrMixedWord η r) (amnrAdvectionVelocity b c p) z| ≤
        (Cv * V) * amnrWeight S H (amnrMixedWord η r))
    (hs : ∀ η r, amnrMixedWord η r ≠ [] → η.length + 2 * r + 1 ≤ N → r < n →
      |amnrWord c (amnrMixedWord η r) f z| ≤
        (Cf * V) * amnrWeight S H (amnrMixedWord η r))
    (hB : ∀ p i η r, r < n → η.length + 2 * r + 2 ≤ N →
      |amnrWord c (amnrMixedWord η r) (amnrVelocityGradient c p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord η r)) :
    |amnrWord c (α.map some) (amnrMaterialErrorValue b c f n) z| ≤
      ((amnrMaterialErrorCardinality n * (n + 1) ^ α.length : ℕ) : ℝ) *
        ((amnrNormalOrderConstant (N - 1) Cb (N - 1) * Cv) ^ n *
          (amnrNormalOrderConstant (N - 1) Cb (N - 1) * Cf) * V *
            S ^ α.length * H ^ n) := by
  let K := amnrNormalOrderConstant (N - 1) Cb (N - 1)
  have hK : 1 ≤ K := amnrNormalOrderConstant_one_le hCb _
  have hKC : 1 ≤ K * Cv := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ K * Cv := mul_le_mul hK hCv (by norm_num) (by linarith)
  apply amnrMaterialError_spatial_abs_le_of_word_bounds hb hc hf hS hH hV
    hKC (mul_nonneg (by linarith) hCf) hVS α n z
  · intro p w hcut hw
    have hh := amnr_word_abs_le_of_mixed_bounds_and_lower_gradients hc
      (amnrAdvectionVelocity_contDiff hb hc p) (N := N - 1) (cut := n - 1)
      hS hH (mul_nonneg (by linarith) hV) hCb z
      (fun η r hη hr => hv p η r (by omega) (by omega))
      (fun p i η r hr hη => hB p i η r (by omega) (by omega)) w (by omega) (by omega)
    exact hh.trans_eq (by ring)
  · intro w hne hcut hw
    have hh := amnr_word_abs_le_of_nonempty_mixed_bounds_and_lower_gradients hc hf
      (N := N - 1) (cut := n - 1) hS hH (mul_nonneg hCf hV) hCb z
      (fun η r hne hη hr => hs η r hne (by omega) (by omega))
      (fun p i η r hr hη => hB p i η r (by omega) (by omega))
      w hne (by omega) (by omega)
    exact hh.trans_eq (by ring)

end AVenhance.Infra.Section4
