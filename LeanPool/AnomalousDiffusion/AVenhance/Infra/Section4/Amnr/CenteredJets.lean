/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.NormalOrderInduction

/-! Ordering estimates without an artificial velocity zero-order bound. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Centering a scalar at the evaluation point preserves every nonempty
actual derivative word. The removed value is a global scalar constant. -/
theorem amnrWord_centered_nonempty {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : List (Option (Fin 2))) (hw : w ≠ []) (z : AmnrSpace) :
    amnrWord b w (fun y => f y - f z) = amnrWord b w f := by
  change amnrWord b w (f - fun _ => f z) = _
  rw [amnrWord_sub_global hb hf contDiff_const w, amnrWord_const]
  simp only [hw, ↓reduceIte, sub_zero]

/-- Nonempty canonical jets and lower gradient levels control arbitrary
nonempty words. No zero-order velocity amplitude is assumed. -/
theorem amnr_word_abs_le_of_nonempty_mixed_bounds_and_lower_gradients
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hfb : ∀ α n, amnrMixedWord α n ≠ [] → α.length + 2 * n ≤ N → n ≤ cut →
      |amnrWord b (amnrMixedWord α n) f z| ≤ F * amnrWeight S H (amnrMixedWord α n))
    (hBb : ∀ p i α n, n < cut → α.length + 2 * n + 2 ≤ N →
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (w : List (Option (Fin 2))) (hw : w ≠ []) (hbudget : amnrBudget w ≤ N)
    (hcut : amnrMaterialCount w ≤ cut) :
    |amnrWord b w f z| ≤ amnrNormalOrderConstant N Cb N * F * amnrWeight S H w := by
  let g := fun y => f y - f z
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hprimitive : ∀ a α n,
      amnrBudget (amnrMixedWord α n) + amnrNormalFieldCost a ≤ N →
      n + amnrNormalFieldReserve a ≤ cut →
      |amnrWord b (amnrMixedWord α n) (amnrNormalField b g a) z| ≤
        amnrNormalFieldAmplitude F Cb H a * amnrWeight S H (amnrMixedWord α n) := by
    intro a α n hbudget hcut
    cases a with
    | none =>
      simp only [amnrNormalFieldCost, amnrNormalFieldReserve, amnrNormalField,
          amnrNormalFieldAmplitude,
        Nat.add_zero, amnrMixedWord_budget] at *
      by_cases he : amnrMixedWord α n = []
      · rw [he]
        simp only [amnrWord, amnrWeight, List.map_nil, List.prod_nil, mul_one]
        simpa only [g, sub_self, abs_zero] using hF
      · rw [amnrWord_centered_nonempty hb hf _ he z]
        exact hfb α n he hbudget hcut
    | some p =>
      simp only [amnrNormalFieldCost, amnrNormalFieldReserve, amnrNormalField,
          amnrNormalFieldAmplitude,
        amnrMixedWord_budget] at *
      exact hBb p.1 p.2 α n (by omega) hbudget
  have hh := amnr_normal_order_family_abs_le_of_canonical_bounds hb hg hS hH hF hCb z hprimitive
    none w (by simpa only [amnrNormalFieldCost, Nat.add_zero] using hbudget)
    (by simpa only [amnrNormalFieldReserve, Nat.add_zero] using hcut)
  change |amnrWord b w g z| ≤ _ at hh
  rw [amnrWord_centered_nonempty hb hf w hw z] at hh
  exact hh

end AVenhance.Infra.Section4
