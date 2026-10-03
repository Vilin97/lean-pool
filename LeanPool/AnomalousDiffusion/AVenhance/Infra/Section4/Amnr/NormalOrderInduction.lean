/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.NormalOrderStep

/-! Quantitative ordering by weighted budget and finite inversion count. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Arbitrary actual words are controlled by canonical primitive jets.
Gradient coefficients reserve two weighted units and one material level.
This generic conditional lemma proves all commutator bookkeeping explicitly. -/
theorem amnr_normal_order_family_abs_le_of_canonical_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hprimitive : ∀ a α n,
      amnrBudget (amnrMixedWord α n) + amnrNormalFieldCost a ≤ N →
      n + amnrNormalFieldReserve a ≤ cut →
      |amnrWord b (amnrMixedWord α n) (amnrNormalField b f a) z| ≤
        amnrNormalFieldAmplitude F Cb H a * amnrWeight S H (amnrMixedWord α n))
    (a : Option (Fin 2 × Fin 2)) (w : List (Option (Fin 2)))
    (hbudget : amnrBudget w + amnrNormalFieldCost a ≤ N)
    (hcut : amnrMaterialCount w + amnrNormalFieldReserve a ≤ cut) :
    |amnrWord b w (amnrNormalField b f a) z| ≤
      amnrNormalOrderConstant N Cb N * amnrNormalFieldAmplitude F Cb H a * amnrWeight S H w := by
  have hbound : ∀ q : ℕ, q ≤ N → ∀ a w,
      amnrBudget w + amnrNormalFieldCost a ≤ q →
      amnrMaterialCount w + amnrNormalFieldReserve a ≤ cut →
      |amnrWord b w (amnrNormalField b f a) z| ≤
        amnrNormalOrderConstant N Cb q * amnrNormalFieldAmplitude F Cb H a * amnrWeight S H w := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq
      cases q with
      | zero =>
        intro a w hw hc
        have hnil : w = [] := by
          have hlen : w.length ≤ 0 := (amnrBudget_length_le w).trans (by omega)
          cases w with
          | nil => rfl
          | cons d w => simp at hlen
        subst w
        have hp := hprimitive a [] 0 (by simpa [amnrMixedWord, amnrBudget] using hw.trans hq)
          (by simpa only [amnrMaterialCount, zero_add] using hc)
        simpa only [amnrMixedWord, List.map_nil, List.replicate_zero, List.append_nil,
          amnrNormalOrderConstant, one_mul] using hp
      | succ q =>
        let R := amnrNormalOrderSwapFactor N Cb q
        have hR : 1 ≤ R := amnrNormalOrderSwapFactor_one_le hCb q
        have hinner : ∀ r : ℕ, ∀ a w, amnrWordInversions w = r →
            amnrBudget w + amnrNormalFieldCost a ≤ q + 1 →
            amnrMaterialCount w + amnrNormalFieldReserve a ≤ cut →
            |amnrWord b w (amnrNormalField b f a) z| ≤
              amnrNormalFieldAmplitude F Cb H a * amnrWeight S H w * R ^ r := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r hir =>
            intro a w hInv hw hc
            rcases amnrWord_mixed_or_adjacent w with hm | ⟨u, i, v, heq⟩
            · obtain ⟨α, n, heq⟩ := IsAmnrMixedWord.normalForm hm
              subst w
              have hp := hprimitive a α n (hw.trans hq)
                (by rw [amnrMaterialCount_mixed] at hc; exact hc)
              have hs := mul_le_mul_of_nonneg_left (one_le_pow₀ hR (n := r))
                (mul_nonneg (amnrNormalFieldAmplitude_nonneg hF hCb hH a)
                  (amnrWeight_nonneg hS hH (amnrMixedWord α n)))
              simp only [mul_one] at hs
              exact hp.trans hs
            · subst w
              have hi := amnrWordInversions_swap u v i
              have hswap := hir (amnrWordInversions (u ++ some i :: none :: v)) (by omega)
                a (u ++ some i :: none :: v) rfl
                (by rw [← amnrAdjacent_budget]; exact hw)
                (by rw [← amnrAdjacent_material_count]; exact hc)
              rw [← amnrAdjacent_weight] at hswap
              have hs := amnr_normal_order_adjacent_abs_le_of_lower_bounds hb hf hS hH hF hCb z
                a u v i hw hq hc
                (fun a w hw hc => ih q (by omega) (by omega) a w hw hc) hswap
              simpa only [hInv] using hs
        intro a w hw hc
        have hs := hinner (amnrWordInversions w) a w rfl hw hc
        have hlen : w.length ≤ N := (amnrBudget_length_le w).trans (by omega)
        have hp := mul_le_mul_of_nonneg_left (amnrNormalOrderSwapFactor_pow_le (q := q) hCb w hlen)
          (mul_nonneg (amnrNormalFieldAmplitude_nonneg hF hCb hH a) (amnrWeight_nonneg hS hH w))
        refine hs.trans (hp.trans_eq ?_)
        ring
  exact hbound N le_rfl a w hbudget hcut

/-- Canonical scalar jets and strictly lower velocity-gradient levels give
arbitrary scalar words at the identical weighted budget. -/
theorem amnr_word_abs_le_of_mixed_bounds_and_lower_gradients
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hfb : ∀ α n, α.length + 2 * n ≤ N → n ≤ cut →
      |amnrWord b (amnrMixedWord α n) f z| ≤ F * amnrWeight S H (amnrMixedWord α n))
    (hBb : ∀ p i α n, n < cut → α.length + 2 * n + 2 ≤ N →
      |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b p i) z| ≤
        (Cb * H) * amnrWeight S H (amnrMixedWord α n))
    (w : List (Option (Fin 2))) (hbudget : amnrBudget w ≤ N)
    (hcut : amnrMaterialCount w ≤ cut) :
    |amnrWord b w f z| ≤ amnrNormalOrderConstant N Cb N * F * amnrWeight S H w := by
  have hprimitive : ∀ a α n,
      amnrBudget (amnrMixedWord α n) + amnrNormalFieldCost a ≤ N →
      n + amnrNormalFieldReserve a ≤ cut →
      |amnrWord b (amnrMixedWord α n) (amnrNormalField b f a) z| ≤
        amnrNormalFieldAmplitude F Cb H a * amnrWeight S H (amnrMixedWord α n) := by
    intro a α n hbudget hcut
    cases a with
    | none =>
      simp only [amnrNormalFieldCost, amnrNormalFieldReserve, amnrNormalField,
          amnrNormalFieldAmplitude,
        Nat.add_zero, amnrMixedWord_budget] at *
      exact hfb α n hbudget hcut
    | some p =>
      simp only [amnrNormalFieldCost, amnrNormalFieldReserve, amnrNormalField,
          amnrNormalFieldAmplitude,
        amnrMixedWord_budget] at *
      exact hBb p.1 p.2 α n (by omega) hbudget
  exact amnr_normal_order_family_abs_le_of_canonical_bounds hb hf hS hH hF hCb z hprimitive
    none w (by simpa only [amnrNormalFieldCost, Nat.add_zero] using hbudget)
    (by simpa only [amnrNormalFieldReserve, Nat.add_zero] using hcut)

end AVenhance.Infra.Section4
