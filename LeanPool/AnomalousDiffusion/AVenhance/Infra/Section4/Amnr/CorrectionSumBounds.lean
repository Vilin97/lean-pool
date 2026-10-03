/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CorrectionScaling

/-! Quantitative bounds for finite actual correction sums. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_list_abs_sum_le {α : Type*} (T : List α) (f : α → ℝ) {K : ℝ}
    (hT : ∀ t ∈ T, |f t| ≤ K) : |(T.map f).sum| ≤ (T.length : ℝ) * K := by
  induction T with
  | nil => simp
  | cons t T ih =>
    have ht := hT t (by simp)
    have hh := ih (fun a ha => hT a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ |f t| + |(T.map f).sum| := abs_add_le _ _
      _ ≤ K + (T.length : ℝ) * K := add_le_add ht hh
      _ = _ := by ring

/-- The error sum uses only strictly lower material jets, with their precise
weighted budgets. This is a conditional calculus estimate, not a source premise. -/
theorem amnrMaterialError_spatial_abs_le_of_word_bounds {b c : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} {S H V C F : ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hV : 0 ≤ V) (hC : 1 ≤ C) (hF : 0 ≤ F) (hVS : V * S = H)
    (α : List (Fin 2)) (n : ℕ) (z : AmnrSpace)
    (hv : ∀ p w, amnrMaterialCount w < n → amnrBudget w + 2 ≤ α.length + 2 * n →
      |amnrWord c w (amnrAdvectionVelocity b c p) z| ≤ C * V * amnrWeight S H w)
    (hscalar : ∀ w, w ≠ [] → amnrMaterialCount w < n →
      amnrBudget w + 1 ≤ α.length + 2 * n →
      |amnrWord c w f z| ≤ F * V * amnrWeight S H w) :
    |amnrWord c (α.map some) (amnrMaterialErrorValue b c f n) z| ≤
      ((amnrMaterialErrorCardinality n * (n + 1) ^ α.length : ℕ) : ℝ) *
        (C ^ n * F * V * S ^ α.length * H ^ n) := by
  rw [amnrMaterialErrorValue, amnrSpatialAdvectionTerms_value hc
    (amnrAdvectionVelocity_contDiff hb hc) hf, amnr_list_sum_apply]
  simp only [List.map_map, Function.comp_def]
  let T := amnrSpatialAdvectionTerms α (amnrMaterialErrorTerms n)
  let K := C ^ n * F * V * S ^ α.length * H ^ n
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterms : ∀ t ∈ T, |amnrAdvectionTermValue c (amnrAdvectionVelocity b c) f t z| ≤ K := by
    intro t ht
    obtain ⟨hw, hm, hbudget, hA⟩ := amnrCorrectionBudgets α n t ht
    have hh := amnrCorrectionTerm_abs_le hS hH hV (by linarith) hVS α n t ht z
      (fun a ha => hv a.1 a.2 (hA a ha).1 (hA a ha).2)
      (hscalar t.scalarWord hw hm hbudget)
    obtain ⟨_, _, _, hcounts⟩ := amnrSpatialMaterialErrorTerms_counts α n t ht
    have hpow : C ^ t.factors.length ≤ C ^ n := pow_le_pow_right₀ hC (by omega)
    exact hh.trans (by dsimp [K]; gcongr)
  have hh := amnr_list_abs_sum_le T _ hterms
  have hlen := amnrSpatialMaterialErrorTerms_length_le α n
  have hcast : (T.length : ℝ) ≤
      ((amnrMaterialErrorCardinality n * (n + 1) ^ α.length : ℕ) : ℝ) := by
    exact_mod_cast hlen
  exact hh.trans (mul_le_mul_of_nonneg_right hcast hK)

end AVenhance.Infra.Section4
