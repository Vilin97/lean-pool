/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.AdvectionProductBounds

/-! Exact amplitude cancellation in material correction products. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Each fast factor supplies exactly the material rate consumed by its
advection. This identity avoids losing a scale factor at higher levels. -/
theorem amnr_correction_scale_cancel {V S H : ℝ} (hVS : V * S = H)
    (L M k n : ℕ) (hn : M + L = n) :
    V ^ (L + 1) * S ^ (L + k) * H ^ M = V * S ^ k * H ^ n := by
  rw [← hn, pow_add, pow_add, pow_succ, ← hVS, mul_pow]
  ring

/-- A genuine material correction has only lower-level jets; their actual
product has the correct current-scale amplitude and derivative rates. -/
theorem amnrCorrectionTerm_abs_le {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ} {S H V C F : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hVS : V * S = H) (α : List (Fin 2)) (n : ℕ) (t : AmnrAdvectionTerm)
    (ht : t ∈ amnrSpatialAdvectionTerms α (amnrMaterialErrorTerms n)) (z : AmnrSpace)
    (hA : ∀ a ∈ t.factors, |amnrWord c a.2 (v a.1) z| ≤ C * V * amnrWeight S H a.2)
    (hf : |amnrWord c t.scalarWord f z| ≤ F * V * amnrWeight S H t.scalarWord) :
    |amnrAdvectionTermValue c v f t z| ≤
      C ^ t.factors.length * F * V * S ^ α.length * H ^ n := by
  have hh := amnrAdvectionTermValue_abs_le hS hH hV hC t z hA hf
  obtain ⟨_, _, hP, hM⟩ := amnrSpatialMaterialErrorTerms_counts α n t ht
  rw [hP] at hh
  refine hh.trans_eq ?_
  calc
    _ = (C ^ t.factors.length * F) *
        (V ^ (t.factors.length + 1) * S ^ (t.factors.length + α.length) *
          H ^ amnrTermMaterialCount t) := by ring
    _ = _ := by rw [amnr_correction_scale_cancel hVS _ _ _ n hM]; ring

end AVenhance.Infra.Section4
