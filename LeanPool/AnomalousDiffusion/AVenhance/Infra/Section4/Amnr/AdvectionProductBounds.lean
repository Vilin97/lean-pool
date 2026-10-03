/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CorrectionCardinality

/-! Quantitative finite-product estimates for actual correction monomials. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnrWeight_counts (S H : ℝ) (w : List (Option (Fin 2))) :
    amnrWeight S H w = S ^ amnrSpatialCount w * H ^ amnrMaterialCount w := by
  induction w with
  | nil => simp [amnrWeight, amnrSpatialCount, amnrMaterialCount]
  | cons d w ih =>
    cases d <;> simp only [amnrWeight, List.map_cons, List.prod_cons, amnrSpatialCount,
      amnrMaterialCount, pow_succ] at * <;> rw [ih] <;> ring

/-- A product of actual velocity jets is bounded by its exact count powers. -/
theorem amnrAdvectionProduct_abs_le {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {S H V C : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (A : List AmnrAdvectionFactor) (z : AmnrSpace)
    (hA : ∀ a ∈ A, |amnrWord c a.2 (v a.1) z| ≤ C * V * amnrWeight S H a.2) :
    |amnrAdvectionProduct c v A z| ≤
      (C * V) ^ A.length * S ^ (A.map (fun a => amnrSpatialCount a.2)).sum *
        H ^ (A.map (fun a => amnrMaterialCount a.2)).sum := by
  induction A with
  | nil => simp [amnrAdvectionProduct]
  | cons a A ih =>
    have ha := hA a (by simp)
    have hh := ih (fun b hb => hA b (by simp [hb]))
    change |amnrWord c a.2 (v a.1) z * amnrAdvectionProduct c v A z| ≤ _
    rw [abs_mul]
    have hn := amnrWeight_nonneg hS hH a.2
    have hp := mul_le_mul ha hh (abs_nonneg _) (mul_nonneg (mul_nonneg hC hV) hn)
    refine hp.trans_eq ?_
    rw [amnrWeight_counts]
    simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ, pow_add]
    ring

/-- One scalar jet and its fast factors give the exact total-count bound. -/
theorem amnrAdvectionTermValue_abs_le {c : AmnrSpace → Vec 2}
    {v : Fin 2 → AmnrSpace → ℝ} {f : AmnrSpace → ℝ} {S H V C F : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (t : AmnrAdvectionTerm) (z : AmnrSpace)
    (hA : ∀ a ∈ t.factors, |amnrWord c a.2 (v a.1) z| ≤ C * V * amnrWeight S H a.2)
    (hf : |amnrWord c t.scalarWord f z| ≤ F * V * amnrWeight S H t.scalarWord) :
    |amnrAdvectionTermValue c v f t z| ≤
      C ^ t.factors.length * F * V ^ (t.factors.length + 1) *
        S ^ amnrTermSpatialCount t * H ^ amnrTermMaterialCount t := by
  have hp := amnrAdvectionProduct_abs_le hS hH hV hC t.factors z hA
  change |amnrAdvectionProduct c v t.factors z * amnrWord c t.scalarWord f z| ≤ _
  rw [abs_mul]
  have hh := mul_le_mul hp hf (abs_nonneg _) (by positivity)
  refine hh.trans_eq ?_
  rw [amnrWeight_counts]
  simp only [amnrTermSpatialCount, amnrTermMaterialCount, pow_add, pow_succ, mul_pow]
  ring

end AVenhance.Infra.Section4
