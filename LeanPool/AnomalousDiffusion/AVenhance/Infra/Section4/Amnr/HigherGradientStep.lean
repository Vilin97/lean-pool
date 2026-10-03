/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.BoundedGradientInduction

/-! Actual gradient jets from velocity jets through the current material level. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Bounded velocity jets through the current level and strictly lower
gradient jets imply the actual gradient bound. Centering removes only the
scalar value at the evaluation point, and every derivative budget is retained. -/
theorem amnr_velocityGradient_mixed_abs_le_of_bounded_velocity_jets
    {b : AmnrSpace → Vec 2} {S H V Kv Cb : ℝ} {N : ℕ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hV : 0 ≤ V) (hKv : 0 ≤ Kv) (hCb : 0 ≤ Cb) (hVS : V * S = H)
    (α : List (Fin 2)) (n : ℕ) (hbudget : α.length + 2 * n + 2 ≤ N)
    (i p : Fin 2) (z : AmnrSpace)
    (hv : ∀ η r, r ≤ n → amnrMixedWord η r ≠ [] → η.length + 2 * r + 1 ≤ N →
      |amnrWord b (amnrMixedWord η r) (fun y => b y i) z| ≤
        Kv * V * S ^ η.length * H ^ r)
    (hB : ∀ j q η r, r < n → η.length + 2 * r + 2 ≤ N →
      |amnrWord b (amnrMixedWord η r) (amnrVelocityGradient b j q) z| ≤
        Cb * H * S ^ η.length * H ^ r) :
    |amnrWord b (amnrMixedWord α n) (amnrVelocityGradient b i p) z| ≤
      ((1 + (2 : ℝ) ^ N * Cb) ^ n * Kv) * H * S ^ α.length * H ^ n := by
  let f := fun y : AmnrSpace => b y i
  let g := fun y => f y - f z
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ i).comp hb
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hfb : ∀ η r, r ≤ n → η.length + 2 * r ≤ N - 1 →
      |amnrWord b (amnrMixedWord η r) g z| ≤ (Kv * V) * S ^ η.length * H ^ r := by
    intro η r hr hη
    by_cases he : amnrMixedWord η r = []
    · rw [he]
      change |f z - f z| ≤ _
      rw [sub_self, abs_zero]
      positivity
    · rw [amnrWord_centered_nonempty hb hf _ he z]
      exact hv η r hr he (by omega)
  have hh := amnr_material_gradient_mixed_abs_le_of_bounded_lower_gradient_bounds hb hg
    (N := N - 1) (cut := n) hS hH (mul_nonneg hKv hV) hCb z hfb
    (fun j q η r hr hη => hB j q η r hr (by omega)) n le_rfl α 0 (by omega)
    (by omega) p
  have hgrad : amnrOp b (some p) g = amnrVelocityGradient b i p := by
    have he := amnrWord_centered_nonempty hb hf [some p] (by simp) z
    change amnrOp b (some p) g = amnrOp b (some p) f at he
    rw [he]
    funext y
    exact amnrOp_space (hf.differentiable (by simp) y) p
  have hN : N - 1 + 1 = N := by omega
  simp only [List.replicate_zero, amnrWord, Nat.add_zero] at hh
  rw [hgrad, hN] at hh
  refine hh.trans_eq ?_
  rw [pow_succ]
  calc
    _ = ((1 + (2 : ℝ) ^ N * Cb) ^ n * Kv) * (V * S) * S ^ α.length * H ^ n := by ring
    _ = _ := by rw [hVS]

end AVenhance.Infra.Section4
