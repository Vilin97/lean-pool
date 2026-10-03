/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherMaterialScaling

/-! The actual spatial velocity base case, without a drift amplitude bound. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_velocity_nonempty_spatial_abs_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (α : List (Fin 2)) (hne : α ≠ [])
    (hbudget : α.length + 1 ≤ AVenhance.Nstar β) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      amnrSpatialVelocityConstant (AVenhance.Nstar β) * AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
  rcases List.eq_nil_or_concat α with hnil | ⟨η, p, hα⟩
  · exact (hne hnil).elim
  · have hα' : α = η ++ [p] := by simpa only [List.concat_eq_append] using hα
    rw [hα'] at hbudget ⊢
    let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
    have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y i) := (contDiff_apply ℝ ℝ i).comp hb
    have heq : amnrWord b [some p] (fun y => b y i) = amnrVelocityGradient b i p := by
      funext y
      exact amnrOp_space (hf.differentiable (by simp) y) p
    simp only [List.map_append, List.map_singleton, List.length_append, List.length_singleton]
    rw [amnrWord_append, heq]
    have hh := amnr_velocityGradient_spatial_le_of_A3 I hΦ hreg hm η
      (by simp only [List.length_append, List.length_singleton] at hbudget; omega) i p z
    have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m :=
        m)
    have hscale : AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ = AVenhance.a β I.Λ m := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
      unfold AVenhance.a
      congr 1
      ring
    refine hh.trans_eq ?_
    rw [pow_succ]
    calc
      _ = amnrSpatialVelocityConstant (AVenhance.Nstar β) *
          (AVenhance.epsilon β I.Λ m ^ (β - 1) * (AVenhance.epsilon β I.Λ m)⁻¹) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length := by rw [hscale]
      _ = _ := by ring

end AVenhance.Infra.Section4
