/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamVelocityConstants

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterialSum

/-! Source bounds for the second spatial derivative of the actual velocity. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Two coordinate directions control an operator into any normed real space. -/
theorem amnr_clm_norm_le_two_basis_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L : Vec 2 →L[ℝ] E} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i : Fin 2, ‖L (basisVec i)‖ ≤ B) : ‖L‖ ≤ 2 * B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    funext i
    fin_cases i <;> simp [basisVec_apply]
  calc
    ‖L v‖ = ‖v 0 • L (basisVec 0) + v 1 • L (basisVec 1)‖ := by
      conv_lhs => rw [hv, map_add, map_smul, map_smul]
    _ ≤ |v 0| * ‖L (basisVec 0)‖ + |v 1| * ‖L (basisVec 1)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (v 0 • L (basisVec 0)) (v 1 • L (basisVec 1))
    _ ≤ ‖v‖ * B + ‖v‖ * B := by
      apply add_le_add
      · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (0 : Fin 2))
          (h 0) (norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (1 : Fin 2))
          (h 1) (norm_nonneg _) (norm_nonneg _)
    _ = (2 * B) * ‖v‖ := by ring

/-- The source velocity Lipschitz rate bounds the actual spatial derivative
operator, uniformly at the preceding scale. -/
theorem amnr_previous_velocityJacobian_norm_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖jointSpatialFDeriv (AVenhance.streamVel (Φ (m - 1))) t x‖ ≤
      (2 : ℝ) ^ 20 * AVenhance.a β I.Λ (m - 1) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  rw [jointSpatialFDeriv_eq_slice hb]
  have ha := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  by_cases hbase : m = 1
  · subst m
    rw [show 1 - 1 = (0 : ℕ) by omega, hΦ.1]
    have hzero : AVenhance.streamVel (fun _ _ => (0 : ℝ)) t = (fun _ => (0 : Vec 2)) := by
      rw [AVenhance.streamVel_spatialConstant]
      rfl
    rw [hzero]
    change ‖fderiv ℝ (fun _ : Vec 2 => (0 : Vec 2)) x‖ ≤ _
    rw [(hasFDerivAt_const (0 : Vec 2) x).fderiv, norm_zero]
    positivity
  · apply norm_fderiv_le_of_lip' ℝ (by positivity)
    apply Filter.Eventually.of_forall
    intro y
    exact amnr_streamVel_lipschitz_of_A3 I hΦ hreg (by omega : 1 ≤ m - 1) t y x

end AVenhance.Infra.Section4
