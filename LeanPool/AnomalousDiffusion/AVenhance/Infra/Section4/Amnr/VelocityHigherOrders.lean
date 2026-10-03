/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamVelocityConstants

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveJetOperators

/-! Auxiliary finite-order stream-regularity bounds, without restricting the paper budget.
The stream-regularity estimates control every spatial order. Auxiliary constants may use a larger
    finite
order while each paper derivative retains its separately checked budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

theorem amnr_velocityGradient_spatial_le_of_A3_auxiliary_budget {β C : ℝ} (I :
    AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (N : ℕ) (hbudget : α.length ≤ N)
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant (N) * AVenhance.a β I.Λ m *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hh := (amnr_velocityGradient_spatialWord_raw_of_A3 I hΦ hreg hm α i p z).trans
    (amnrStreamSpatialEnvelope_le_uniform hA.le hE
      (show α.length ≤ N by omega))
  simpa only [Real.norm_eq_abs] using hh

/-- The previous-scale spatial primitive bound retains the actual amplitude,
including the zero-stream base case. -/
theorem amnr_previous_velocityGradient_spatial_raw_le_of_A3_auxiliary_budget {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (α : List (Fin 2))
    (N : ℕ) (hbudget : α.length ≤ N) (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant (N) * AVenhance.a β I.Λ (m - 1) *
        (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ α.length := by
  have hC := (amnrSpatialVelocityConstant_pos (N)).le
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  by_cases hbase : m = 1
  · subst m
    have hB : amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (1 - 1)) y.1 y.2) i p =
        (0 : AmnrSpace → ℝ) := by
      funext y
      rw [show 1 - 1 = (0 : ℕ) by omega, hΦ.1]
      rw [AVenhance.streamVel_spatialConstant]
      change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y.2 (basisVec p) = 0
      rw [fderiv_const_apply]
      rfl
    rw [hB, amnrWord_zero]
    simp only [Pi.zero_apply, abs_zero]
    positivity
  · exact amnr_velocityGradient_spatial_le_of_A3_auxiliary_budget I hΦ hreg
      (by omega : 1 ≤ m - 1) α N hbudget i p z

theorem amnr_previous_velocityGradient_iteratedFDeriv_norm_le_of_A3_auxiliary_budget {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (N : ℕ) (hbudget : n ≤ N)
    (i p : Fin 2) (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
      (fun y => amnrVelocityGradient (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) i p (t,
          y)) x‖ ≤
      (2 : ℝ) ^ n * (amnrSpatialVelocityConstant (N) *
        AVenhance.a β I.Λ (m - 1) * (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n) := by
  let b := fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hB : ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient b i p) :=
    contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn i p)
  apply amnr_iteratedFDeriv_norm_le_of_spatial_words
    (hB.comp (contDiff_const.prodMk contDiff_id)) n x
  · have := amnrSpatialVelocityConstant_pos (N)
    have := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
    have := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
        - 1)
    positivity
  intro α hα
  have hh := amnr_previous_velocityGradient_spatial_raw_le_of_A3_auxiliary_budget I hΦ hreg hm α N
    (by omega) i p (t, x)
  rw [amnrWord_spatial_slice hB, hα] at hh
  exact hh

theorem amnr_previous_velocityJacobian_iteratedFDeriv_norm_le_of_A3_auxiliary_budget {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (N : ℕ) (hbudget : n ≤ N)
    (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => jointSpatialFDeriv (AVenhance.streamVel (Φ (m - 1))) t y) x‖ ≤
      (2 : ℝ) ^ (n + 1) * (amnrSpatialVelocityConstant (N) *
        AVenhance.a β I.Λ (m - 1) * (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n) := by
  let Q := amnrSpatialVelocityConstant (N) *
    AVenhance.a β I.Λ (m - 1) * (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n
  have hQ : 0 ≤ Q := by
    have := amnrSpatialVelocityConstant_pos (N)
    have := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
    have := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
        - 1)
    dsimp [Q]
    positivity
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hP : 0 ≤ ∏ j : Fin n, ‖v j‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hh : ‖iteratedFDeriv ℝ n
      (fun y => jointSpatialFDeriv (AVenhance.streamVel (Φ (m - 1))) t y) x v‖ ≤
      2 * ((2 : ℝ) ^ n * Q * ∏ j : Fin n, ‖v j‖) := by
    apply amnr_clm_norm_le_two_basis_general (by positivity)
    intro p
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs, amnr_velocityJacobian_iteratedFDeriv_coordinate
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m))]
    have hc := amnr_previous_velocityGradient_iteratedFDeriv_norm_le_of_A3_auxiliary_budget I hΦ
        hreg hm n N hbudget i p t x
    have he := (iteratedFDeriv ℝ n
      (fun y => amnrVelocityGradient (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) i p (t,
          y)) x).le_opNorm v
    rw [Real.norm_eq_abs] at he
    exact he.trans (mul_le_mul_of_nonneg_right hc hP)
  exact hh.trans_eq (by rw [pow_succ]; ring)

end AVenhance.Infra.Section4
