/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FastVelocityMaterial

/-! Fine material rate comparisons with the corrected supergeometric factor. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Ingredients

/-- The corrected factor retained in the material rate comparison. -/
def amnrFineScaleFactor (β : ℝ) : ℝ := 1 + supergeoConstant β

/-- A uniform weak supergeometric upper bound, including the base scale. -/
theorem amnr_epsilon_weak_supergeo {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    AVenhance.epsilon β I.Λ m ≤ amnrFineScaleFactor β *
      AVenhance.epsilon β I.Λ (m - 1) ^ AVenhance.q β := by
  have hq := one_lt_q I.one_lt_beta I.beta_lt
  have hs : 0 ≤ supergeoConstant β := by unfold supergeoConstant; positivity
  have hB : 1 ≤ amnrFineScaleFactor β := by unfold amnrFineScaleFactor; linarith
  have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1)
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  by_cases hbase : m = 1
  · subst m
    have hzero : AVenhance.epsilon β I.Λ (1 - 1) = 1 := by simp [AVenhance.epsilon]
    rw [hzero, Real.one_rpow, mul_one]
    exact (AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := 1)).trans hB
  · have hh := (epsilon_supergeo I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (by omega : 1 ≤ m - 1)).2
    rw [Nat.sub_add_cancel hm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg he.le _))
    unfold amnrFineScaleFactor
    have hc := mul_le_mul_of_nonneg_left he1 hs
    simpa only [mul_one, add_comm] using add_le_add_left hc 1

/-- The source exponent gap absorbs the fine time radius into the current
amplitude. Only scalar polynomial identities enter this step. -/
theorem amnr_fine_material_exponent {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    AVenhance.q β * (β - 2) ≤ β - 2 - 4 * AVenhance.delta β := by
  have hh := AVenhance.Infra.Numeric.eight_delta_identity hβ
  have hd := delta_pos hβ hβ'
  have hq := one_lt_q hβ hβ'
  have hg := gamma_pos hβ hβ'
  have hqg : 0 ≤ AVenhance.q β * AVenhance.gamma β := by positivity
  nlinarith only [hh, hd, hqg]

/-- A β-dependent constant, independent of the scale, for the fine rate. -/
def amnrFineMaterialConstant (β : ℝ) : ℝ :=
  (2 : ℝ) ^ 33 * amnrFineScaleFactor β ^ (2 - β)

/-- The actual fine cutoff rate is controlled by the current amplitude.
The corrected factor is used rather than a false uniform supergeometric constant. -/
theorem amnr_inverse_tau_le_current_amplitude {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    (AVenhance.tau β I.Λ m)⁻¹ ≤ amnrFineMaterialConstant β * AVenhance.a β I.Λ m := by
  have hq := one_lt_q I.one_lt_beta I.beta_lt
  have hs : 0 ≤ supergeoConstant β := by unfold supergeoConstant; positivity
  have hB : 0 < amnrFineScaleFactor β := by unfold amnrFineScaleFactor; linarith
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1)
  have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1)
  have hem := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hτ := I.tau_pos' m
  have hlo := (tau_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).1
  have hτinv := (inv_le_inv₀ hτ (by positivity : 0 < (2 : ℝ) ^ (-33 : ℤ) *
    AVenhance.epsilon β I.Λ (m - 1) ^ (2 - β + 4 * AVenhance.delta β))).mpr hlo
  have hτbound : (AVenhance.tau β I.Λ m)⁻¹ ≤ (2 : ℝ) ^ 33 *
      AVenhance.epsilon β I.Λ (m - 1) ^ (β - 2 - 4 * AVenhance.delta β) := by
    refine hτinv.trans_eq ?_
    rw [mul_inv_rev, ← Real.rpow_neg he.le]
    norm_num only [zpow_neg, zpow_natCast, inv_inv, Nat.reducePow]
    rw [show -(2 - β + 4 * AVenhance.delta β) = β - 2 - 4 * AVenhance.delta β by ring]
    ring
  have hpow := Real.rpow_le_rpow_of_nonpos
    hem (amnr_epsilon_weak_supergeo I hm)
    (show β - 2 ≤ 0 by linarith [I.beta_lt])
  rw [Real.mul_rpow hB.le (Real.rpow_nonneg he.le _), ← Real.rpow_mul he.le] at hpow
  have hcancel : amnrFineScaleFactor β ^ (2 - β) * amnrFineScaleFactor β ^ (β - 2) = 1 := by
    rw [← Real.rpow_add hB]
    simp
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg hB.le (2 - β))
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  have hexp := Real.rpow_le_rpow_of_exponent_ge he he1
    (amnr_fine_material_exponent I.one_lt_beta I.beta_lt)
  refine hτbound.trans ?_
  unfold amnrFineMaterialConstant AVenhance.a
  exact (mul_le_mul_of_nonneg_left (hexp.trans hscaled)
    (show 0 ≤ (2 : ℝ) ^ 33 by positivity)).trans_eq (by ring)

end AVenhance.Infra.Section4
