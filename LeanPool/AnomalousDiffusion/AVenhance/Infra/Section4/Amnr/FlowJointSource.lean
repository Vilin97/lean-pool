/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowJointPrimitives

/-! Actual all-order joint source regularity on an open cutoff neighborhood. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Abstract short-interval arithmetic, separated from flow differentiation. -/
theorem amnr_short_source_jacobian_product {A d : ℝ} (hA : 0 < A)
    (hd : |d| ≤ (2 : ℝ) ^ (-24 : ℤ) * A⁻¹) :
    |d| * ((2 : ℝ) ^ 20 * A) ≤ 1 / 16 := by
  have hh := mul_le_mul_of_nonneg_left hd hA.le
  have hc : A * ((2 : ℝ) ^ (-24 : ℤ) * A⁻¹) = (2 : ℝ) ^ (-24 : ℤ) := by field_simp
  rw [hc] at hh
  have hi := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 ^ 20 by positivity)
  have he : (2 : ℝ) ^ 20 * (2 : ℝ) ^ (-24 : ℤ) = 1 / 16 := by norm_num
  rw [he] at hi
  convert hi using 1; ring

/-- An open time neighborhood strictly containing every actual source
cutoff support, including its endpoints. -/
def amnrSourceFlowDomain {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (l : ℤ) : Set AmnrSpace :=
  {z | |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| <
    (2 : ℝ) ^ (-24 : ℤ) * (AVenhance.a β I.Λ (m - 1))⁻¹}

theorem amnrSourceFlowDomain_isOpen {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (l : ℤ) :
    IsOpen (amnrSourceFlowDomain I m l) :=
  isOpen_lt (by fun_prop) continuous_const

/-- Each actual cutoff window lies inside the open smoothness domain. -/
theorem amnr_cutoff_window_mem_sourceFlowDomain {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (z : AmnrSpace)
    (ht : |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
    z ∈ amnrSourceFlowDomain I m l := by
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  refine (ht.trans (amnr_cutoff_window_fits_flow I hm)).trans_lt ?_
  exact mul_lt_mul_of_pos_right (by norm_num) (inv_pos.mpr hA)

/-- The actual pulled source Jacobian has every mixed derivative on the
open cutoff neighborhood. Its quantitative bounds remain separate. -/
theorem amnr_flowGrad_contDiffOn_infty_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (l : ℤ) (i j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 i j)
      (amnrSourceFlowDomain I m l) := by
  intro z hz
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hp := amnr_short_source_jacobian_product hA hz.le
  exact (amnr_pulledFlowGradientEntry_contDiffAt_of_short
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m))
    (AVenhance.flow_isFlow _ (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz)
    (by positivity) (amnr_previous_velocityJacobian_norm_le_of_A3 I hΦ hreg hm)
    ((l : ℝ) * AVenhance.tauPP β I.Λ m) z.1 z.2 (hp.trans (by norm_num)) i j).contDiffWithinAt

end AVenhance.Infra.Section4
