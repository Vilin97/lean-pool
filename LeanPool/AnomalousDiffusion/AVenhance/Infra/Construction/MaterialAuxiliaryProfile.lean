/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialAuxiliaryFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TransportProfileJets

/-! Transported profiles at auxiliary spatial orders, with material cutoff
orders still checked against the literal source cutoff. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Construction
open AVenhance.Infra.Section4

/-- Every actual transported profile derivative retains the fine spatial
radius. Coarse flow derivatives are absorbed by the actual scale separation. -/
theorem material_aux_transportProfile_iteratedFDeriv_norm_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (k l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => AVenhance.psi β I.Λ m k (I.xFlowInv hΦ m l t y)) x‖ ≤
      amnrTransportSpatialConstant (N) * AVenhance.a β I.Λ m *
        AVenhance.epsilon β I.Λ m ^ 2 * (AVenhance.epsilon β I.Λ m)⁻¹ ^ n := by
  let E := AVenhance.epsilon β I.Λ m
  let P := AVenhance.epsilon β I.Λ (m - 1)
  let A := AVenhance.a β I.Λ m
  let K := amnrFlowSpatialSourceConstant N
  let Y := I.xFlowInv hΦ m l t
  have hE : 0 < E := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hP : 0 < P := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 < A := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hK : 1 ≤ K := (by norm_num : (1 : ℝ) ≤ 2).trans (amnrJacobianJetConstant_two_le _ _)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hEP : E ≤ P := by
    have hs := AVenhance.Infra.Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    rw [Nat.sub_add_cancel hm] at hs
    have hL : 1 ≤ (I.Λ : ℝ) := by exact_mod_cast (show 1 ≤ I.Λ by have := I.two_pow_seven_le; omega)
    exact (le_mul_of_one_le_left hE.le hL).trans hs
  have hout : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j (AVenhance.psi β I.Λ m k) (Y x)‖ ≤
      (A * E ^ 2 * (2 * Real.pi) ^ N) * E⁻¹ ^ j := by
    intro j hj
    have hh := amnr_psi_iteratedFDeriv_norm_le I m k j (Y x)
    refine hh.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hπ (hj.trans hbudget)) (by positivity)) (by positivity)
  have hin : ∀ j, j < n → ‖iteratedFDeriv ℝ (j + 1) Y x‖ ≤ K * E⁻¹ ^ j := by
    intro j hj
    have hh := amnr_aux_xFlowInv_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm l t ht
      (N := N) j (by omega) x
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hP.le) (inv_anti₀ hE hEP) j) (by linarith))
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y :=
    (amnr_xFlowInv_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hh := amnr_iteratedFDeriv_comp_radius_bound (amnr_psi_contDiff I m k) hY hE hK n x hout hin
  refine hh.trans ?_
  have hc : (n.factorial : ℝ) * (2 * Real.pi) ^ N * K ^ n ≤ amnrTransportSpatialConstant N := by
    unfold amnrTransportSpatialConstant
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hbudget) (by
        positivity))
      (pow_le_pow_right₀ hK hbudget) (by positivity) (by positivity)
  calc
    _ = ((n.factorial : ℝ) * (2 * Real.pi) ^ N * K ^ n) * A * E ^ 2 * E⁻¹ ^ n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
        hA.le)
      (sq_nonneg E)) (by positivity)

end AVenhance.Infra.Construction

end
