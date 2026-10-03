/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialCompositionRates

/-! The actual pulled flow Jacobian has every source spatial derivative rate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Evaluate one actual matrix entry with unit norm cost. -/
def amnrJacobianEntryProjection (i j : Fin 2) : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec i))

theorem amnrJacobianEntryProjection_norm_le (i j : Fin 2) :
    ‖amnrJacobianEntryProjection i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro L
  change ‖L (basisVec i) j‖ ≤ 1 * ‖L‖
  have hb : ‖basisVec i‖ = 1 := by fin_cases i <;> simp [basisVec, Pi.norm_single]
  exact (norm_le_pi_norm (L (basisVec i)) j).trans ((L.le_opNorm _).trans_eq (by rw [hb]; ring))

/-- The entire finite spatial budget of the actual pulled Jacobian is
controlled uniformly in scale, cutoff index, target time and position. -/
theorem amnr_flowGrad_iteratedFDeriv_norm_le_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m)
    (n : ℕ) (hbudget : n ≤ AVenhance.Nstar β) (i j : Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => I.flowGrad hΦ m l t y i j) x‖ ≤
      (n.factorial : ℝ) * amnrFlowSpatialSourceConstant (AVenhance.Nstar β) ^ (n + 1) *
        (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ n := by
  let X := I.xFlow hΦ m l t
  let Y := I.xFlowInv hΦ m l t
  let K := amnrFlowSpatialSourceConstant (AVenhance.Nstar β)
  let ε := AVenhance.epsilon β I.Λ (m - 1)
  let P := amnrJacobianEntryProjection i j
  let f := P ∘ fderiv ℝ X
  have hX : ContDiff ℝ (⊤ : ℕ∞) X := amnr_xFlow_spatial_contDiff_infty_of_A3 I hΦ hreg hm l t ht
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := amnr_xFlowInv_spatial_contDiff_infty_of_A3 I hΦ hreg hm l t ht
  have hJ := hX.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := P.contDiff.comp hJ
  have hK : 1 ≤ K := (by norm_num : (1 : ℝ) ≤ 2).trans (amnrJacobianJetConstant_two_le _ _)
  have hε : 0 < ε := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hout : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k f (Y x)‖ ≤ K * ε⁻¹ ^ k := by
    intro k hk
    have hh := P.norm_iteratedFDeriv_comp_left (hJ.contDiffAt (x := Y x)) (n := k) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at hh
    exact hh.trans ((mul_le_mul (amnrJacobianEntryProjection_norm_le i j)
      (amnr_xFlow_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm l t ht k (by omega) (Y x))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _))
  have hin : ∀ k, k < n → ‖iteratedFDeriv ℝ (k + 1) Y x‖ ≤ K * ε⁻¹ ^ k := by
    intro k hk
    exact amnr_xFlowInv_iteratedFDeriv_norm_le_of_A3 I hΦ hreg hm l t ht k (by omega) x
  have hh := amnr_iteratedFDeriv_comp_radius_bound hf hY hε hK n x hout hin
  have he : f ∘ Y = fun y => I.flowGrad hΦ m l t y i j := by
    funext y
    change (fderiv ℝ X (Y y) (basisVec i)) j =
      AVenhance.spaceGrad (fun z => X z j) (Y y) i
    unfold AVenhance.spaceGrad
    rw [fderiv_apply (hX.differentiable (by simp) (Y y)) j]
    rfl
  rw [he] at hh
  exact hh.trans_eq (by rw [pow_succ]; ring)

end AVenhance.Infra.Section4
