/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondSpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity

/-! Spatial C² regularity of a smooth periodic flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- On a forward interval, a smooth flow map is twice continuously
differentiable in its initial point. -/
theorem flow_spatial_contDiff_two_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) (hst : s ≤ t) :
    ContDiff ℝ 2 (fun x => X t x s) := by
  let f : Vec 2 → Vec 2 := fun x => X t x s
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ f x
  let B : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun x => fderiv ℝ J x
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨Cjac, hCjac₀, hCjac⟩ := exists_global_spatialFDeriv_lipschitz hb
  obtain ⟨C₂, hC₂₀, hC₂⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  obtain ⟨C₃, hC₃₀, hC₃⟩ := exists_global_spatialSecondDerivativeEval_lipschitz hb
  let Csp := flowSecondVariationLipschitzConstant L M Cjac C₂ C₃ s t
  have hCsp₀ : 0 ≤ Csp := by
    obtain ⟨C, hC₀, hCeq, _⟩ :=
      exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₃ hL₀ hM₀ hCjac₀ hC₂₀ hC₃₀ hL hM hCjac hC₂ hC₃
        0 0 s t hst 0 0
    dsimp [Csp]
    rw [← hCeq]
    exact hC₀
  have hJderiv (x : Vec 2) : HasFDerivAt J (B x) x := by
    obtain ⟨_, _, Bx, _, hD⟩ :=
      exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX x s t hst
    have hEq : B x = Bx := by
      dsimp [B, J, f]
      exact hD.fderiv
    rw [hEq]
    simpa [J, f] using hD
  have hBeval (x h k : Vec 2) :
      B x h k = flowSecondVariation hb hX x s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
        h k t 0 s := by
    obtain ⟨_, _, Bx, hBx, hD⟩ :=
      exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX x s t hst
    have hEq : B x = Bx := by
      dsimp [B, J, f]
      exact hD.fderiv
    rw [hEq]
    exact hBx h k
  have hBdiff (x y : Vec 2) : ‖B y - B x‖ ≤ Csp * ‖x - y‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hCsp₀ (norm_nonneg _))
    intro h
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hCsp₀ (norm_nonneg _)) (norm_nonneg _))
    intro k
    obtain ⟨Cxy, _, hCxyEq, hpoint⟩ :=
      exists_flow_secondVariation_lipschitz_all_times_of_le hb hX
        L M Cjac C₂ C₃ hL₀ hM₀ hCjac₀ hC₂₀ hC₃₀ hL hM hCjac hC₂ hC₃
        x y s t hst h k
    have hpoint' := hpoint t ⟨hst, le_rfl⟩
    rw [hCxyEq] at hpoint'
    calc
      ‖((B y - B x) h) k‖ = ‖B y h k - B x h k‖ := by simp
      _ = ‖flowSecondVariation hb hX y s
            (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX y s) |>.1)
            h k t 0 s - flowSecondVariation hb hX x s
            (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
            h k t 0 s‖ := by rw [hBeval, hBeval]
      _ ≤ Csp * ‖x - y‖ * ‖h‖ * ‖k‖ := hpoint'
  let KN : ℝ≥0 := ⟨Csp, hCsp₀⟩
  have hBlip : LipschitzWith KN B := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖B x - B y‖ = ‖B y - B x‖ := norm_sub_rev (B x) (B y)
      _ ≤ Csp * ‖x - y‖ := hBdiff x y
  have hBcont : Continuous B := hBlip.continuous
  have hJcontDiff : ContDiff ℝ 1 J := by
    rw [contDiff_one_iff_hasFDerivAt]
    exact ⟨B, hBcont, hJderiv⟩
  have hfderiv (x : Vec 2) : HasFDerivAt f (J x) x := by
    obtain ⟨_, Jx, _, _, hD⟩ := exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
    have hEq : J x = Jx := by
      dsimp [J, f]
      exact hD.fderiv
    rw [hEq]
    exact hD
  rw [show (2 : ℕ∞ω) = (1 : ℕ) + 1 by norm_num,
    contDiff_succ_iff_hasFDerivAt]
  exact ⟨J, hJcontDiff, hfderiv⟩

/-- Every fixed-time map of a smooth flow is twice continuously
differentiable in its initial point. -/
theorem flow_spatial_contDiff_two
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) :
    ContDiff ℝ 2 (fun x => X t x s) := by
  by_cases hst : s ≤ t
  · exact flow_spatial_contDiff_two_of_le hb hX s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br := regularityReverseTimeField b
    let Xr := regularityReverseTimeFlow X
    have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
    have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
    have hforward : -s ≤ -t := by linarith
    have hC2 := flow_spatial_contDiff_two_of_le hbr hXr (-s) (-t) hforward
    simpa [Xr, regularityReverseTimeFlow] using hC2

end AVenhance.Infra.Flow
