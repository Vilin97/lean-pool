/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage

@[expose] public section

/-! The summable scalar budgets propagate the genuine low source
guards and absorb the absolute geometric errors. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketInductionScales EulerPacketLowConstants
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketBaseGuardScales EulerPacketPressureScale EulerPacketGeometryLowBounds
  EulerParentRenewalScale EulerParentRenewalPrefix EulerMeanHarmonic

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

theorem initial_step_bound (e : ℝ) (he : e ≤ initialIncrement S.J S.X n) :
    P.low.Be+e ≤ initialCoefficientCost+∑ i ∈ range (n+1), initialIncrement S.J S.X i ∧
    P.low.Bc+e ≤ gradientConstant*S.X^1000+∑ i ∈ range (n+1), initialIncrement S.J S.X i := by
  rw [sum_range_succ]
  constructor <;> linarith only [P.exterior_bound,P.core_bound,he]

theorem pressure_step_bound (e : ℝ) (he : e ≤ pressureIncrement S.J S.X n) :
    P.low.K+e ≤ initialCoefficientCost+literalInitialPressureCost S.D S.X+
      ∑ i ∈ range (n+1), pressureIncrement S.J S.X i := by
  rw [sum_range_succ]
  linarith only [P.pressure_bound,he]

theorem next_localized (T ei ep : ℝ) (hT : 0 ≤ T) (hTcap : T ≤ baseHorizon S.J S.X)
    (hi0 : 0 ≤ ei) (hp0 : 0 ≤ ep)
    (hi : ei ≤ initialIncrement S.J S.X n) (hp : ep ≤ pressureIncrement S.J S.X n) :
    (P.low.K+ep)*(T^2/2)+(P.low.Be+ei)*T+
      boundaryLocalizationC2*(P.low.Bc+ei)*P.low.r^3*T ≤ 1/2 := by
  have hib := P.initial_step_bound ei hi
  have hpb := P.pressure_step_bound ep hp
  have his := S.initial_partial_sum (n+1)
  have hps := S.pressure_partial_sum (n+1)
  have hd := S.delta_small
  have hb := S.first.pressure_small
  rw [P.radius_eq]
  apply S.localized_guard T (P.low.K+ep) (P.low.Be+ei) (P.low.Bc+ei) hT
    (add_nonneg P.low.K_nonneg hp0) (add_nonneg P.low.Be_nonneg hi0)
    (add_nonneg P.low.Bc_nonneg hi0)
  · linarith only [hpb,hps,hd,hb]
  · linarith only [hib.1,his,hd]
  · linarith only [hib.2,his,hd]
  · exact hTcap

theorem ratio_absorption (r : ℝ) (hr : 0 ≤ r)
    (hbad : 2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*r ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n)
        :
    gradientConstant*previousShear S.J S.X n+shear S.J S.X n*(goodRatio+r)+
        (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ gradientConstant*shear S.J S.X n ∧
    hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n+
      2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*(goodRatio+r)+
        (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤
      hessianConstant*shear S.J S.X n*previousShear S.J S.X n := by
  have hsum : badCost S.J 4 gradientConstant gradientConstant hessianConstant 80
      (scaleSequence S.J S.X) n+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by
    have h := S.initial_series.term_le n
    change initialIncrement S.J S.X n ≤ _
    exact h.trans (by linarith only [S.delta_small])
  have hM : 1 ≤ 2*gradientConstant*previousShear S.J S.X n := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    nlinarith only [gradient_properties.1,h]
  have hgrad : shear S.J S.X n*r ≤
      2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*r := by
    have h := mul_le_mul_of_nonneg_right hM (mul_nonneg (zero_le_one.trans (S.shear_one n)) hr)
    nlinarith only [h]
  have hg : shear S.J S.X n*r+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by
    linarith only [hgrad,hbad,hsum]
  have hh : 2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*r+
      (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by linarith only [hbad,hsum]
  exact ⟨EulerPacketLowBoundPropagation.gradient_bound _ _ _ _ _ _ gradient_properties.1
      (S.previousShear_one n) (S.shear_one n) (S.shear_separation n) gradient_properties.2.2 hg,
    EulerPacketLowBoundPropagation.hessian_bound _ _ _ _ _ _ _ _ hessian_properties.1
      (S.previousShear_one n) (S.shear_one n) (S.olderShear_le n) (S.shear_separation n)
      hessian_properties.2.2 hh⟩

theorem next_frame_bounds :
    1 ≤ frameConstant*(1+previousShear S.J S.X n) ∧
    gradientConstant*previousShear S.J S.X n ≤ frameConstant*(1+previousShear S.J S.X n) ∧
    (gradientConstant*previousShear S.J S.X n)^2+
        hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n ≤
      (frameConstant*(1+previousShear S.J S.X n))^2 := by
  have hp := S.previousShear_one n
  have hp0 := zero_le_one.trans hp
  have hf0 := zero_le_one.trans frame_properties.1
  have hold := S.olderShear_le n
  have hcf := frame_properties.2.1
  have hCH := frame_properties.2.2
  refine ⟨one_le_mul_of_one_le_of_one_le frame_properties.1 (by linarith only [hp]),?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hcf hp0).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hf0)
  · have h1 := mul_le_mul_of_nonneg_left hold (mul_nonneg hessian_nonneg hp0)
    have h2 := mul_le_mul_of_nonneg_right hCH (sq_nonneg (previousShear S.J S.X n))
    have h3 := mul_nonneg (sq_nonneg frameConstant)
      (show 0 ≤ 1+2*previousShear S.J S.X n by positivity)
    nlinarith only [h1,h2,h3]

theorem coupling_step (a : ℝ)
    (h : |a/P.frame.a-1| ≤ renewalCost S.J S.D 4 c frameConstant S.X n) :
    |a-1| ≤ 2*∑ i ∈ range (n+1), renewalCost S.J S.D 4 c frameConstant S.X i := by
  have he := S.renewal_series.nonneg n
  have hd := relative_step_error P.coupling_pos P.coupling_bounds.2 he h
  have ht := abs_add_le (a-P.frame.a) (P.frame.a-1)
  rw [show a-P.frame.a+(P.frame.a-1)=a-1 by ring] at ht
  rw [sum_range_succ]
  linarith only [hd,ht,P.coupling_error]

theorem tilt_step (σ : ℝ)
    (h : |(scaleSequence S.J S.X (n+1))^2*σ^2-1| ≤
      renewalCost S.J S.D 4 c frameConstant S.X n) :
    1/2 ≤ σ^2*(scaleSequence S.J S.X (n+1))^2 ∧
      σ^2*(scaleSequence S.J S.X (n+1))^2 ≤ 2 := by
  have hh := abs_le.mp h
  have he := S.renewal_series.term_le n
  constructor <;> nlinarith only [hh.1,hh.2,he]

end EulerPacketInduction.Stage

namespace EulerParentPacketFrames.RenewalAtTarget

open InnerProductSpace EulerPacketMovingFrame EulerPacketSourceGeometry EulerPacketNormalizedPrimary

theorem background_compression_of_error_le_one
    {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {D : EulerTransversePacketProvider.Data V} {G : PhysicalGeometryData ι}
    {P : ParentFrame D G.targetTime} (J : RenewalAtTarget G P) (e : ℝ) (he : e ≤ 1) :
    ⟪P.B G.targetTime (unit (P.m G.targetTime)),unit (P.m G.targetTime)⟫_ℝ+e < 0 := by
  rw [J.background_compression_eq]
  have hm := G.compression_margin he
  have hc := G.nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.RenewalAtTarget
