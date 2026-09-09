/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationLipschitz

@[expose] public section

/-! The actual source coefficient differences retain a factor ell.
The stationary history sensitivity is linear in these differences, so
its computed Lipschitz constant retains that factor as well. -/

noncomputable section

namespace EulerMeanCoefficients.SmoothCoefficientPath

open Set EulerSmoothLimit
open scoped BoundedContinuousFunction

variable {J V : Type} [TopologicalSpace J] [CompactSpace J]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V)) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V)) := inferInstance

theorem derivative_norm_le_of_bound (A : SmoothCoefficientPath J V) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ 1 (A.field t : Space → V) x‖ ≤ C) :
    ‖A.derivative.field‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).2
  intro t
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  change ‖A.derivativeField t x‖ ≤ C
  rw [A.derivativeField_eq]
  simpa only [norm_iteratedFDeriv_one] using hb t x

end EulerMeanCoefficients.SmoothCoefficientPath

namespace EulerParentPacketFrames.LabelData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketParentLabelBounds EulerPacketCofactor EulerGevrey EulerTransverseBoundedFrame
  EulerTransverseFrameCoordinates EulerTransversePacketProvider EulerPacketActivationHistory
  EulerTransverseHistoryBounds
open scoped BoundedContinuousFunction

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m) (S : Set Space) (hS : IsCompact S)

def frameDifferenceCost : ℝ := frameAmplitude L.K*coefficientRadius L.K
def firstDifferenceCost : ℝ := gradientAmplitude L.K*coefficientRadius L.K
def normalDifferenceCost : ℝ := 9*(frameAmplitude L.K)^2*coefficientRadius L.K
def strainDifferenceCost : ℝ := 27*(frameAmplitude L.K)^2*gradientAmplitude L.K*coefficientRadius
  L.K

theorem scaled_first_majorant (A : ℝ) :
    A*majorant L.scaledRadius 0 1=(A*coefficientRadius L.K)*G.ell := by
  norm_num [majorant,scaledRadius]
  ring

theorem source_frame_derivative_norm :
    ‖(G.transverseData m hm R S hS).frame.derivative.field‖ ≤ L.frameDifferenceCost*G.ell := by
  have h0 := frameAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold frameDifferenceCost;
    positivity)
  intro t x
  have h := coefficient_derivative_bound m R G.frame.toSmoothCoefficientPath 1
    (frameAmplitude L.K*majorant L.scaledRadius 0 1) (L.frame_scaled_bound 1) t x
  rw [L.scaled_first_majorant] at h
  exact h

theorem source_first_derivative_norm :
    ‖(G.transverseData m hm R S hS).frameDerivative.derivative.field‖ ≤ L.firstDifferenceCost*G.ell
      := by
  have h0 := gradientAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold firstDifferenceCost;
    positivity)
  intro t x
  have h := coefficient_derivative_bound m R G.first.toSmoothCoefficientPath 1
    (gradientAmplitude L.K*majorant L.scaledRadius 0 1) (L.first_scaled_bound 1) t x
  rw [L.scaled_first_majorant] at h
  exact h

theorem source_normal_derivative_norm :
    ‖(G.transverseData m hm R S hS).normal.derivative.field‖ ≤ L.normalDifferenceCost*G.ell := by
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold normalDifferenceCost;
    positivity)
  intro t x
  have h := normalCoefficient_derivative_bound m G.inverse.toSmoothCoefficientPath hm 1
    ((9*(frameAmplitude L.K)^2)*majorant L.scaledRadius 0 1) (L.inverse_scaled_bound 1) t x
  rw [L.scaled_first_majorant] at h
  exact h

theorem source_strain_derivative_norm :
    ‖(G.transverseData m hm R S hS).M.derivative.field‖ ≤ L.strainDifferenceCost*G.ell := by
  have h0 := gradientAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold strainDifferenceCost;
    positivity)
  intro t x
  have h := L.strain_scaled_bound 1 t x
  rw [L.scaled_first_majorant] at h
  exact h

theorem source_curvature_derivative_norm (H : LowBounds G) :
    ‖(G.historyData m hm R S hS H).H.derivative.field‖ ≤ L.strainDifferenceCost*G.ell := by
  have h0 := gradientAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold strainDifferenceCost;
    positivity)
  intro t x
  have h := L.curvature_scaled_bound 1 t x
  rw [L.scaled_first_majorant] at h
  exact h

variable [CompleteSpace U]

def historyDifferenceScaleCost (H : LowBounds G) : ℝ :=
  let D := G.transverseData m hm R S hS
  let B := G.historyData m hm R S hS H
  historyDifferenceCost G.T D.frameLower ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (G.T*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+G.T^2*‖B.H.field‖)
    (historyTransportCost (D := D)) L.frameDifferenceCost L.firstDifferenceCost
      L.strainDifferenceCost

omit [CompleteSpace U] in
theorem source_history_derivative_scale (H : LowBounds G) :
    historyLabelDifferenceCost (G.historyData m hm R S hS H) ≤
      L.historyDifferenceScaleCost m hm R S hS H*G.ell := by
  apply historyDifferenceCost_le_scale
  · exact G.T_pos.le
  · exact (G.transverseData m hm R S hS).frameLower_pos.le
  · positivity
  · positivity
  · exact add_nonneg (mul_nonneg G.T_pos.le (norm_nonneg _)) (norm_nonneg _)
  · positivity
  · exact historyTransportCost_nonneg
  · exact L.source_frame_derivative_norm m hm R S hS
  · exact L.source_first_derivative_norm m hm R S hS
  · exact L.source_curvature_derivative_norm m hm R S hS H

end EulerParentPacketFrames.LabelData
