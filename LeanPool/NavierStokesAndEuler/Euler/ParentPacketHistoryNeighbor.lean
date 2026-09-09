/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData

@[expose] public section

/-! Spatial variation of the actual activation history retains the
parent's label scale.  The constants are computed from the prescribed
coefficients and the older frame, not from an estimate on the new primary. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketParentLabelBounds EulerGevrey EulerTransverseBoundedFrame
  EulerTransverseFrameCoordinates EulerTransversePacketProvider EulerPacketActivationHistory
  EulerTransverseHistoryBounds EulerTimeIntervalRestriction EulerPacketSourceGeometry
  EulerPacketMovingFrame
open scoped BoundedContinuousFunction

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)

omit [CompleteSpace U] in
theorem initial_frame_derivative_norm :
    ‖((G.transverseData m hm R S hS).initial τ hτ hτT.le).frame.derivative.field‖ ≤
      L.frameDifferenceCost*G.ell := by
  have h0 := frameAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold frameDifferenceCost;
    positivity)
  intro t x
  have h := coefficient_derivative_bound m R G.frame.toSmoothCoefficientPath 1
    (frameAmplitude L.K*majorant L.scaledRadius 0 1) (L.frame_scaled_bound 1)
    (initialInclusion G.T τ hτT.le t) x
  rw [L.scaled_first_majorant] at h
  exact h

omit [CompleteSpace U] in
theorem initial_first_derivative_norm :
    ‖((G.transverseData m hm R S hS).initial τ hτ hτT.le).frameDerivative.derivative.field‖ ≤
      L.firstDifferenceCost*G.ell := by
  have h0 := gradientAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold firstDifferenceCost;
    positivity)
  intro t x
  have h := coefficient_derivative_bound m R G.first.toSmoothCoefficientPath 1
    (gradientAmplitude L.K*majorant L.scaledRadius 0 1) (L.first_scaled_bound 1)
    (initialInclusion G.T τ hτT.le t) x
  rw [L.scaled_first_majorant] at h
  exact h

omit [CompleteSpace U] in
theorem initial_curvature_derivative_norm :
    ‖(G.historyOn H m hm R S hS τ hτ hτT).H.derivative.field‖ ≤
      L.strainDifferenceCost*G.ell := by
  have h0 := gradientAmplitude_nonneg L.K
  have h1 := coefficientRadius_nonneg L.K
  have hell := G.ell_pos
  apply SmoothCoefficientPath.derivative_norm_le_of_bound _ _ (by unfold strainDifferenceCost;
    positivity)
  intro t x
  have h := L.curvature_scaled_bound 1 (initialInclusion G.T τ hτT.le t) x
  rw [L.scaled_first_majorant] at h
  exact h

/-- The coefficient of the label scale in the actual history difference
bound.  All zeroth norms belong to the restricted source coefficients. -/
def initialHistoryDifferenceScaleCost : ℝ :=
  let D := (G.transverseData m hm R S hS).initial τ hτ hτT.le
  let B := G.historyOn H m hm R S hS τ hτ hτT
  historyDifferenceCost τ D.frameLower ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (τ*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+τ^2*‖B.H.field‖)
    (historyTransportCost (D := D)) L.frameDifferenceCost L.firstDifferenceCost
      L.strainDifferenceCost

omit [CompleteSpace U] in
theorem initial_history_derivative_scale :
    historyLabelDifferenceCost (G.historyOn H m hm R S hS τ hτ hτT) ≤
      L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT*G.ell := by
  apply historyDifferenceCost_le_scale
  · exact hτ.le
  · exact ((G.transverseData m hm R S hS).initial τ hτ hτT.le).frameLower_pos.le
  · positivity
  · positivity
  · exact add_nonneg (mul_nonneg hτ.le (norm_nonneg _)) (norm_nonneg _)
  · positivity
  · exact historyTransportCost_nonneg
  · exact L.initial_frame_derivative_norm m hm R S hS τ hτ hτT
  · exact L.initial_first_derivative_norm m hm R S hS τ hτ hτT
  · exact L.initial_curvature_derivative_norm m hm R S hS H τ hτ hτT

/-- The actual neighbor coefficient after extracting the one factor of
ell supplied by the parent spatial derivative estimates. -/
def neighborScaleCost
    (P : ParentFrame (G.transverseData m hm R S hS) τ) (CM CH : ℝ) : ℝ :=
  L.strainDifferenceCost+
    3*L.normalDifferenceCost/(P.rayScale hτ hτT*P.epsilon)+
    2*(L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT)*
      P.terminalBound CM CH/P.epsilon

omit [CompleteSpace U] in
theorem source_neighbor_scale
    (P : ParentFrame (G.transverseData m hm R S hS) τ) (CM CH : ℝ)
    (_hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hshear : 0 < P.shear) (heps : 0 < P.epsilon) :
    P.neighborCost hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ≤
      L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell := by
  have hray := Guards.rayScale_pos hτ hτT P
  have hterminal : 0 ≤ P.terminalBound CM CH := by
    unfold ParentFrame.terminalBound EulerTransverseActivationSelection.activationConstant
    positivity [(G.transverseData m hm R S hS).inverseBound_pos]
  have hn := L.source_normal_derivative_norm m hm R S hS
  have hm' := L.source_strain_derivative_norm m hm R S hS
  have hh := L.initial_history_derivative_scale m hm R S hS H τ hτ hτT
  unfold ParentFrame.neighborCost neighborScaleCost
  calc
    _ ≤ L.strainDifferenceCost*G.ell+
        3*(L.normalDifferenceCost*G.ell)/(P.rayScale hτ hτT*P.epsilon)+
        2*(L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT*G.ell)*
          P.terminalBound CM CH/P.epsilon := by gcongr
    _ = _ := by ring

omit [CompleteSpace U] in
theorem source_totalError_bound
    (P : ParentFrame (G.transverseData m hm R S hS) τ) (CM CH ρ e n : ℝ)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hshear : 0 < P.shear) (heps : 0 < P.epsilon)
    (hρ : 0 ≤ ρ) (herr : P.error ≤ e)
    (hn : L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell*ρ ≤ n) :
    P.totalError hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) CM CH ρ ≤ e+n := by
  exact add_le_add herr ((mul_le_mul_of_nonneg_right
    (L.source_neighbor_scale m hm R S hS H τ hτ hτT P CM CH hCM hCH hshear heps) hρ).trans hn)

end EulerParentPacketFrames.LabelData
