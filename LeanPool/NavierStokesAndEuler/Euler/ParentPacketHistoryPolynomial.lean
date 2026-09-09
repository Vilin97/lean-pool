/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHistoryNeighbor
public import LeanPool.NavierStokesAndEuler.Euler.ParentHistoryCostPolynomial

@[expose] public section

/-! The actual restricted history sensitivity has a single fixed
polynomial dependence on the parent label constant and reciprocal
history length. The small physical scale remains a multiplicative factor. -/

noncomputable section

namespace EulerMeanCoefficients.SmoothCoefficientPath

open EulerSmoothLimit
open scoped BoundedContinuousFunction

variable {J V : Type} [TopologicalSpace J] [CompactSpace J]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance

theorem field_norm_le_of_bound (A : SmoothCoefficientPath J V) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖A.field t x‖ ≤ C) : ‖A.field‖ ≤ C :=
  (ContinuousMap.norm_le _ hC).2 fun t => (BoundedContinuousFunction.norm_le hC).2 (hb t)

end EulerMeanCoefficients.SmoothCoefficientPath

namespace EulerTransversePacketProvider.Data

open Set EulerSmoothLimit EulerMeanCoefficients EulerTransverseBoundedFrame
open scoped BoundedContinuousFunction

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem frame_norm_le (C : ℝ) (hC : 0 ≤ C) (hF : ∀ t x, ‖D.F.field t x‖ ≤ C) :
    ‖D.frame.field‖ ≤ C := by
  apply SmoothCoefficientPath.field_norm_le_of_bound _ C hC
  intro t x
  have h := coefficient_derivative_bound D.m₀ D.R D.F 0 C
    (fun t x => by simpa only [norm_iteratedFDeriv_zero] using hF t x) t x
  simpa only [norm_iteratedFDeriv_zero] using h

theorem frameDerivative_norm_le (C1 : ℝ) (hC1 : 0 ≤ C1) (hF1 : ∀ t x, ‖D.F₁.field t x‖ ≤ C1) :
    ‖D.frameDerivative.field‖ ≤ C1 := by
  apply SmoothCoefficientPath.field_norm_le_of_bound _ C1 hC1
  intro t x
  have h := coefficient_derivative_bound D.m₀ D.R D.F₁ 0 C1
    (fun t x => by simpa only [norm_iteratedFDeriv_zero] using hF1 t x) t x
  simpa only [norm_iteratedFDeriv_zero] using h

end EulerTransversePacketProvider.Data

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerPacketParentLabelBounds EulerGevrey EulerPacketCofactor EulerPacketPiola
  EulerPacketActivationHistory EulerTransverseHistoryBounds EulerParentHistoryCost
  EulerPacketParentMeanCoercivity

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T) (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)

omit [CompleteSpace U] in
include hτ1 hTi in
theorem initialHistoryDifferenceScaleCost_bound :
    L.initialHistoryDifferenceScaleCost m hm R S hS H τ hτ hτT ≤ labelHistoryEnvelope L.K Ti := by
  let D := (G.transverseData m hm R S hS).initial τ hτ hτT.le
  let B := G.historyOn H m hm R S hS τ hτ hτT
  let C := frameAmplitude L.K
  let C1 := gradientAmplitude L.K
  let CH := 27*C^2*C1
  have hC : 0 ≤ C := frameAmplitude_nonneg L.K
  have hC1 : 0 ≤ C1 := gradientAmplitude_nonneg L.K
  have hCH : 0 ≤ CH := by dsimp [CH]; positivity
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ C := by
    intro t x
    have he : D.F.field t x=G.frame.field (initialInclusion G.T τ hτT.le t) x := rfl
    rw [he]
    have h := L.frame_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hF1 : ∀ t x, ‖D.F₁.field t x‖ ≤ C1 := by
    intro t x
    have he : D.F₁.field t x=G.first.field (initialInclusion G.T τ hτT.le t) x := rfl
    rw [he]
    have h := L.first_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hBH : ‖B.H.field‖ ≤ CH := by
    apply SmoothCoefficientPath.field_norm_le_of_bound _ CH hCH
    intro t x
    have he : B.H.field t x=G.curvature.field (initialInclusion G.T τ hτT.le t) x := rfl
    rw [he]
    have h := L.curvature_scaled_bound 0 (initialInclusion G.T τ hτT.le t) x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1 :=
    fun t x => G.frame_det (initialInclusion G.T τ hτT.le t) x
  have hci : D.frameLower⁻¹ ≤ gramInverseEnvelope C := by
    simpa only [gramInverseEnvelope,add_comm] using D.frameLower_inv_le_of_frame C hC hdet hF
  exact historyDifferenceCost_le_parentEnvelope τ D.frameLower ‖D.frame.field‖
    ‖D.frameDerivative.field‖
    ‖B.H.field‖ Ti C C1 CH (coefficientRadius L.K) hτ hτ1 hTi D.frameLower_pos hci
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC hC1 hCH (coefficientRadius_nonneg L.K)
    (D.frame_norm_le C hC hF) (D.frameDerivative_norm_le C1 hC1 hF1) hBH

omit [CompleteSpace U] in
include hτ1 hTi in
theorem initial_history_polynomial :
    historyLabelDifferenceCost (G.historyOn H m hm R S hS τ hτ hτT) ≤
      (labelHistoryConstant*(1+L.K+Ti)^labelHistoryPower)*G.ell := by
  have hTi0 : 0 ≤ Ti := (inv_pos.mpr hτ).le.trans hTi
  exact (L.initial_history_derivative_scale m hm R S hS H τ hτ hτT).trans
    (mul_le_mul_of_nonneg_right
      ((L.initialHistoryDifferenceScaleCost_bound m hm R S hS H τ hτ hτT Ti hτ1 hTi).trans
        (labelHistoryEnvelope_power L.K Ti (zero_le_one.trans L.K_one) hTi0)) G.ell_pos.le)

end EulerParentPacketFrames.LabelData
