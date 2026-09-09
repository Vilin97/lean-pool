/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryUncut
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointUniqueness

@[expose] public section

/-! The stationary path selected by the actual activation argument is the
same history used by the packet, after matching its physical terminal trace. -/

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTimeLp EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
  EulerTransverseEndpointUniqueness EulerTransverseEndpointParameter
    EulerTransverseEndpointCoordinates
  EulerTransverseInitialCoordinates EulerTransverseFrameCoordinates
    EulerTransverseSourceCoefficientPath
  EulerTransverseActivationSelection EulerTransverseActivationTrial

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {D : Data U} (B : HistoryData D) (x : Space)

def stationaryDerivative (L : V →L[ℝ] TimeLp D.T Space) : V →L[ℝ] TimeLp D.T Space :=
  endpointDerivative D.T D.T_pos.le (fun t => D.normal.field t x)
    (B.coefficients.labelHessian x) B.potential B.potential_nonneg
    (B.coefficients.labelHessian_upper x) B.small L

def stationaryCorrectedVelocity (L : V →L[ℝ] TimeLp D.T Space) (Y : V)
    (t : Icc (0 : ℝ) D.T) : Space :=
  physicalVelocityPath D.T D.T_pos.le (B.coefficients.labelFrame x)
    (B.coefficients.labelFrameDerivative x) B.coefficients.lower B.coefficients.lower_pos
    (B.coefficients.labelFrame_lower x) (B.coefficients.labelHessian x)
    (stationaryDerivative B x L Y) t -
      D.M.field t x (initialRealPrimitive D.T (stationaryDerivative B x L Y) t)

theorem history_eq_stationary_of_terminal (L : V →L[ℝ] TimeLp D.T Space)
    (hL : ∀ Y t, ⟪D.normal.field t x,initialPrimitive D.T D.T_pos.le (L Y) t⟫_ℝ=0)
    (Y : V) (ξ : U)
    (hterminal : initialRealPrimitive D.T (L Y) D.T =
      D.frame.field ⟨D.T,D.T_pos.le,le_rfl⟩ x ξ)
    (t : Icc (0 : ℝ) D.T) :
    B.coefficients.labelVelocity x ξ t = stationaryCorrectedVelocity B x L Y t := by
  let C := B.coefficients
  let m : Icc (0 : ℝ) D.T → Space := fun s => D.normal.field s x
  let A := affineTrial D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
  let u := stationaryDerivative B x L Y
  have hm : ∀ s η, ⟪m s,C.labelFrame x s η⟫_ℝ=0 := fun s η => D.frame_tangent s x η
  have hRange : ∀ s η, ⟪m s,η⟫_ℝ=0 → ∃ z : U, C.labelFrame x s z=η :=
    fun s η h => D.frame_range s x η h
  have hA : ∀ Z s, ⟪m s,initialPrimitive D.T D.T_pos.le (A Z) s⟫_ℝ=0 :=
    affineTrial_tangent D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
      (C.labelFrame_derivative x) m hm
  have hu : u=endpointDerivative D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small A ξ := by
    apply endpointDerivative_unique D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small A ξ (hA ξ) u
    · exact endpointDisplacement_tangent D.T D.T_pos.le m (C.labelHessian x)
        B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L hL Y
    · calc
        _ = initialRealPrimitive D.T (L Y) D.T :=
          endpointDisplacement_terminal D.T D.T_pos.le m (C.labelHessian x)
            B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L Y
        _ = D.frame.field ⟨D.T,D.T_pos.le,le_rfl⟩ x ξ := hterminal
        _ = _ := (affineTrial_terminal D.T D.T_pos.le (C.labelFrame x)
          (C.labelFrameDerivative x) D.T_pos (C.labelFrame_derivative x) ξ).symm
    · exact endpointDerivative_weak D.T D.T_pos.le m (C.labelHessian x)
        B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L Y
  have hhistory := historyVelocity_eq D.T D.T_pos.le (C.labelFrame x)
    (C.labelFrameDerivative x) (C.labelHessian x) C.lower C.lower_pos
    (C.labelFrame_lower x) (C.labelFrame_derivative x) C.potential C.potential_nonneg
    (C.labelHessian_upper x) C.small m hm hRange (C.labelFrameSecond x) D.T_pos
    (C.labelFrame_second_derivative x) (C.labelFrame_equation x) ξ t
  change C.labelVelocity x ξ t = C.labelFrame x t
    (coordinateVelocityPath D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
      C.lower C.lower_pos (C.labelFrame_lower x) (C.labelHessian x)
      (endpointDerivative D.T D.T_pos.le m (C.labelHessian x) B.potential B.potential_nonneg
        (C.labelHessian_upper x) B.small A ξ) t) at hhistory
  rw [← hu] at hhistory
  have hurange : ∀ s : Icc (0 : ℝ) D.T, ∃ z : U,
      C.labelFrame x s z=initialRealPrimitive D.T u s := by
    intro s
    exact hRange s _ (endpointDisplacement_tangent D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L hL Y s)
  have hrec := initialCoordinates_reconstruct D.T D.T_pos.le (C.labelFrame x)
    C.lower C.lower_pos (C.labelFrame_lower x) u hurange t
  change D.frame.field t x
    (initialCoordinates D.T D.T_pos.le (C.labelFrame x) C.lower C.lower_pos
      (C.labelFrame_lower x) u t) = initialRealPrimitive D.T u t at hrec
  change C.labelVelocity x ξ t = physicalVelocityPath D.T D.T_pos.le (C.labelFrame x)
    (C.labelFrameDerivative x) C.lower C.lower_pos (C.labelFrame_lower x) (C.labelHessian x) u t -
      D.M.field t x (initialRealPrimitive D.T u t)
  rw [hhistory]
  simp only [physicalVelocityPath,extendPath,projIcc_of_mem D.T_pos.le t.property]
  change D.frame.field t x _ = D.frameDerivative.field t x _+D.frame.field t x _-D.M.field t x _
  rw [D.frame_strain,comp_apply,hrec]
  abel

end EulerPacketActivationHistory
