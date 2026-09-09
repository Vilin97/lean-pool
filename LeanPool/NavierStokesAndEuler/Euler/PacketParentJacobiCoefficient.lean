/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds

/-! The Hessian multiplier bound follows from the actual second time
derivative of the deformation and the Jacobi equation.  Uniqueness of
within-interval derivatives includes both endpoints of the interval. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketPiola EulerPacketCofactor EulerVolterraConvolution EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} (B : HistoryData D)
  (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) D.T) EndSpace)
  (h₂ : ∀ t ∈ Icc (0 : ℝ) D.T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.F₁.field s x)
      (extendPath D.T D.T_pos.le F₂.field t x) (Icc (0 : ℝ) D.T) t)

include h₂

theorem second_eq_jacobi (t : Icc (0 : ℝ) D.T) (x v : Space) :
    F₂.field t x v = -(B.H.field t x (D.F.field t x v)) := by
  have hu := uniqueDiffOn_Icc D.T_pos (t : ℝ) t.property
  have he := ((h₂ t t.property x).derivWithin hu).symm.trans
    ((B.jacobi t t.property x).derivWithin hu)
  have hval := congrArg (fun A : EndSpace => A v) he
  simpa only [extendPath,projIcc_of_mem D.T_pos.le t.property,
    neg_apply,ContinuousLinearMap.comp_apply] using hval

theorem curvature_bound_of_second (R C C₂ : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₂ : ∀ n t x, ‖iteratedFDeriv ℝ n (F₂.field t : Space → EndSpace) x‖ ≤ C₂ * majorant R 0 n)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (B.H.field t : Space → EndSpace) x‖ ≤
      (27*C^2*C₂)*majorant R 0 n :=
  coefficientCurvature_bound D.F F₂ B.H hdet (B.second_eq_jacobi F₂ h₂)
    R C C₂ hR hC hC₂ hF hF₂ n t x

end EulerTransversePacketProvider.HistoryData
