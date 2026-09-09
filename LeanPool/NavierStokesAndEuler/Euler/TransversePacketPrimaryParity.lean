/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity

/-! Odd compact terminal data propagate through the genuine history and forward primary solve. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerTransversePacketProvider EulerTimeIntervalRestriction EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))

include hF hM hH hY

theorem forwardInitial_reflection_neg :
    reflection P ((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U) =
      -((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U) :=
  B.coefficients.endpointCoordinate_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun t x => hF (initialInclusion D.T τ hτT.le t) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun t x => hF (initialInclusion D.T τ hτT.le t) x)
      (fun t x => hM (initialInclusion D.T τ hτT.le t) x))
    hH Y.value hY ⟨τ,hτ.le,le_rfl⟩

theorem pastVelocity_reflection_neg (t : Icc (0 : ℝ) τ) :
    reflection P (pastVelocity τ hτ hτT B Y t) = -pastVelocity τ hτ hτT B Y t :=
  B.coefficients.endpointVelocity_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun s x => hF (initialInclusion D.T τ hτT.le s) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x))
    hH Y.value hY t

theorem pastDerivative_reflection_neg (t : Icc (0 : ℝ) τ) :
    reflection P (pastDerivative τ hτ hτT B Y t) = -pastDerivative τ hτ hτT B Y t :=
  B.coefficients.endpointDerivative_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun s x => hF (initialInclusion D.T τ hτT.le s) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x))
    hH Y.value hY t

include hSym

theorem futureVelocity_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection P (futureVelocity τ hτ hτT B Y t) = -futureVelocity τ hτ hτT B Y t :=
  (zeroForcing (D.tail τ hτ.le hτT)).velocityPath_reflection_neg (forwardInitial τ hτ hτT B Y) hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (by intro s x θ; simp only [Pi.zero_apply,neg_zero])
    (forwardInitial_reflection_neg τ hτ hτT B Y hF hM hH hY) t

theorem futureDerivative_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection P (futureDerivative τ hτ hτT B Y t) = -futureDerivative τ hτ hτT B Y t :=
  (zeroForcing (D.tail τ hτ.le hτT)).derivativePath_reflection_neg (forwardInitial τ hτ hτT B Y)
      hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (by intro s x θ; simp only [Pi.zero_apply,neg_zero])
    (forwardInitial_reflection_neg τ hτ hτT B Y hF hM hH hY) t

theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (velocityPath τ hτ hτT B Y t) = -velocityPath τ hτ hτT B Y t :=
  join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) {u | reflection P u = -u}
    (pastVelocity_reflection_neg τ hτ hτT B Y hF hM hH hY)
    (futureVelocity_reflection_neg τ hτ hτT B Y hSym hF hM hH hY) t

theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (derivativePath τ hτ hτT B Y t) = -derivativePath τ hτ hτT B Y t :=
  join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) {u | reflection P u = -u}
    (pastDerivative_reflection_neg τ hτ hτT B Y hF hM hH hY)
    (futureDerivative_reflection_neg τ hτ hτT B Y hSym hF hM hH hY) t

end EulerTransversePacketPrimary
