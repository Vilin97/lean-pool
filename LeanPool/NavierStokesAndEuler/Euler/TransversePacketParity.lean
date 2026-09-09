/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorParity

/-! Joint odd parity of the actual transverse velocity, its time derivative, and its corrector. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderFieldReflection EulerTransverseBoundedFrame

namespace Data

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem frame_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.frame.field t (-x) = D.frame.field t x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [frame,coefficient_apply,hF]

theorem frameDerivative_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.frameDerivative.field t (-x) = D.frameDerivative.field t
        x := by
  rw [D.frame_strain,D.frame_strain,hM,D.frame_even hF]

theorem inverse_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.FInv.field t (-x) = D.FInv.field t x := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    D.FInv.field t (-x) v = D.FInv.field t (-x) (D.F.field t x (D.FInv.field t x v)) := by
      rw [D.inverse_right]
    _ = D.FInv.field t (-x) (D.F.field t (-x) (D.FInv.field t x v)) := by rw [hF]
    _ = D.FInv.field t x v := D.inverse_left t (-x) _

theorem normal_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.normal.field t (-x) = D.normal.field t x := by
  change (D.FInv.field t (-x)).adjoint D.m₀ = (D.FInv.field t x).adjoint D.m₀
  rw [D.inverse_even hF]

end Data

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

/-- Forcing field, bundling `path`, `orbit`, `raw_eq`. -/
def forcingField : Field P D.T raw where
  path := includePath P D.support D.support_measurable G.path
  orbit := G.path_orbit
  raw_eq := G.raw_eq

omit [CompleteSpace U] in
theorem path_reflection_neg
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
    (t : Icc (0 : ℝ) D.T) :
    reflection P (G.path t : CylinderL2 P Space) = -(G.path t : CylinderL2 P Space) :=
  G.forcingField.reflection_neg_of_raw_odd t (hraw t)

variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
  (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))

include hSym hF hM hraw hinit in
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (G.fullVelocityPath I t) = -G.fullVelocityPath I t :=
  EulerSourceCylinderParity.velocity_reflection_neg P D.support D.support_measurable hSym
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (D.frame_even hF) (D.frameDerivative_even hF hM) G.path I.value (G.path_reflection_neg hraw)
        hinit t

include hSym hF hM hraw hinit in
theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (G.fullDerivativePath I t) = -G.fullDerivativePath I t :=
  EulerSourceCylinderParity.velocityDerivative_reflection_neg P D.support D.support_measurable hSym
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (D.frame_even hF) (D.frameDerivative_even hF hM) G.path I.value (G.path_reflection_neg hraw)
        hinit t

include hSym hF hM hraw hinit in
theorem vector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vector I (t,(-x,-θ)) = -G.vector I (t,(x,θ)) :=
  (G.vectorField I).raw_odd_of_reflection_neg t
    (G.velocityPath_reflection_neg I hSym hF hM hraw hinit t) x θ

include hSym hF hM hraw hinit in
theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative I (t,(-x,-θ)) = -G.vectorDerivative I (t,(x,θ)) :=
  (G.vectorDerivativeField I).raw_odd_of_reflection_neg t
    (G.derivativePath_reflection_neg I hSym hF hM hraw hinit t) x θ

include hSym hF hM hraw hinit in
theorem corrector_odd_of_data (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.corrector I (t,(-x,-θ)) = -G.corrector I (t,(x,θ)) :=
  G.corrector_odd I t (D.inverse_even hF t) (G.vector_odd I hSym hF hM hraw hinit t) x θ

end Forcing
end EulerTransversePacketProvider
