/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureRegularity

/-! The actual normalized transverse pressure supplies the literal next-grade pressure gradient. -/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderScalarPrimitive
  EulerPacketProfileRecursion EulerPacketCylinderField

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem scalar_eq_pointField (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.scalar I (t,(x,θ)) =
      scalarPointField P (G.pressurePath I) (G.pressurePath_orbit I) t (x,(θ : AddCircle P)) := by
  simpa only [scalar,Data.clamp_coe] using congrFun
    (EulerSourceCylinderClassical.pressureField_eq_pointField P D.support D.support_measurable
      D.support_compact D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos
      D.frame_lower G.path I.value G.path_orbit I.orbit D.M D.normal D.normalLower
      D.normalLower_pos D.normal_lower G.mean_zero I.mean_zero t) (x,(θ : AddCircle P))

/-- The next known-force pressure term comes from the constructed scalar pressure itself. -/
def scalarGradientField : Field P D.T (pressureGradient (G.scalar I)) :=
  EulerPacketCylinderField.scalarGradientField (G.scalar I) (G.pressurePath I)
    (G.pressurePath_orbit I) (G.scalar_eq_pointField I)

end Forcing

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField)
  (h : Nonempty (Forcing P D raw))

/-- The total high operator has the required pressure-gradient witness on admissible forcing. -/
def highSolvePressureGradientField : Field P D.T (pressureGradient (highSolve P D I raw).2) :=
  ((Classical.choice h).scalarGradientField I).congr (fun _ _ _ => by
    rw [highSolve_of_admissible D I raw h])

end EulerTransversePacketProvider
