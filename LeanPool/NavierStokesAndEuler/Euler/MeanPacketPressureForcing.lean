/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketOrbitForcing

@[expose] public section

/-! The actual scalar pressure gradient is an admissible smooth L² field. -/

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set EulerSmoothLimit EulerMeanCoefficients EulerMeanScalarPressure
  EulerPacketPointJets EulerPacketProfileRecursion

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

def scalarGradient : VectorField := fun z =>
  gradient (fun x => G.scalar (z.1,(x,z.2.2))) z.2.1

theorem scalarGradient_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.scalarGradient (t,(x,θ)) = (D.F.field t x).adjoint (G.pressureForce (t,(x,θ))) := by
  have h := (pressureScalar_spec D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit t).2.2 x
  simpa only [scalarGradient, scalar, pressureForce, Data.clamp_coe] using h

/-- All actual pressure-gradient jets are square-integrable and continuous in time. -/
def scalarGradientForcing : Forcing D G.scalarGradient := by
  let A := SmoothCoefficientPath.map (EulerTransverseGramInverse.realAdjoint (U := Space) (E :=
    Space)) D.F
  have hAdj (M : Space →L[ℝ] Space) :
      EulerTransverseGramInverse.realAdjoint M = M.adjoint := rfl
  apply (G.pressureForceForcing.multiply A).congr
  intro t x θ
  simpa only [A, SmoothCoefficientPath.map_apply, Data.clamp_coe,
    hAdj] using G.scalarGradient_eq t x θ

theorem physicalGradient_eq (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    (D.inverseFrame (t,(x,θ))).adjoint (G.scalarGradient (t,(x,θ))) =
      G.pressureForce (t,(x,θ)) := by
  have h := pressureScalar_physicalGradient D.T D.T_pos.le D.F D.F₁ D.opInv G.solution
    D.frameLower D.frameLower_pos D.frame_lower G.path G.pressureForcePath_orbit
    D.FInv D.inverse_right t x
  simpa only [Data.inverseFrame, scalarGradient, scalar, pressureForce, Data.clamp_coe] using h

end EulerMeanPacketProvider.Forcing
