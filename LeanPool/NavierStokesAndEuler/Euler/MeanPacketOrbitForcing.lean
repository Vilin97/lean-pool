/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSmoothL2Field
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketNonlinearForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider

@[expose] public section

/-!
# Solved mean fields are actual admissible forcing fields

The genuine continuous L² solution path and its solved spatial translation
orbit produce the literal smooth L² slices required by the forcing interface.
The same construction applies to its actual time derivative and pressure force.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
  EulerMeanPathTimeDerivative EulerMeanScalarPressure EulerPacketPointJets
    EulerPacketProfileRecursion
open scoped ContDiff

namespace Forcing

variable {D : Data} {raw : VectorField}

/-- Actual path-orbit regularity is converted into literal spatial derivative data. -/
def ofOrbitPath (p : C(Icc (0 : ℝ) D.T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a p))
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ,
      raw (t,(x,θ)) = representative (p t) (pathTranslation_evaluation_contDiff D.T p hp t) x) :
    Forcing D raw where
  slices t := smoothL2Field (p (D.clamp t)) (pathTranslation_evaluation_contDiff D.T p hp (D.clamp
    t))
  jets_continuous n := by
    simpa only [Data.clamp_coe] using smoothL2Field_path_jet_continuous D.T p hp n
  path := p
  path_eq t := by
    rw [Data.clamp_coe, smoothL2Field_toLp]
  raw_eq t x θ := by
    simpa only [Data.clamp_coe, smoothL2Field_field] using heq t x θ

/-- The output velocity of the genuine source mean solve can be used as the next forcing input. -/
def vectorForcing (G : Forcing D raw) : Forcing D G.vector :=
  ofOrbitPath G.velocityPath G.velocityPath_orbit (fun t x θ => by
    simp only [vector, pathRepresentative, Data.clamp_coe])

/-- Its true continuous time derivative has the same literal spatial admissibility. -/
def vectorDerivativeForcing (G : Forcing D raw) : Forcing D G.vectorDerivative :=
  ofOrbitPath G.derivativePath G.derivativePath_orbit (fun t x θ => by
    simp only [vectorDerivative, pathRepresentative, Data.clamp_coe])

def pressureForce (G : Forcing D raw) : VectorField := fun z =>
  pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit (D.clamp z.1) z.2.1

/-- The physical pressure gradient, rather than the unneeded scalar pressure value, is spatially L². -/
def pressureForceForcing (G : Forcing D raw) : Forcing D G.pressureForce :=
  ofOrbitPath G.pressureForcePath G.pressureForcePath_orbit (fun t x θ => by
    simp only [pressureForce, pathRepresentative, Data.clamp_coe])

end Forcing

theorem meanSolve_admissible (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw)) :
    Nonempty (Forcing D (meanSolve D raw).1) := by
  rw [meanSolve_of_admissible D raw h]
  exact ⟨(Classical.choice h).vectorForcing⟩

end EulerMeanPacketProvider
