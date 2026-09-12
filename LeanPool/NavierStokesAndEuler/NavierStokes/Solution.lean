/-
Copyright (c) 2026 OpenAI and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Classical Navier–Stokes solutions with prescribed initial data

The periodic and finite-energy comparison arguments share the same local equation.
`SolutionOn` records this common contract independently of periodicity and energy
bounds. Viscosity, initial time, initial velocity, and the time set are parameters.
Smoothness is relative to the time set; the equation is imposed only after the
initial time, so no derivative of an arbitrary extension across that boundary is used.

This interface adapts the shared solution vocabulary of
https://github.com/Code4me2/NavierStokesAndEuler/tree/26e896edbdbe1215c0d50ddba24b2b6453646f5f.
-/

public section

noncomputable section

namespace NavierStokes

open Set ProblemStatement
open scoped ContDiff

/-- The Navier–Stokes equation's left-hand side at an arbitrary viscosity. -/
@[expose] def viscousResidual (viscosity : ℝ) (velocity : VelocityField)
    (pressure : PressureField) (time : ℝ) (position : Space) : Space :=
  temporalDerivative velocity time position + advection velocity time position -
    viscosity • spatialLaplacian velocity time position + pressureGradient pressure time position

@[simp] theorem viscousResidual_one (velocity : VelocityField) (pressure : PressureField)
    (time : ℝ) (position : Space) :
    viscousResidual 1 velocity pressure time position =
      navierStokesResidual velocity pressure time position := by
  simp only [viscousResidual, one_smul, navierStokesResidual]

@[simp] theorem viscousResidual_zero_fields (viscosity time : ℝ) (position : Space) :
    viscousResidual viscosity (fun _ => 0) (fun _ => 0) time position = 0 := by
  simp [viscousResidual, temporalDerivative, advection, spatialLaplacian,
    spatialDerivative, pressureGradient]

/-- A smooth incompressible solution with specified initial value. The initial
value is required at `initialTime` even if the chosen time set omits that point.
No positivity assumption on viscosity is needed for the definition or restriction API. -/
structure SolutionOn (viscosity initialTime : ℝ) (initialVelocity : Space → Space)
    (times : Set ℝ) (force velocity : VelocityField) (pressure : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ velocity (times ×ˢ univ)
  pressure_smooth : ContDiffOn ℝ ∞ pressure (times ×ˢ univ)
  initial_velocity : ∀ position : Space, velocity (initialTime, position) = initialVelocity position
  divergence_free : ∀ time ∈ times, ∀ position : Space, spatialDivergence velocity time position = 0
  navier_stokes : ∀ time ∈ times, initialTime < time → ∀ position : Space,
    viscousResidual viscosity velocity pressure time position = force (time, position)

namespace SolutionOn

variable {viscosity initialTime : ℝ} {initialVelocity : Space → Space}
  {times smallerTimes : Set ℝ} {force velocity : VelocityField} {pressure : PressureField}

/-- Restrict a solution's regularity and equation to a smaller time set. -/
theorem mono
    (solution : SolutionOn viscosity initialTime initialVelocity times force velocity pressure)
    (subset : smallerTimes ⊆ times) :
    SolutionOn viscosity initialTime initialVelocity smallerTimes force velocity pressure where
  velocity_smooth := solution.velocity_smooth.mono (prod_mono subset subset_rfl)
  pressure_smooth := solution.pressure_smooth.mono (prod_mono subset subset_rfl)
  initial_velocity := solution.initial_velocity
  divergence_free := fun time member => solution.divergence_free time (subset member)
  navier_stokes := fun time member => solution.navier_stokes time (subset member)

/-- The identically zero fields solve the equation with zero force and initial velocity. -/
theorem zero (viscosity initialTime : ℝ) (times : Set ℝ) :
    SolutionOn viscosity initialTime (fun _ => 0) times
      (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial_velocity := fun _ => rfl
  divergence_free := by simp [spatialDivergence, spatialDerivative]
  navier_stokes := by simp

end SolutionOn

/-- The periodic blow-up candidate satisfies the shared local solution contract. -/
theorem ProblemStatement.CandidateProperties.toSolutionOn
    {velocity force : VelocityField} {pressure : PressureField}
    (candidate : CandidateProperties velocity pressure force) :
    SolutionOn 1 0 (fun _ => 0) (Ico 0 1) force velocity pressure where
  velocity_smooth := candidate.velocity_smooth
  pressure_smooth := candidate.pressure_smooth
  initial_velocity := candidate.zero_initial_velocity
  divergence_free := candidate.divergence_free
  navier_stokes := by
    intro time member positive position
    simpa only [viscousResidual_one] using
      candidate.navier_stokes time ⟨positive, member.2⟩ position

end NavierStokes
