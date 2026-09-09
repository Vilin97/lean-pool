/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Common definitions for whole-space comparison

These are the ordinary volume energies and differential expressions. No
comparison estimate or pressure representation is assumed in this module.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators ENNReal InnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

abbrev slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

abbrev partialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  NavierStokes.PeriodicIntegration.spatialPartial i f x

def comparisonLpNorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (f : Space → E) : ℝ :=
  (eLpNorm f p (volume : Measure Space)).toReal

def l2Sq {E : Type*} [NormedAddCommGroup E] (f : Space → E) : ℝ :=
  ∫ x : Space, ‖f x‖ ^ 2

def gradientSq (f : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖partialD i f x‖ ^ 2

def weightedEnergy (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * ‖w (t, x)‖ ^ 2

def weightedEnergyRate (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * (2 * ⟪w (t, x),
    NavierStokes.ProblemStatement.temporalDerivative w t x⟫_ℝ)

def weightedDissipation (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * gradientSq (fun y => w (t, y)) x

def dissipationRoot (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (weightedDissipation (fun x => φ x ^ 8) w t)

def cutoffL6 (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  comparisonLpNorm 6 (fun x => (φ x ^ 4) • w (t, x))

def tensorDiff (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j

end NavierStokesR3.Comparison
