/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import LeanPool.NavierStokesAndEuler.NavierStokes.SolutionDifference

/-!
# Common definitions for whole-space comparison

These are the ordinary volume energies and differential expressions. No
comparison estimate or pressure representation is assumed in this module.
-/

@[expose] public section



noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators ENNReal InnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- Slab: an abbreviation for `Icc a b ×ˢ univ`. -/
abbrev slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

/-- Partial D: an abbreviation for `NavierStokes.SolutionDifference.spatialPartial i f x`. -/
abbrev partialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  NavierStokes.SolutionDifference.spatialPartial i f x

/-- Comparison Lᵖ norm, given by `(eLpNorm f p (volume : Measure Space)).toReal`. -/
def comparisonLpNorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (f : Space → E) : ℝ :=
  (eLpNorm f p (volume : Measure Space)).toReal

/-- L2 sq, given by `∫ x : Space, ‖f x‖ ^ 2`. -/
def l2Sq {E : Type*} [NormedAddCommGroup E] (f : Space → E) : ℝ :=
  ∫ x : Space, ‖f x‖ ^ 2

/-- Gradient sq, given by `∑ i : Fin 3, ‖partialD i f x‖ ^ 2`. -/
def gradientSq (f : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖partialD i f x‖ ^ 2

/-- Weighted energy, given by `∫ x : Space, χ x * ‖w (t, x)‖ ^ 2`. -/
def weightedEnergy (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * ‖w (t, x)‖ ^ 2

/-- Weighted energy rate, given by `∫ x : Space, χ x * (2 * ⟪w (t, x),
NavierStokes.ProblemStatement.temporalDerivative w t x⟫_ℝ)`. -/
def weightedEnergyRate (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * (2 * ⟪w (t, x),
    NavierStokes.ProblemStatement.temporalDerivative w t x⟫_ℝ)

/-- Weighted dissipation, given by `∫ x : Space, χ x * gradientSq (fun y => w (t, y)) x`. -/
def weightedDissipation (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, χ x * gradientSq (fun y => w (t, y)) x

/-- Dissipation root, given by `Real.sqrt (weightedDissipation (fun x => φ x ^ 8) w t)`. -/
def dissipationRoot (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (weightedDissipation (fun x => φ x ^ 8) w t)

/-- Cutoff L6, given by `comparisonLpNorm 6 (fun x => (φ x ^ 4) • w (t, x))`. -/
def cutoffL6 (φ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  comparisonLpNorm 6 (fun x => (φ x ^ 4) • w (t, x))

/-- Tensor diff, given by `u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j`. -/
def tensorDiff (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j

end NavierStokesR3.Comparison
