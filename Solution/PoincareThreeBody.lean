/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.LocalEnergyLeaf

/-!
# Solution: Poincaré's nonintegrability theorem for the planar restricted three-body problem

Challenge: `poincare-planar-restricted-three-body` (`Challenge.PoincareThreeBody`)
Proves: `Challenge.PoincareThreeBody.nonintegrability`
Solved by: Gershon Bialer
Pool project: `poincare-three-body-nonintegrability`

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/

namespace Challenge.PoincareThreeBody

open Set

/-- Planar canonical phase space, ordered as `(x, y, pₓ, pᵧ)`. -/
abbrev PhaseSpace := Fin 4 → ℝ

/-- Squared distance from the primary of mass `μ` at `(1 - μ, 0)`. -/
def firstPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2

/-- Squared distance from the primary of mass `1 - μ` at `(-μ, 0)`. -/
def secondPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 + μ) ^ 2 + (s 1) ^ 2

/-- The collision-free joint mass-parameter/phase-space domain. -/
def collisionFree : Set (ℝ × PhaseSpace) :=
  {z | firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧ secondPrimaryDistanceSq z.1 z.2 ≠ 0}

/-- The collision-free domain with the mass parameter restricted to `|μ| < δ`. -/
def parameterDomain (δ : ℝ) : Set (ℝ × PhaseSpace) :=
  {z | |z.1| < δ ∧ z ∈ collisionFree}

/-- The Newtonian potential in the rotating frame. -/
noncomputable def potential (μ : ℝ) (s : PhaseSpace) : ℝ :=
  μ / Real.sqrt (firstPrimaryDistanceSq μ s) +
    (1 - μ) / Real.sqrt (secondPrimaryDistanceSq μ s)

/-- The planar circular restricted three-body Hamiltonian in rotating canonical coordinates. -/
noncomputable def hamiltonian (μ : ℝ) (s : PhaseSpace) : ℝ :=
  ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 - potential μ s

/-- The coordinate basis vector in the concrete phase space. -/
def coordinateVector (i : Fin 4) : PhaseSpace :=
  fun j ↦ if j = i then 1 else 0

/-- The canonical Poisson bracket in coordinates `(x, y, pₓ, pᵧ)`. -/
noncomputable def poissonBracket (F G : PhaseSpace → ℝ) (s : PhaseSpace) : ℝ :=
  let dF := fderiv ℝ F s
  let dG := fderiv ℝ G s
  dF (coordinateVector 0) * dG (coordinateVector 2) -
      dF (coordinateVector 2) * dG (coordinateVector 0) +
    (dF (coordinateVector 1) * dG (coordinateVector 3) -
      dF (coordinateVector 3) * dG (coordinateVector 1))

attribute [local instance 10000] NormedField.toNormedSpace

/-- Joint real analyticity in the mass parameter and phase variables. -/
def IsJointlyAnalytic (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  AnalyticOnNhd ℝ (Function.uncurry F) (parameterDomain δ)

/-- A first-integral family Poisson-commutes with the Hamiltonian throughout the domain. -/
noncomputable def IsFirstIntegralFamily (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∀ z ∈ parameterDomain δ, poissonBracket (F z.1) (hamiltonian z.1) z.2 = 0

/-- Functional independence of the phase differentials at some point. -/
noncomputable def IsIndependentSomewhere (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∃ z ∈ parameterDomain δ,
    LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian z.1) z.2, fderiv ℝ (F z.1) z.2]

/-- Poincaré's classical parameter-dependent nonintegrability theorem for the planar circular
restricted three-body problem. -/
theorem nonintegrability :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧ IsIndependentSomewhere δ F :=
  LeanPool.PoincareThreeBody.nonintegrability_of_collisionBand

end Challenge.PoincareThreeBody
