/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Poincaré's nonintegrability theorem for the planar restricted three-body problem

Source: arxiv:2111.11031, doi:10.1063/5.0266087, url:https://arxiv.org/abs/2111.11031
Proposed by: Gershon Bialer
Open declarations: `Challenge.PoincareThreeBody.nonintegrability`
Tags: dynamical-systems, celestial-mechanics, hamiltonian-systems, nonintegrability
MSC: 70F07, 37J30, 37J40
Estimated size: ~17000 lines of Lean

Informal statement:
* `Challenge.PoincareThreeBody.nonintegrability` — There is no positive interval about zero on which
  the planar circular restricted three-body Hamiltonian admits a first integral that is jointly
  real-analytic in the mass parameter and all collision-free phase variables and whose phase
  differential is independent of the Hamiltonian differential at some point of that domain.
-/

/-
Source correspondence: Yagasaki states the classical planar result as Theorem 1.1 on page 2 of
arXiv:2111.11031v2. Theorem 3.1 on page 8 gives the paper's precise local meromorphic obstruction
near resonant unperturbed elliptic orbits. The Lean statement is the fixed-coordinate, global
uniform-domain special case: a jointly real-analytic family on `parameterDomain δ` restricts and
complexifies on each of those local neighborhoods. Since that real domain is connected, a minor
witnessing functional independence at one point cannot vanish on a nonempty open neighborhood, so
the local obstruction rules out the global family asserted here.
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

/-- The collision-free joint mass-parameter/phase-space domain. Both primaries are excluded even
at a parameter value where one of their masses vanishes, making this a uniform domain in `μ`. -/
def collisionFree : Set (ℝ × PhaseSpace) :=
  {z | firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧ secondPrimaryDistanceSq z.1 z.2 ≠ 0}

/-- The collision-free domain with the mass parameter restricted to `|μ| < δ`. -/
def parameterDomain (δ : ℝ) : Set (ℝ × PhaseSpace) :=
  {z | |z.1| < δ ∧ z ∈ collisionFree}

/-- The Newtonian potential of the planar circular restricted three-body problem in the rotating
frame, with the primary convention used in Yagasaki's paper. -/
noncomputable def potential (μ : ℝ) (s : PhaseSpace) : ℝ :=
  μ / Real.sqrt (firstPrimaryDistanceSq μ s) +
    (1 - μ) / Real.sqrt (secondPrimaryDistanceSq μ s)

/-- The planar circular restricted three-body Hamiltonian in rotating canonical coordinates,
using `ω = dx ∧ dpₓ + dy ∧ dpᵧ`. -/
noncomputable def hamiltonian (μ : ℝ) (s : PhaseSpace) : ℝ :=
  ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 - potential μ s

/-- The coordinate basis vector in the concrete phase space. -/
def coordinateVector (i : Fin 4) : PhaseSpace :=
  fun j ↦ if j = i then 1 else 0

/-- The canonical Poisson bracket in coordinates `(x, y, pₓ, pᵧ)`. Analyticity hypotheses in
the challenge ensure that the total Fréchet derivatives are the actual derivatives on the domain. -/
noncomputable def poissonBracket (F G : PhaseSpace → ℝ) (s : PhaseSpace) : ℝ :=
  let dF := fderiv ℝ F s
  let dG := fderiv ℝ G s
  dF (coordinateVector 0) * dG (coordinateVector 2) -
      dF (coordinateVector 2) * dG (coordinateVector 0) +
    (dF (coordinateVector 1) * dG (coordinateVector 3) -
      dF (coordinateVector 3) * dG (coordinateVector 1))

/-- A family is jointly real-analytic in the mass parameter and phase variables throughout the
uniform collision-free domain. -/
def IsJointlyAnalytic (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  AnalyticOnNhd ℝ (Function.uncurry F) (parameterDomain δ)

/-- `F` is a first-integral family when it Poisson-commutes with the CR3BP Hamiltonian at every
point of the uniform parameter domain. -/
noncomputable def IsFirstIntegralFamily (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∀ z ∈ parameterDomain δ, poissonBracket (F z.1) (hamiltonian z.1) z.2 = 0

/-- Functional independence means that at some point the phase differentials of the Hamiltonian
and the putative additional integral are linearly independent. For analytic functions, independence
at one point persists on a nonempty open neighborhood. -/
noncomputable def IsIndependentSomewhere (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∃ z ∈ parameterDomain δ,
    LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian z.1) z.2, fderiv ℝ (F z.1) z.2]

/-- **Poincaré's classical nonintegrability theorem, planar global form.** There is no jointly
real-analytic family of additional first integrals for the planar circular restricted three-body
problem near the integrable mass value `μ = 0`.

This is deliberately a parameter-dependent statement. It makes no claim about a first integral
defined only for one fixed positive mass ratio. -/
theorem nonintegrability :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧ IsIndependentSomewhere δ F := sorry

end Challenge.PoincareThreeBody
