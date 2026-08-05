/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The planar circular restricted three-body Hamiltonian

This file gives the exact definitions occurring in the Poincaré nonintegrability challenge and
establishes their elementary structural properties. It deliberately does not import the challenge
module: the solution and challenge environments must remain separately exportable for comparator.
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

lemma firstPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ firstPrimaryDistanceSq μ s := by
  simp only [firstPrimaryDistanceSq]
  positivity

lemma secondPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ secondPrimaryDistanceSq μ s := by
  simp only [secondPrimaryDistanceSq]
  positivity

lemma firstPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : firstPrimaryDistanceSq μ s ≠ 0) : 0 < firstPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (firstPrimaryDistanceSq_nonneg μ s) (Ne.symm h)

lemma secondPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : secondPrimaryDistanceSq μ s ≠ 0) : 0 < secondPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (secondPrimaryDistanceSq_nonneg μ s) (Ne.symm h)

lemma mem_collisionFree_iff {μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ collisionFree ↔
      firstPrimaryDistanceSq μ s ≠ 0 ∧ secondPrimaryDistanceSq μ s ≠ 0 :=
  Iff.rfl

lemma mem_parameterDomain_iff {δ μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ parameterDomain δ ↔ |μ| < δ ∧ (μ, s) ∈ collisionFree :=
  Iff.rfl

@[simp] lemma coordinateVector_same (i : Fin 4) : coordinateVector i i = 1 := by
  simp [coordinateVector]

@[simp] lemma coordinateVector_apply {i j : Fin 4} (h : j ≠ i) : coordinateVector i j = 0 := by
  simp [coordinateVector, h]

lemma poissonBracket_self (F : PhaseSpace → ℝ) (s : PhaseSpace) :
    poissonBracket F F s = 0 := by
  simp only [poissonBracket]
  ring

lemma hamiltonian_isFirstIntegralFamily (δ : ℝ) :
    IsFirstIntegralFamily δ hamiltonian := by
  intro z hz
  exact poissonBracket_self (hamiltonian z.1) z.2

lemma hamiltonian_zero (s : PhaseSpace) :
    hamiltonian 0 s =
      ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 -
        1 / Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2) := by
  simp [hamiltonian, potential, firstPrimaryDistanceSq, secondPrimaryDistanceSq]

lemma IsFirstIntegralFamily.poissonBracket_zero_at_mass_zero {δ : ℝ}
    {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ) (hF : IsFirstIntegralFamily δ F)
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    poissonBracket (F 0) (hamiltonian 0) s = 0 := by
  apply hF (0, s)
  exact ⟨by simpa using hδ, hs⟩

lemma hamiltonian_not_independent (δ : ℝ) : ¬IsIndependentSomewhere δ hamiltonian := by
  rintro ⟨z, hz, hlinear⟩
  have hindex : (0 : Fin 2) = 1 := hlinear.injective (by simp)
  norm_num at hindex

end Challenge.PoincareThreeBody
