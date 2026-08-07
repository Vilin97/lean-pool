/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Separation.Hausdorff

/-!
# Resonant covectors in two degrees of freedom

This file develops the elementary linear-algebra step in Poincaré's nonintegrability argument. At
a resonant action, both the unperturbed frequency and the differential of the leading coefficient
of a putative first integral annihilate the same nonzero resonance vector. In two dimensions, the
two covectors must therefore be linearly dependent.
-/

namespace LeanPool.PoincareThreeBody

/-- The two-dimensional action or frequency space used in the planar problem. -/
abbrev ActionSpace := Fin 2 → ℝ

/-- The coordinate dot product on the two-dimensional action space. -/
def dot (u v : ActionSpace) : ℝ :=
  ∑ i, u i * v i

/-- The oriented area spanned by two vectors in the action space. -/
def wedge (u v : ActionSpace) : ℝ :=
  u 0 * v 1 - u 1 * v 0

lemma dot_eq (u v : ActionSpace) : dot u v = u 0 * v 0 + u 1 * v 1 := by
  simp [dot, Fin.sum_univ_two]

/-- Two covectors annihilating the same nonzero vector in dimension two have zero wedge. -/
theorem wedge_eq_zero_of_resonance {k u v : ActionSpace} (hk : k ≠ 0)
    (hu : dot k u = 0) (hv : dot k v = 0) : wedge u v = 0 := by
  rw [dot_eq] at hu hv
  by_cases hk0 : k 0 = 0
  · have hk1 : k 1 ≠ 0 := by
      intro hk1
      apply hk
      funext i
      fin_cases i <;> assumption
    have hu1 : u 1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hk1
      simpa [hk0] using hu
    have hv1 : v 1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hk1
      simpa [hk0] using hv
    simp [wedge, hu1, hv1]
  · have hmul : k 0 * wedge u v = 0 := by
      have hu' := congrArg (fun x : ℝ ↦ x * v 1) hu
      have hv' := congrArg (fun x : ℝ ↦ x * u 1) hv
      dsimp [wedge]
      nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left hk0

/-- Zero wedge is equivalent to failure of linear independence for two vectors in dimension two. -/
theorem not_linearIndependent_of_wedge_eq_zero {u v : ActionSpace} (h : wedge u v = 0) :
    ¬LinearIndependent ℝ ![u, v] := by
  intro huv
  let A : Matrix (Fin 2) (Fin 2) ℝ := ![u, v]
  have hunit : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp huv
  have hdetUnit : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunit
  apply hdetUnit.ne_zero
  rw [Matrix.det_fin_two]
  simpa [A, wedge] using h

/-- The resonant linear-algebra obstruction in the form used by the perturbative proof. -/
theorem not_linearIndependent_of_common_resonance {k frequency differential : ActionSpace}
    (hk : k ≠ 0) (hfrequency : dot k frequency = 0)
    (hdifferential : dot k differential = 0) :
    ¬LinearIndependent ℝ ![frequency, differential] :=
  not_linearIndependent_of_wedge_eq_zero
    (wedge_eq_zero_of_resonance hk hfrequency hdifferential)

/-- A nonzero perturbing Fourier mode turns the first homological equation into the second
orthogonality relation needed by the resonant obstruction. -/
theorem homologicalEquation_obstruction
    {k frequency differential : ActionSpace} {correction perturbation : ℝ}
    (hk : k ≠ 0) (hresonance : dot k frequency = 0) (hperturbation : perturbation ≠ 0)
    (hequation : dot k frequency * correction + dot k differential * perturbation = 0) :
    ¬LinearIndependent ℝ ![frequency, differential] := by
  have hdifferential : dot k differential = 0 := by
    rw [hresonance, zero_mul, zero_add] at hequation
    exact (mul_eq_zero.mp hequation).resolve_right hperturbation
  exact not_linearIndependent_of_common_resonance hk hresonance hdifferential

/-- A continuous wedge that vanishes on a dense family of resonant actions vanishes everywhere. -/
theorem wedge_eq_zero_of_dense_resonances {X : Type*} [TopologicalSpace X]
    {resonantActions : Set X} (hdense : Dense resonantActions)
    {frequency differential : X → ActionSpace} (hfrequency : Continuous frequency)
    (hdifferential : Continuous differential)
    (hresonant : ∀ x ∈ resonantActions, wedge (frequency x) (differential x) = 0) (x : X) :
    wedge (frequency x) (differential x) = 0 := by
  have hwedge : Continuous (fun y ↦ wedge (frequency y) (differential y)) := by
    simp only [wedge]
    fun_prop
  have heq : (fun y ↦ wedge (frequency y) (differential y)) = fun _ ↦ 0 :=
    hwedge.ext_on hdense continuous_const hresonant
  exact congrFun heq x

/-- Dense resonant obstructions force dependence at every action in the two-dimensional family. -/
theorem denseResonance_obstruction {X : Type*} [TopologicalSpace X]
    {resonantActions : Set X} (hdense : Dense resonantActions)
    {frequency differential : X → ActionSpace} (hfrequency : Continuous frequency)
    (hdifferential : Continuous differential)
    (hresonant : ∀ x ∈ resonantActions, wedge (frequency x) (differential x) = 0) (x : X) :
    ¬LinearIndependent ℝ ![frequency x, differential x] :=
  not_linearIndependent_of_wedge_eq_zero
    (wedge_eq_zero_of_dense_resonances hdense hfrequency hdifferential hresonant x)

end LeanPool.PoincareThreeBody
