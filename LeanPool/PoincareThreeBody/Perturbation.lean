/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# First mass perturbation of the planar Hamiltonian

This file differentiates the rotating-frame Hamiltonian with respect to the mass parameter at the
Kepler limit. The resulting disturbing function is the explicit input to Poincaré's first
homological equation.
-/

namespace LeanPool.PoincareThreeBody


lemma hasDerivAt_firstPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) :
    HasDerivAt (fun mass ↦ firstPrimaryDistanceSq mass s) (2 * (s 0 - 1 + μ)) μ := by
  have hlinear := (hasDerivAt_const μ (s 0 - 1)).add (hasDerivAt_id μ)
  have hsquare := hlinear.pow 2
  simpa [firstPrimaryDistanceSq] using hsquare.add_const ((s 1) ^ 2)

lemma hasDerivAt_secondPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) :
    HasDerivAt (fun mass ↦ secondPrimaryDistanceSq mass s) (2 * (s 0 + μ)) μ := by
  have hlinear := (hasDerivAt_const μ (s 0)).add (hasDerivAt_id μ)
  have hsquare := hlinear.pow 2
  simpa [secondPrimaryDistanceSq] using hsquare.add_const ((s 1) ^ 2)

lemma hasDerivAt_inverseSqrt_comp {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (hpositive : 0 < f x) :
    HasDerivAt (fun y ↦ 1 / Real.sqrt (f y))
      (-(f' / (2 * Real.sqrt (f x))) / (Real.sqrt (f x)) ^ 2) x := by
  have hsqrt := hf.sqrt hpositive.ne'
  have hinv := hsqrt.inv (Real.sqrt_ne_zero'.mpr hpositive)
  apply hinv.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [one_div]

/-- The coefficient of `μ` in the planar Hamiltonian at the Kepler limit. -/
noncomputable def firstMassPerturbation (s : PhaseSpace) : ℝ :=
  1 / Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2) +
    s 0 / (Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2)) ^ 3 -
      1 / Real.sqrt ((s 0 - 1) ^ 2 + (s 1) ^ 2)

lemma firstMassPerturbation_eq_source_form {s : PhaseSpace}
    (hsecond : secondPrimaryDistanceSq 0 s ≠ 0) :
    firstMassPerturbation s =
      (((s 0) ^ 2 + (s 1) ^ 2) + s 0) /
          (Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2)) ^ 3 -
        1 / Real.sqrt ((s 0 - 1) ^ 2 + (s 1) ^ 2) := by
  have hpositive := secondPrimaryDistanceSq_pos hsecond
  have hroot : Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    simpa [secondPrimaryDistanceSq] using hpositive
  have hsquare : (Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2)) ^ 2 =
      (s 0) ^ 2 + (s 1) ^ 2 := Real.sq_sqrt (by positivity)
  unfold firstMassPerturbation
  field_simp [hroot]
  nlinarith

/-- The explicit disturbing function is the mass derivative of the Hamiltonian at `μ = 0`. -/
theorem hasDerivAt_hamiltonian_mass_zero {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    HasDerivAt (fun μ ↦ hamiltonian μ s) (firstMassPerturbation s) 0 := by
  rcases hs with ⟨hfirst, hsecond⟩
  have hfirstPos := firstPrimaryDistanceSq_pos hfirst
  have hsecondPos := secondPrimaryDistanceSq_pos hsecond
  have hfirstRoot : Real.sqrt (firstPrimaryDistanceSq 0 s) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hfirstPos
  have hsecondRoot : Real.sqrt (secondPrimaryDistanceSq 0 s) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hsecondPos
  have hfirstInverseRaw := hasDerivAt_inverseSqrt_comp
    (hasDerivAt_firstPrimaryDistanceSq 0 s) hfirstPos
  have hfirstInverse : HasDerivAt
      (fun μ ↦ 1 / Real.sqrt (firstPrimaryDistanceSq μ s))
      (-(s 0 - 1) / (Real.sqrt (firstPrimaryDistanceSq 0 s)) ^ 3) 0 := by
    apply hfirstInverseRaw.congr_deriv
    field_simp [hfirstRoot]
    ring
  have hsecondInverseRaw := hasDerivAt_inverseSqrt_comp
    (hasDerivAt_secondPrimaryDistanceSq 0 s) hsecondPos
  have hsecondInverse : HasDerivAt
      (fun μ ↦ 1 / Real.sqrt (secondPrimaryDistanceSq μ s))
      (-s 0 / (Real.sqrt (secondPrimaryDistanceSq 0 s)) ^ 3) 0 := by
    apply hsecondInverseRaw.congr_deriv
    field_simp [hsecondRoot]
    ring
  have hmass : HasDerivAt (fun μ : ℝ ↦ μ) 1 0 := hasDerivAt_id 0
  have hfirstTermRaw := hmass.mul hfirstInverse
  have hfirstTerm : HasDerivAt
      (fun μ ↦ μ * (1 / Real.sqrt (firstPrimaryDistanceSq μ s)))
      (1 / Real.sqrt (firstPrimaryDistanceSq 0 s)) 0 := by
    apply (hfirstTermRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with μ
    rfl
  have hcomplementRaw :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub (hasDerivAt_id 0)
  have hcomplement : HasDerivAt (fun μ : ℝ ↦ 1 - μ) (-1) 0 := by
    apply (hcomplementRaw.congr_deriv (by norm_num)).congr_of_eventuallyEq
    filter_upwards [] with μ
    simp
  have hsecondTermRaw := hcomplement.mul hsecondInverse
  have hsecondTerm : HasDerivAt
      (fun μ ↦ (1 - μ) * (1 / Real.sqrt (secondPrimaryDistanceSq μ s)))
      (-(1 / Real.sqrt (secondPrimaryDistanceSq 0 s)) -
        s 0 / (Real.sqrt (secondPrimaryDistanceSq 0 s)) ^ 3) 0 := by
    apply (hsecondTermRaw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with μ
    rfl
  have hpotential := hfirstTerm.add hsecondTerm
  have hkinetic : HasDerivAt
      (fun _ : ℝ ↦ ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0) 0 0 :=
    hasDerivAt_const 0 _
  have hraw := hkinetic.sub hpotential
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [] with μ
    simp [hamiltonian, potential, div_eq_mul_inv]
  · rw [zero_sub]
    unfold firstMassPerturbation firstPrimaryDistanceSq secondPrimaryDistanceSq
    ring_nf

theorem deriv_hamiltonian_mass_zero {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    deriv (fun μ ↦ hamiltonian μ s) 0 = firstMassPerturbation s :=
  (hasDerivAt_hamiltonian_mass_zero hs).deriv

end LeanPool.PoincareThreeBody
