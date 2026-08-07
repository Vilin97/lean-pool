/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.KeplerFlow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FinCases

/-!
# Differential of the rotating Kepler Hamiltonian

We compute the Fréchet derivative of the mass-zero Hamiltonian and identify its Hamiltonian vector
field with `rotatingKeplerVectorField`.  Consequently, a Poisson bracket with the Kepler
Hamiltonian is exactly differentiation along a Kepler flow line.
-/

namespace LeanPool.PoincareThreeBody


/-- Explicit differential of the rotating Kepler Hamiltonian. -/
noncomputable def rotatingKeplerDifferential (s : PhaseSpace) : PhaseSpace →L[ℝ] ℝ :=
  let radius := Real.sqrt (s 0 ^ 2 + s 1 ^ 2)
  let projection : Fin 4 → PhaseSpace →L[ℝ] ℝ := fun i ↦ ContinuousLinearMap.proj i
  (s 0 / radius ^ 3 - s 3) • projection 0 +
    (s 1 / radius ^ 3 + s 2) • projection 1 +
    (s 2 + s 1) • projection 2 +
    (s 3 - s 0) • projection 3

/-- Fréchet derivative of the mass-zero Hamiltonian away from the Kepler collision. -/
theorem hasFDerivAt_hamiltonian_zero {s : PhaseSpace}
    (horigin : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    HasFDerivAt (hamiltonian 0) (rotatingKeplerDifferential s) s := by
  let x : PhaseSpace → ℝ := fun y ↦ y 0
  let y : PhaseSpace → ℝ := fun y ↦ y 1
  let px : PhaseSpace → ℝ := fun y ↦ y 2
  let py : PhaseSpace → ℝ := fun y ↦ y 3
  let radiusSq : PhaseSpace → ℝ := fun state ↦ x state ^ 2 + y state ^ 2
  have hprojection (i : Fin 4) : HasFDerivAt (fun state : PhaseSpace ↦ state i)
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj i) s := by
    have h :=
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj i).hasFDerivAt (x := s)
    apply h.congr_of_eventuallyEq
    filter_upwards [] with state
    rfl
  have hx : HasFDerivAt x
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 0) s :=
    hprojection 0
  have hy : HasFDerivAt y
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 1) s :=
    hprojection 1
  have hpx : HasFDerivAt px
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 2) s :=
    hprojection 2
  have hpy : HasFDerivAt py
      (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 3) s :=
    hprojection 3
  have hradiusSqRaw := (hx.mul hx).add (hy.mul hy)
  have hradiusSq : HasFDerivAt radiusSq
      (x s • (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 0) +
        x s • (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 0) +
        (y s • (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 1) +
          y s • (show PhaseSpace →L[ℝ] ℝ from ContinuousLinearMap.proj 1))) s := by
    apply hradiusSqRaw.congr_of_eventuallyEq
    filter_upwards [] with state
    simp [radiusSq, pow_two]
  have hradiusSqPos : 0 < radiusSq s := by
    change 0 < s 0 ^ 2 + s 1 ^ 2
    exact lt_of_le_of_ne (by positivity) (Ne.symm horigin)
  have hinverseScalar := hasDerivAt_inverseSqrt_comp
    (hasDerivAt_id (radiusSq s)) hradiusSqPos
  have hinverseScalar' : HasDerivAt (fun value : ℝ ↦ 1 / Real.sqrt value)
      (-(1 / (2 * Real.sqrt (radiusSq s))) /
        Real.sqrt (radiusSq s) ^ 2) (radiusSq s) := by
    simpa using hinverseScalar
  have hinverse := hinverseScalar'.hasFDerivAt.comp s hradiusSq
  have hkinetic := ((hpx.mul hpx).add (hpy.mul hpy)).const_mul (1 / 2 : ℝ)
  have hcoriolis := (hpx.mul hy).sub (hpy.mul hx)
  have hraw := (hkinetic.add hcoriolis).sub hinverse
  apply (hraw.congr_fderiv ?_).congr_of_eventuallyEq
  · filter_upwards [] with state
    simp [hamiltonian_zero, x, y, px, py]
    ring
  · ext direction
    have hroot : Real.sqrt (s 0 ^ 2 + s 1 ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hradiusSqPos
    simp only [rotatingKeplerDifferential, add_apply, sub_apply, smul_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      x, y, px, py, radiusSq]
    field_simp [hroot]
    ring

theorem fderiv_hamiltonian_zero {s : PhaseSpace}
    (horigin : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    fderiv ℝ (hamiltonian 0) s = rotatingKeplerDifferential s :=
  (hasFDerivAt_hamiltonian_zero horigin).fderiv

/-- The Poisson bracket with the Kepler Hamiltonian is the directional derivative along its
explicit Hamiltonian vector field. -/
theorem poissonBracket_hamiltonian_zero_eq_fderiv_apply
    (F : PhaseSpace → ℝ) {s : PhaseSpace}
    (horigin : s 0 ^ 2 + s 1 ^ 2 ≠ 0) :
    poissonBracket F (hamiltonian 0) s =
      fderiv ℝ F s (rotatingKeplerVectorField s) := by
  rw [poissonBracket, fderiv_hamiltonian_zero horigin]
  let radius := Real.sqrt (s 0 ^ 2 + s 1 ^ 2)
  have hvector : rotatingKeplerVectorField s =
      (s 2 + s 1) • coordinateVector 0 +
        (s 3 - s 0) • coordinateVector 1 +
        (s 3 - s 0 / radius ^ 3) • coordinateVector 2 +
        (-s 2 - s 1 / radius ^ 3) • coordinateVector 3 := by
    funext i
    fin_cases i <;> simp [rotatingKeplerVectorField, coordinateVector, radius]
  rw [hvector]
  simp only [map_add, map_smul, rotatingKeplerDifferential,
    add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp [coordinateVector, radius, div_eq_mul_inv]
  ring

/-- Along the true resonant orbit, the time derivative of any differentiable observable is its
Poisson bracket with the mass-zero Hamiltonian. -/
theorem DifferentiableAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint
    {F : PhaseSpace → ℝ} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hF : DifferentiableAt ℝ F
      (orientedResonantKeplerPhasePoint p q eccentricity orientation time)) :
    HasDerivAt
      (fun t ↦ F (orientedResonantKeplerPhasePoint p q eccentricity orientation t))
      (poissonBracket F (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time)) time := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have horigin : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    have hfirstAction : resonantFirstAction p q ≠ 0 :=
      (resonantFirstAction_pos hp hq).ne'
    have hradius := eccentricRadius_pos (anomaly :=
        resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
      heccentricityOne
    have hsquare := orientedResonantEllipsePosition_sq
      (p := p) (q := q) (orientation := orientation) (time := time)
      heccentricity heccentricityOne.le
    change orientedResonantEllipsePosition p q eccentricity orientation time 0 ^ 2 +
      orientedResonantEllipsePosition p q eccentricity orientation time 1 ^ 2 ≠ 0
    rw [hsquare]
    exact (sq_pos_of_pos hradius).ne'
  have hchain := HasFDerivAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint
    hF.hasFDerivAt hp hq heccentricity heccentricityOne (s := state) rfl
  apply hchain.congr_deriv
  exact (poissonBracket_hamiltonian_zero_eq_fderiv_apply F horigin).symm

end LeanPool.PoincareThreeBody
