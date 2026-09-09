/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init

/-! Euler's spatial/amplitude rescaling, proved for the actual first
derivatives and scalar pressure. Time is unchanged. -/

@[expose] public section


noncomputable section

namespace EulerSpatialRescaling

open ContinuousLinearMap InnerProductSpace EulerLagrangian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Coordinates, given by `(fst ℝ ℝ E).prod ((ell⁻¹ • ContinuousLinearMap.id ℝ E).comp (snd ℝ ℝ
E))`. -/
def coordinates (ell : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (fst ℝ ℝ E).prod ((ell⁻¹ • ContinuousLinearMap.id ℝ E).comp (snd ℝ ℝ E))

omit [CompleteSpace E] in
@[simp] theorem coordinates_apply (ell : ℝ) (q : ℝ × E) :
    coordinates ell q=(q.1,ell⁻¹ • q.2) := rfl

/-- Velocity, given by `ell • u (coordinates ell q)`. -/
def velocity (ell : ℝ) (u : ℝ × E → E) (q : ℝ × E) : E :=
  ell • u (coordinates ell q)

/-- Pressure, given by `ell^2*p (coordinates ell q)`. -/
def pressure (ell : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E) : ℝ :=
  ell^2*p (coordinates ell q)

omit [CompleteSpace E] in
theorem velocity_hasFDerivAt (ell : ℝ) (u : ℝ × E → E) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q)) :
    HasFDerivAt (velocity ell u) (ell • (fderiv ℝ u (coordinates ell q)).comp (coordinates ell)) q
        := by
  have hc : HasFDerivAt (coordinates ell : ℝ × E → ℝ × E) (coordinates ell) q :=
    (coordinates (E := E) ell).hasFDerivAt
  exact (hu.hasFDerivAt.comp q hc).const_smul ell

theorem pressure_gradient (ell : ℝ) (hell : ell ≠ 0) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2)) :
    gradient (fun y => pressure ell p (q.1,y)) q.2 =
      ell • gradient (fun y => p (q.1,y)) (ell⁻¹ • q.2) := by
  have hs := (hp.hasFDerivAt.comp q.2 (ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul
      (ell^2)
  change HasFDerivAt (fun y => ell^2 • p (q.1,ell⁻¹ • y)) _ q.2 at hs
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (fun y => ell^2 • p (q.1,ell⁻¹ • y)) q.2) v = _
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,hs.fderiv]
  simp only [smul_apply,comp_apply,id_apply,map_smul,smul_eq_mul]
  field_simp [hell]

theorem momentumResidual_eq (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q))
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2)) :
    momentumResidual (velocity ell u) (pressure ell p) q =
      ell • momentumResidual u p (coordinates ell q) := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt ell u q hu).fderiv,pressure_gradient ell hell p q hp]
  simp only [smul_apply,comp_apply]
  have hd : coordinates ell ((1 : ℝ),velocity ell u q) = (1,u (coordinates ell q)) := by
    simp only [coordinates_apply,velocity,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rw [hd,← smul_add]
  rfl

theorem momentumResidual_zero (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q))
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2))
    (hEuler : momentumResidual u p (coordinates ell q) = 0) :
    momentumResidual (velocity ell u) (pressure ell p) q=0 := by
  rw [momentumResidual_eq ell hell u p q hu hp,hEuler,smul_zero]

omit [CompleteSpace E] in
theorem spatial_derivative (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (t : ℝ) (x : E)
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) (ell⁻¹ • x)) :
    fderiv ℝ (fun y => velocity ell u (t,y)) x =
      fderiv ℝ (fun y => u (t,y)) (ell⁻¹ • x) := by
  have hd := (hu.hasFDerivAt.comp x (ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul ell
  change HasFDerivAt (fun y => velocity ell u (t,y)) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,id_apply,map_smul,smul_smul,mul_inv_cancel₀ hell,one_smul]

end EulerSpatialRescaling
