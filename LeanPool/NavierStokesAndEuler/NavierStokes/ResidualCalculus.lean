/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Calculus of the physical Navier--Stokes residual

These identities concern the ordinary Frechet derivatives used by the actual
PDE target in `ProblemStatement`. The velocity hypotheses give two continuous
spatial derivatives on the time slice and a differentiable time slice at the
point in question. No abstract differential operators are assumed linear.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ResidualCalculus

open ProblemStatement Set
open scoped BigOperators ContDiff

/-- Time differentiation is additive for differentiable velocity time slices. -/
theorem temporalDerivative_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (he : DifferentiableAt ℝ (fun s : ℝ => e (s, x)) t) :
    temporalDerivative (fun z => u z + e z) t x =
      temporalDerivative u t x + temporalDerivative e t x := by
  unfold temporalDerivative
  rw [fderiv_fun_add hu he]
  rfl

/-- The spatial derivative is additive under actual spatial differentiability. -/
theorem spatialDerivative_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    spatialDerivative (fun z => u z + e z) t x =
      spatialDerivative u t x + spatialDerivative e t x := by
  exact fderiv_fun_add hu he

/-- Pressure-gradient additivity follows from derivative additivity and the
fixed Euclidean coordinate basis in the PDE target. -/
theorem pressureGradient_add
    (p q : PressureField) (t : ℝ) (x : Space)
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x)
    (hq : DifferentiableAt ℝ (fun y : Space => q (t, y)) x) :
    pressureGradient (fun z => p z + q z) t x =
      pressureGradient p t x + pressureGradient q t x := by
  unfold pressureGradient
  rw [fderiv_fun_add hp hq]
  simp only [add_apply, add_smul, Finset.sum_add_distrib]

/-- Divergence remains additive for these same genuine spatial derivatives. -/
theorem spatialDivergence_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    spatialDivergence (fun z => u z + e z) t x =
      spatialDivergence u t x + spatialDivergence e t x := by
  unfold spatialDivergence
  rw [spatialDerivative_add u e t x hu he]
  simp only [add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-- The spatial C² hypothesis gives differentiability of each first directional
derivative. This is the second-derivative fact needed for the Laplacian. -/
theorem differentiable_spatial_direction
    (u : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y))) (v : Space) :
    Differentiable ℝ (fun y : Space => spatialDerivative u t y v) := by
  have hfirst : ContDiff ℝ 1 (fderiv ℝ (fun y : Space => u (t, y))) :=
    hu.fderiv_right (by norm_num)
  exact (hfirst.clm_apply contDiff_const).differentiable (by norm_num)

/-- Additivity of the concrete iterated-derivative Laplacian on C² slices. -/
theorem spatialLaplacian_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y)))
    (he : ContDiff ℝ 2 (fun y : Space => e (t, y))) :
    spatialLaplacian (fun z => u z + e z) t x =
      spatialLaplacian u t x + spatialLaplacian e t x := by
  have hdu := hu.differentiable (by norm_num)
  have hde := he.differentiable (by norm_num)
  have hsum : ∀ y : Space,
      spatialDerivative (fun z => u z + e z) t y =
        spatialDerivative u t y + spatialDerivative e t y :=
    fun y => spatialDerivative_add u e t y (hdu y) (hde y)
  unfold spatialLaplacian
  simp_rw [hsum, add_apply]
  simp_rw [fderiv_fun_add
    (differentiable_spatial_direction u t hu _ x)
    (differentiable_spatial_direction e t he _ x), add_apply]
  exact Finset.sum_add_distrib

/-- The quadratic advection term produces exactly its two cross terms and the
self-advection of the perturbation. -/
theorem advection_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    advection (fun z => u z + e z) t x =
      advection u t x + spatialDerivative u t x (e (t, x)) +
        spatialDerivative e t x (u (t, x)) + advection e t x := by
  unfold advection
  rw [spatialDerivative_add u e t x hu he]
  simp only [add_apply, map_add]
  abel

/-- Exact perturbation formula for the physical residual, at viscosity one.
Every operator in this statement is the concrete operator in `ProblemStatement`. -/
theorem navierStokesResidual_add_sub
    (u e : VelocityField) (p q : PressureField) (t : ℝ) (x : Space)
    (hut : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (het : DifferentiableAt ℝ (fun s : ℝ => e (s, x)) t)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y)))
    (he : ContDiff ℝ 2 (fun y : Space => e (t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x)
    (hq : DifferentiableAt ℝ (fun y : Space => q (t, y)) x) :
    navierStokesResidual (fun z => u z + e z) (fun z => p z + q z) t x -
      navierStokesResidual u p t x =
        temporalDerivative e t x - spatialLaplacian e t x + pressureGradient q t x +
          spatialDerivative u t x (e (t, x)) + spatialDerivative e t x (u (t, x)) +
          spatialDerivative e t x (e (t, x)) := by
  have hdu := hu.differentiable (by norm_num)
  have hde := he.differentiable (by norm_num)
  unfold navierStokesResidual
  rw [temporalDerivative_add u e t x hut het, advection_add u e t x (hdu x) (hde x),
    spatialLaplacian_add u e t x hu he, pressureGradient_add p q t x hp hq]
  unfold advection
  abel

/-- A spatial slice of a field smooth on the actual presingular domain is
globally smooth in space at each interior time. -/
theorem spatial_contDiff_of_presingular_smooth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SpaceTime → V) (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun y : Space => g (t, y)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_at_interior hg ht x).comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- Interior time differentiability follows from the same domain smoothness;
no extension through the singular time is assumed. -/
theorem temporal_differentiable_of_presingular_smooth
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SpaceTime → V) (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    DifferentiableAt ℝ (fun s : ℝ => g (s, x)) t := by
  exact ((smooth_at_interior hg ht x).differentiableAt (by simp)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const x))

/-- The perturbation identity applies directly to the smoothness conditions
appearing in the candidate PDE statement, at every interior time. -/
theorem navierStokesResidual_add_sub_of_smooth
    (u e : VelocityField) (p q : PressureField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (he : ContDiffOn ℝ ∞ e preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hq : ContDiffOn ℝ ∞ q preSingularDomain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    navierStokesResidual (fun z => u z + e z) (fun z => p z + q z) t x -
      navierStokesResidual u p t x =
        temporalDerivative e t x - spatialLaplacian e t x + pressureGradient q t x +
          spatialDerivative u t x (e (t, x)) + spatialDerivative e t x (u (t, x)) +
          spatialDerivative e t x (e (t, x)) := by
  exact navierStokesResidual_add_sub u e p q t x
    (temporal_differentiable_of_presingular_smooth u hu t ht x)
    (temporal_differentiable_of_presingular_smooth e he t ht x)
    ((spatial_contDiff_of_presingular_smooth u hu t ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    ((spatial_contDiff_of_presingular_smooth e he t ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    ((spatial_contDiff_of_presingular_smooth p hp t ht).differentiable (by simp) x)
    ((spatial_contDiff_of_presingular_smooth q hq t ht).differentiable (by simp) x)

/-- A constant spatial scalar factors out of the actual spatial derivative. -/
theorem spatialDerivative_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    spatialDerivative (fun z => c • u z) t x = c • spatialDerivative u t x := by
  exact fderiv_fun_const_smul hu c

/-- Constant-scalar linearity of the actual pressure gradient. -/
theorem pressureGradient_const_smul
    (p : PressureField) (t : ℝ) (x : Space) (c : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x) :
    pressureGradient (fun z => c • p z) t x = c • pressureGradient p t x := by
  unfold pressureGradient
  rw [fderiv_fun_const_smul hp c]
  simp only [smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Constant-scalar linearity of divergence, using coordinate evaluation. -/
theorem spatialDivergence_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    spatialDivergence (fun z => c • u z) t x = c * spatialDivergence u t x := by
  unfold spatialDivergence
  rw [spatialDerivative_const_smul u t x c hu]
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Constant-scalar linearity of the concrete second spatial derivative. -/
theorem spatialLaplacian_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y))) :
    spatialLaplacian (fun z => c • u z) t x = c • spatialLaplacian u t x := by
  have hdu := hu.differentiable (by norm_num)
  have hscale : ∀ y : Space,
      spatialDerivative (fun z => c • u z) t y = c • spatialDerivative u t y :=
    fun y => spatialDerivative_const_smul u t y c (hdu y)
  unfold spatialLaplacian
  simp_rw [hscale, smul_apply]
  simp_rw [fderiv_fun_const_smul (differentiable_spatial_direction u t hu _ x) c,
    smul_apply]
  exact (Finset.smul_sum).symm

/-- Velocity scaling squares in advection, because both the direction and the
spatial derivative scale. -/
theorem advection_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    advection (fun z => c • u z) t x = (c * c) • advection u t x := by
  unfold advection
  rw [spatialDerivative_const_smul u t x c hu]
  simp only [smul_apply, map_smul, smul_smul]

/-- The time derivative of a switched velocity includes the derivative of the
switch; it is proved using the Frechet derivative product rule. -/
theorem temporalDerivative_time_smul
    (u : VelocityField) (a : ℝ → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ a t)
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t) :
    temporalDerivative (fun z => a z.1 • u z) t x =
      a t • temporalDerivative u t x + (fderiv ℝ a t 1) • u (t, x) := by
  unfold temporalDerivative
  rw [fderiv_fun_smul ha hu]
  rfl

/-- Exact time-switch identity for the physical PDE, when both velocity and
pressure are multiplied by the same scalar time switch. -/
theorem navierStokesResidual_time_smul
    (u : VelocityField) (p : PressureField) (a : ℝ → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ a t)
    (hut : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y)))
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x) :
    navierStokesResidual (fun z => a z.1 • u z) (fun z => a z.1 • p z) t x =
      a t • navierStokesResidual u p t x + (fderiv ℝ a t 1) • u (t, x) +
        (a t * a t - a t) • advection u t x := by
  have hdu := hu.differentiable (by norm_num)
  have hadv : advection (fun z => a z.1 • u z) t x = (a t * a t) • advection u t x := by
    change advection (fun z => a t • u z) t x = _
    exact advection_const_smul u t x (a t) (hdu x)
  have hlap : spatialLaplacian (fun z => a z.1 • u z) t x =
      a t • spatialLaplacian u t x := by
    change spatialLaplacian (fun z => a t • u z) t x = _
    exact spatialLaplacian_const_smul u t x (a t) hu
  have hgrad : pressureGradient (fun z => a z.1 • p z) t x =
      a t • pressureGradient p t x := by
    change pressureGradient (fun z => a t • p z) t x = _
    exact pressureGradient_const_smul p t x (a t) hp
  unfold navierStokesResidual
  rw [temporalDerivative_time_smul u a t x ha hut, hadv, hlap, hgrad]
  simp only [smul_add, smul_sub, sub_smul]
  abel

/-- A scalar time switch preserves the divergence-free condition. -/
theorem time_smul_divergence_free
    (u : VelocityField) (a : ℝ → ℝ) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (hdiv : spatialDivergence u t x = 0) :
    spatialDivergence (fun z => a z.1 • u z) t x = 0 := by
  change spatialDivergence (fun z => a t • u z) t x = 0
  rw [spatialDivergence_const_smul u t x (a t) hu, hdiv, mul_zero]

end NavierStokes.ResidualCalculus
