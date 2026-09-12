/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration
import LeanPool.NavierStokesAndEuler.ForMathlib.Gronwall
import LeanPool.NavierStokesAndEuler.NavierStokes.SolutionDifference
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Classical uniqueness for periodic Navier--Stokes fields

The differential operators are those of `ProblemStatement`. The energy
estimate is derived from the equations and periodic integration by parts.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokes.PeriodicUniqueness

open ProblemStatement

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- Slab, given by `Icc a b ×ˢ univ`. -/
noncomputable def slab (a b : ℝ) : Set SpaceTime := Icc a b ×ˢ univ

theorem spatial_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (fun x : Space => u (t, x)) :=
  SolutionDifference.spatial_smooth hu ht

theorem smooth_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : Space) : ContDiffAt ℝ ∞ u (t, x) :=
  SolutionDifference.smooth_at_interior hu ht x

theorem spatialDerivative_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDerivative (u - v) t x = spatialDerivative u t x - spatialDerivative v t x :=
  SolutionDifference.spatialDerivative_sub hu hv x

theorem spatialDivergence_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDivergence (u - v) t x = spatialDivergence u t x - spatialDivergence v t x :=
  SolutionDifference.spatialDivergence_sub hu hv x

theorem advection_difference {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    advection u t x - advection v t x =
      spatialDerivative u t x ((u - v) (t, x)) +
        spatialDerivative (u - v) t x (v (t, x)) :=
  SolutionDifference.advection_difference hu hv x

theorem spatialLaplacian_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialLaplacian (u - v) t x = spatialLaplacian u t x - spatialLaplacian v t x :=
  SolutionDifference.spatialLaplacian_sub hu hv x

theorem pressureGradient_sub {p q : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x))) (x : Space) :
    pressureGradient (p - q) t x = pressureGradient p t x - pressureGradient q t x :=
  SolutionDifference.pressureGradient_sub hp hq x

theorem temporalDerivative_sub {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (hv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t) :
    temporalDerivative (u - v) t x = temporalDerivative u t x - temporalDerivative v t x :=
  SolutionDifference.temporalDerivative_sub hu hv

/-- Subtract the actual Navier--Stokes residuals, retaining the favorable
transport decomposition `Du(w) + Dw(v)`. -/
theorem difference_equation {u v : VelocityField} {p q : PressureField} {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : navierStokesResidual u p t x = navierStokesResidual v q t x) :
    temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
      spatialDerivative u t x ((u - v) (t, x)) -
      spatialDerivative (u - v) t x (v (t, x)) - pressureGradient (p - q) t x :=
  SolutionDifference.difference_equation hu hv hp hq htu htv hNS

/-- The only indefinite energy term is controlled by the operator norm of
the first velocity gradient. -/
theorem nonlinear_energy_bound (A : Space →L[ℝ] Space) (w : Space) {B : ℝ}
    (hB : ‖A‖ ≤ B) : -⟪w, A w⟫_ℝ ≤ B * ‖w‖ ^ 2 :=
  SolutionDifference.nonlinear_energy_bound A w hB

/-- The zero-initial-data Gronwall conclusion, proved by the integrating
factor and mean-value theorem. Only interior derivatives are required. -/
theorem gronwall_zero {a b K : ℝ} {E E' : ℝ → ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn E (Icc a b)) (hinitial : E a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo a b, E' t ≤ K * E t) :
    ∀ t ∈ Icc a b, E t = 0 :=
  Gronwall.eq_zero_of_deriv_le hab hcont hinitial hnonneg hderiv hbound

/-- The ordinary spatial derivative at a time endpoint is the restriction
of the joint within-derivative to spatial directions. -/
theorem spatialDerivative_eq_within_comp {a b t : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (ht : t ∈ Icc a b) (x : Space) :
    spatialDerivative u t x =
      (fderivWithin ℝ u (slab a b) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  SolutionDifference.spatialDerivative_eq_within_comp hu ht x

/-- Compactness supplies the spatial-gradient bound used by the energy
estimate; it is a conclusion from smoothness, not an input to uniqueness. -/
theorem exists_gradient_bound {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) {K : Set Space} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K, ‖spatialDerivative u t x‖ ≤ B :=
  SolutionDifference.exists_gradient_bound hab hu hK

/-- Reconstruction in the standard Euclidean coordinate basis. -/
theorem sum_coordinates (x : Space) :
    (∑ i : Fin 3, x i • coordinateVector i) = x :=
  SolutionDifference.sum_coordinates x

/-- Unit coordinate periods imply invariance under every integer lattice
translation; no quotient or fundamental-domain claim is assumed. -/
theorem periodic_lattice {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i))
    (n : Fin 3 → ℤ) : Function.Periodic f (∑ i : Fin 3, n i • coordinateVector i) := by
  have hsum (s : Finset (Fin 3)) : Function.Periodic f (∑ i ∈ s, n i • coordinateVector i) := by
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s his ih =>
      simpa only [Finset.sum_insert his] using ((hf i).zsmul (n i)).add_period ih
  simpa using hsum Finset.univ

/-- Each point has a representative in the unit cube with the same value
under every function having the three unit coordinate periods. -/
theorem exists_cube_representative {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i)) (x : Space) :
    ∃ y : Space, (∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1) ∧ f y = f x := by
  let y : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => Int.fract (x i))
  have hy : ∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨Int.fract_nonneg (x i), (Int.fract_lt_one (x i)).le⟩
  refine ⟨y, hy, ?_⟩
  have hxy : x = y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i := by
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    ext j
    change x j = (EuclideanSpace.proj j) (y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i)
    simp only [map_add, map_sum, map_zsmul]
    simp [y, coordinateVector, Int.fract_add_floor]
  have hp := periodic_lattice hf (fun i => ⌊x i⌋)
  rw [hxy]
  exact (hp y).symm

theorem periodic_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hp : ∀ x : Space, ∀ i : Fin 3, f (x + coordinateVector i) = f x)
    (x : Space) (i : Fin 3) :
    fderiv ℝ f (x + coordinateVector i) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right (coordinateVector i)]
  exact congrArg (fun g : Space → V => fderiv ℝ g x) (funext (fun y => hp y i))

theorem spatial_partial_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x (coordinateVector i)) :=
  SolutionDifference.spatial_partial_contDiff hf i

theorem component_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => f x j) :=
  SolutionDifference.component_contDiff hf j

theorem fderiv_component {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => f y j) x v = fderiv ℝ f x v j :=
  SolutionDifference.fderiv_component hf j x v

theorem fderiv_apply_eq_sum (f : Space → ℝ) (x v : Space) :
    fderiv ℝ f x v = ∑ i : Fin 3, v i * fderiv ℝ f x (coordinateVector i) :=
  SolutionDifference.fderiv_apply_eq_sum f x v

theorem fderiv_normsq {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x v : Space) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) x v = 2 * ⟪f x, fderiv ℝ f x v⟫_ℝ :=
  SolutionDifference.fderiv_normsq hf x v

theorem fderiv_inner {f g : Space → Space} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x v : Space) :
    fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v =
      ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ :=
  SolutionDifference.fderiv_inner hf hg x v

/-- The pressure term paired with a vector is its scalar directional
derivative. This uses exactly the gradient definition in the target. -/
theorem inner_pressureGradient (p : PressureField) (t : ℝ) (x w : Space) :
    ⟪w, pressureGradient p t x⟫_ℝ = fderiv ℝ (fun y => p (t, y)) x w :=
  SolutionDifference.inner_pressureGradient p t x w

theorem energy_density_derivative {u : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s => u (s, x)) t) :
    HasDerivAt (fun s : ℝ => ‖u (s, x)‖ ^ 2)
      (2 * ⟪u (t, x), temporalDerivative u t x⟫_ℝ) t :=
  SolutionDifference.energy_density_derivative hu

open PeriodicIntegration

theorem component_periodic {f : Space → Space} (hf : UnitPeriods f) (j : Fin 3) :
    UnitPeriods (fun x => f x j) := by
  intro x i
  exact congrArg (fun v : Space => v j) (hf x i)

theorem spatial_partial_periodic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : UnitPeriods f) (i : Fin 3) : UnitPeriods (spatialPartial i f) := by
  intro x j
  exact congrArg (fun A : Space →L[ℝ] V => A (coordinateVector i)) (periodic_fderiv hf x j)

theorem normsq_periodic {f : Space → Space} (hf : UnitPeriods f) :
    UnitPeriods (fun x => ‖f x‖ ^ 2) := by
  intro x i
  exact congrArg (fun v : Space => ‖v‖ ^ 2) (hf x i)

/-- Scalar transport integration by parts, derived from the three
coordinate identities on the unit cube. -/
theorem cubeIntegral_fderiv_apply {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) =
      -cubeIntegral (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hleft : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x
    exact fderiv_apply_eq_sum f x (v x)
  have hright : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [hleft, hright]
  dsimp only [spatialPartial]
  rw [cubeIntegral_sum Finset.univ _ (fun i _ =>
      (component_contDiff hv i).continuous.fun_mul (spatial_partial_contDiff hf i).continuous),
    cubeIntegral_sum Finset.univ _ (fun i _ =>
      hf.continuous.fun_mul (component_contDiff (spatial_partial_contDiff hv i) i).continuous),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := cubeIntegral_mul_partial ((component_contDiff hv i).of_le (nat_le_infty 1))
    (hf.of_le (nat_le_infty 1)) (component_periodic hpv i) hpf i
  simpa only [spatialPartial, fderiv_component hv] using h

theorem cubeIntegral_fderiv_apply_zero {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) = 0 := by
  rw [cubeIntegral_fderiv_apply hf hv hpf hpv]
  simp only [hdiv, mul_zero, cubeIntegral_zero, neg_zero]

/-- Divergence-free transport has zero contribution to the energy. -/
theorem cubeIntegral_transport_energy_zero {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hpw : UnitPeriods w) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  have h := cubeIntegral_fderiv_apply_zero (hw.norm_sq ℝ) hv (normsq_periodic hpw) hpv hdiv
  have hfun : (fun x => fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) := by
    funext x
    exact fderiv_normsq hw x (v x)
  rw [hfun, cubeIntegral_const_mul] at h
  linarith

/-- Vector integration by parts follows from the scalar derivative of
the Euclidean inner product; it is not assumed as an energy identity. -/
theorem cubeIntegral_inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : UnitPeriods f) (hpg : UnitPeriods g) (i : Fin 3) :
    cubeIntegral (fun x => ⟪f x, spatialPartial i g x⟫_ℝ) =
      -cubeIntegral (fun x => ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have hp : UnitPeriods (fun x => ⟪f x, g x⟫_ℝ) := by
    intro x j
    change ⟪f (x + coordinateVector j), g (x + coordinateVector j)⟫_ℝ = _
    rw [hpf x j, hpg x j]
  have h := cubeIntegral_partial_eq_zero ((hf.inner ℝ hg).of_le (nat_le_infty 1)) hp i
  have hfun : spatialPartial i (fun x => ⟪f x, g x⟫_ℝ) =
      (fun x => ⟪f x, spatialPartial i g x⟫_ℝ + ⟪spatialPartial i f x, g x⟫_ℝ) := by
    funext x
    exact fderiv_inner hf hg x (coordinateVector i)
  rw [hfun] at h
  dsimp only [spatialPartial] at h ⊢
  rw [cubeIntegral_add
    (hf.inner ℝ (spatial_partial_contDiff hg i)).continuous
    ((spatial_partial_contDiff hf i).inner ℝ hg).continuous] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The viscosity term is minus the actual integrated sum of squared
coordinate derivatives of the difference field. -/
theorem cubeIntegral_laplacian_energy {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x))) :
    cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)) := by
  have hsum : cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      ∑ i : Fin 3, cubeIntegral (fun x =>
        ⟪w (t, x), spatialPartial i (spatialPartial i (fun y => w (t, y))) x⟫_ℝ) := by
    simp only [spatialLaplacian, inner_sum]
    exact cubeIntegral_sum Finset.univ _ (fun i _ =>
      (hw.inner ℝ (spatial_partial_contDiff (spatial_partial_contDiff hw i) i)).continuous)
  rw [hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold spatialPartial
  simpa only [spatialPartial, real_inner_self_eq_norm_sq] using
    cubeIntegral_inner_partial hw (spatial_partial_contDiff hw i) hpw
      (spatial_partial_periodic hpw i) i

/-- Pressure has zero energy contribution when the difference velocity
is divergence free. -/
theorem cubeIntegral_pressure_energy_zero {w : VelocityField} {p : PressureField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hdiv : ∀ x, spatialDivergence w t x = 0) :
    cubeIntegral (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) = 0 := by
  have hfun : (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) =
      (fun x => fderiv ℝ (fun y => p (t, y)) x (w (t, x))) := by
    funext x
    exact inner_pressureGradient p t x (w (t, x))
  rw [hfun]
  exact cubeIntegral_fderiv_apply_zero hp hw hpp hpw hdiv

theorem spatialLaplacian_contDiff {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x))) :
    ContDiff ℝ ∞ (spatialLaplacian w t) :=
  SolutionDifference.spatialLaplacian_contDiff hw

theorem pressureGradient_contDiff {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x))) :
    ContDiff ℝ ∞ (pressureGradient p t) :=
  SolutionDifference.pressureGradient_contDiff hp

theorem unitPeriods_sub {V : Type*} [Sub V] {f g : Space → V}
    (hf : UnitPeriods f) (hg : UnitPeriods g) : UnitPeriods (f - g) := by
  intro x i
  change f (x + coordinateVector i) - g (x + coordinateVector i) = f x - g x
  rw [hf x i, hg x i]

/-- Squared `L²` distance, using the actual unit-cube Lebesgue integral. -/
noncomputable def energy (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ‖(u - v) (t, x)‖ ^ 2)

/-- Energy rate, given by `cubeIntegral (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u -
v) t x⟫_ℝ)`. -/
noncomputable def energyRate (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)

/-- Dissipation, given by `∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t,
y)) x‖ ^ 2)`. -/
noncomputable def dissipation (w : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)

/-- Coupling, given by `cubeIntegral (fun x => ⟪w (t, x), spatialDerivative u t x (w (t,
x))⟫_ℝ)`. -/
noncomputable def coupling (u w : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)

theorem energy_nonneg (u v : VelocityField) (t : ℝ) : 0 ≤ energy u v t :=
  cubeIntegral_nonneg (fun _ => sq_nonneg _)

theorem dissipation_nonneg (w : VelocityField) (t : ℝ) : 0 ≤ dissipation w t :=
  Finset.sum_nonneg (fun _ _ => cubeIntegral_nonneg (fun _ => sq_nonneg _))

/-- The exact difference-energy balance, derived from the actual PDE,
pressure cancellation, divergence-free transport, and viscous integration
by parts. No energy inequality is an input. -/
theorem energy_balance {u v : VelocityField} {p q : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x) :
    energyRate u v t = -2 * dissipation (u - v) t - 2 * coupling u (u - v) t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hpw : UnitPeriods (fun x : Space => (u - v) (t, x)) := unitPeriods_sub hpu hpv
  have hdw : ∀ x, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdu x, hdv x, sub_self]
  have hL := (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hN := (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous
  have hT := (hw.inner ℝ ((hw.fderiv_right infty_add_one_le).clm_apply hv)).continuous
  have hP := (hw.inner ℝ (pressureGradient_contDiff (p := p - q) (t := t) (hp.sub hq))).continuous
  have hEq : (fun x => ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) =
      (fun x => ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (hNS x)]
    simp only [inner_sub_right]
  unfold energyRate
  rw [cubeIntegral_const_mul, hEq]
  change 2 * cubeIntegral (fun x =>
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => u (t, y)) x ((u - v) (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => (u - v) (t, y)) x (v (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) = _
  rw [cubeIntegral_sub ((hL.fun_sub hN).fun_sub hT) hP, cubeIntegral_sub (hL.fun_sub hN) hT,
    cubeIntegral_sub hL hN, cubeIntegral_laplacian_energy hw hpw,
    cubeIntegral_transport_energy_zero hw hv hpw hpv hdv,
    cubeIntegral_pressure_energy_zero hw (hp.sub hq) hpw (unitPeriods_sub hpp hpq) hdw]
  simp only [sub_zero, dissipation, coupling, spatialDerivative]
  ring

/-- Integrating the pointwise nonlinear bound only needs a gradient bound
on the compact unit cube. -/
theorem neg_coupling_le_energy {u v : VelocityField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    -coupling u (u - v) t ≤ B * energy u v t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  unfold coupling energy
  rw [← cubeIntegral_neg, ← cubeIntegral_const_mul]
  apply cubeIntegral_mono_on_cube
    (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous.neg
    (continuous_const.mul (hw.norm_sq ℝ).continuous)
  intro y hy
  exact nonlinear_energy_bound _ _ (hB y hy)

theorem energy_rate_le {u v : VelocityField} {p q : PressureField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    energyRate u v t ≤ (2 * B) * energy u v t := by
  rw [energy_balance hu hv hp hq hpu hpv hpp hpq hdu hdv htu htv hNS]
  have hc := neg_coupling_le_energy hu hv hB
  have hd := dissipation_nonneg (u - v) t
  nlinarith

theorem time_differentiable_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : SpaceTime → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : Space) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t :=
  SolutionDifference.time_differentiable_at_interior hu ht x

theorem energy_continuousOn {a b : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b)) :
    ContinuousOn (energy u v) (Icc a b) := by
  have hF : ContDiffOn ℝ ∞ (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Icc a b ×ˢ univ) := (hu.sub hv).norm_sq ℝ
  exact cubeIntegral_continuousOn_Icc hF.continuousOn

/-- Differentiation under the genuine spatial integral is justified by
joint smoothness and compactness of the cube. -/
theorem energy_hasDerivAt {a b t : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b))
    (ht : t ∈ Ioo a b) : HasDerivAt (energy u v) (energyRate u v t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Ioo a b ×ˢ univ) :=
    (((hu.sub hv).norm_sq ℝ).of_le (nat_le_infty 1)).mono
      (fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have h := hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hF ht
  have hrate : (fun x => deriv (fun s : ℝ => ‖(u - v) (s, x)‖ ^ 2) t) =
      (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) := by
    funext x
    exact (energy_density_derivative
      (time_differentiable_at_interior (u := u - v) (hu.sub hv) ht x)).deriv
  rw [hrate] at h
  exact h

theorem energy_initial_zero {u v : VelocityField} {a : ℝ}
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) : energy u v a = 0 := by
  have hzero : (fun x => ‖(u - v) (a, x)‖ ^ 2) = (fun _ : Space => (0 : ℝ)) := by
    funext x
    simp only [Pi.sub_apply, hinitial x, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  unfold energy
  rw [hzero, cubeIntegral_zero]

/-- Zero squared `L²` difference implies equality everywhere, using
continuity on the cube and the explicitly proved periodic representatives. -/
theorem eq_of_energy_zero {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hv : Continuous (fun x : Space => v (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hzero : energy u v t = 0) (x : Space) : u (t, x) = v (t, x) := by
  have hc := eq_zero_on_cube_of_integral_norm_sq_eq_zero (hu.sub hv) hzero
  have hpw : UnitPeriods (fun z : Space => (u - v) (t, z)) := unitPeriods_sub hpu hpv
  obtain ⟨z, hz, hzx⟩ := exists_cube_representative
    (f := fun z : Space => (u - v) (t, z)) (fun i y => hpw y i) x
  let y : Coords := toSpace.symm z
  have hy : y ∈ cube := by
    constructor
    · intro i
      exact (hz i).1
    · intro i
      exact (hz i).2
  have hzy : toSpace y = z := toSpace.apply_symm_apply z
  have hcz := hc y hy
  rw [hzy] at hcz
  exact sub_eq_zero.mp (hzx.symm.trans hcz)

/-- Classical uniqueness on a compact time interval for the exact periodic
Navier--Stokes equation of `ProblemStatement`, with viscosity one. Both
solutions have the same force and initial datum. The energy inequality,
uniform gradient bound, and spatial integration identities are conclusions
of the preceding proofs, not assumptions of this theorem. -/
theorem classical_uniqueness_on_Icc {a b : ℝ}
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hv : ContDiffOn ℝ ∞ v (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hq : ContDiffOn ℝ ∞ q (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u)
    (hpv : UnitSpatialPeriodsOn (Icc a b) v)
    (hpp : UnitSpatialPeriodsOn (Icc a b) p)
    (hpq : UnitSpatialPeriodsOn (Icc a b) q)
    (hdu : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSu : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual u p t x = f (t, x))
    (hNSv : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual v q t x = f (t, x))
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) :
    ∀ t ∈ Icc a b, ∀ x : Space, u (t, x) = v (t, x) := by
  by_cases hab : a < b
  · have hcompact : IsCompact (toSpace '' cube) :=
      (show IsCompact cube from isCompact_Icc).image toSpace.continuous
    obtain ⟨B, _, hB⟩ := exists_gradient_bound hab hu hcompact
    have hbound : ∀ t ∈ Ioo a b, energyRate u v t ≤ (2 * B) * energy u v t := by
      intro t ht
      have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      exact energy_rate_le (spatial_smooth hu ht') (spatial_smooth hv ht')
        (spatial_smooth hp ht') (spatial_smooth hq ht')
        (hpu t ht') (hpv t ht') (hpp t ht') (hpq t ht') (hdu t ht) (hdv t ht)
        (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
        (fun x => (hNSu t ht x).trans (hNSv t ht x).symm)
        (fun y hy => hB t ht' (toSpace y) ⟨y, hy, rfl⟩)
    have hzero := gronwall_zero hab.le (energy_continuousOn hu hv)
      (energy_initial_zero hinitial) (fun t _ => energy_nonneg u v t)
      (fun t ht => energy_hasDerivAt hu hv ht) hbound
    intro t ht x
    exact eq_of_energy_zero (spatial_smooth hu ht).continuous (spatial_smooth hv ht).continuous
      (hpu t ht) (hpv t ht) (hzero t ht) x
  · intro t ht x
    have ht' : t = a := le_antisymm (ht.2.trans (le_of_not_gt hab)) ht.1
    simpa only [ht'] using hinitial x

/-- Direct application to the exact candidate specification: any other
classical periodic solution with its force and zero initial velocity must
agree on every compact interval strictly before time one. The comparison
solution is not assumed to satisfy the candidate blow-up condition. -/
theorem candidate_unique_on_Icc {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) {T : ℝ} (hT : T < 1)
    {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (slab 0 T)) (hq : ContDiffOn ℝ ∞ q (slab 0 T))
    (hpv : UnitSpatialPeriodsOn (Icc (0 : ℝ) T) v)
    (hpq : UnitSpatialPeriodsOn (Icc (0 : ℝ) T) q)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x : Space, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x) := by
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
  apply classical_uniqueness_on_Icc (h.velocity_smooth.mono hsub) hv
    (h.pressure_smooth.mono hsub) hq
  · intro t ht x i
    exact h.velocity_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · exact hpv
  · intro t ht x i
    exact h.pressure_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · exact hpq
  · intro t ht x
    exact h.divergence_free t ⟨ht.1.le, ht.2.trans hT⟩ x
  · exact hdv
  · intro t ht x
    exact h.navier_stokes t ⟨ht.1, ht.2.trans hT⟩ x
  · exact hNSv
  · intro x
    exact (h.zero_initial_velocity x).trans (hvzero x).symm

end NavierStokes.PeriodicUniqueness
