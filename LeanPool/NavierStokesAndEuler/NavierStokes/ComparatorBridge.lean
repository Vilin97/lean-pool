/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorDefinitions
public import LeanPool.NavierStokesAndEuler.NavierStokes.Solution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Coordinate and viscosity bridge to the Clay statements

This module translates the project's physical differential operators to the
comparator's operators, and normalizes any positive viscosity to one. It uses
only the independent comparator definitions; no reference theorem is imported.
The applications to the periodic and finite-energy candidates share the same
normalization theorem, `normalized_solution_core`.

The shared normalization API adapts work by Code4me2:
https://github.com/Code4me2/NavierStokesAndEuler/tree/26e896edbdbe1215c0d50ddba24b2b6453646f5f.
-/

public section


noncomputable section

namespace NavierStokes.ComparatorBridge

open Set Function InnerProductSpace ProblemStatement
open scoped ContDiff Laplacian RealInnerProductSpace

/-- Change the argument order from `(time, space)` to `space, time`. -/
@[expose] def toComparator {V : Type*} (f : SpaceTime → V) : Space → ℝ → V :=
  fun x t => f (t, x)

/-- Change the argument order from `space, time` to `(time, space)`. -/
@[expose] def fromComparator {V : Type*} (f : Space → ℝ → V) : SpaceTime → V :=
  fun z => f z.2 z.1

theorem divergence_eq (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence v t x = Comparator.divergence (fun y => v (t, y)) x := by
  rw [Comparator.divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [spatialDivergence, spatialDerivative, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem gradient_eq (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient p t x = gradient (fun y => p (t, y)) x := by
  apply ext_inner_left_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro i
  simp [pressureGradient, coordinateVector, EuclideanSpace.basisFun_apply,
    inner_gradient_right, EuclideanSpace.inner_single_left, Pi.single_apply]

theorem laplacian_eq (v : VelocityField) (t : ℝ) (x : Space)
    (hv : ContDiff ℝ 2 (fun y => v (t, y))) :
    spatialLaplacian v t x = Δ (fun y => v (t, y)) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [spatialLaplacian, spatialDerivative, EuclideanSpace.basisFun_apply,
    coordinateVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => v (t, y))) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem temporalDerivative_eq (v : VelocityField) {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative v t x = derivWithin (fun s => v (s, x)) (Ici 0) t := by
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
  rfl

/-- Time change and amplitude change for a spacetime field. -/
@[expose] def rescale {V : Type*} [SMul ℝ V] (a c : ℝ) (f : SpaceTime → V) : SpaceTime → V :=
  fun z => a • f (c * z.1, z.2)

/-- The force for viscosity `ν`, starting with a force for viscosity one. -/
@[expose] def rescaledForce (ν : ℝ) (f : VelocityField) : VelocityField := rescale (ν ^ 2) ν f

theorem rescale_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f futureDomain)
    (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ContDiffOn ℝ ∞ (rescale a c f) futureDomain := by
  apply (hf.comp ((contDiff_fst.const_smul c).prodMk contDiff_snd).contDiffOn ?_).const_smul a
  intro z hz
  exact ⟨mul_nonneg hc hz.1, mem_univ _⟩

theorem rescale_periodic {V : Type*} [SMul ℝ V] {f : SpaceTime → V}
    (hf : UnitSpatialPeriodsOn (Ici 0) f) (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    UnitSpatialPeriodsOn (Ici 0) (rescale a c f) := by
  intro t ht x i
  exact congrArg (fun y => a • y) (hf (c * t) (mul_nonneg hc ht) x i)

theorem rescale_support {f : VelocityField} (hf : CompactFutureTimeSupport f)
    (a : ℝ) {c : ℝ} (hc : 0 < c) : CompactFutureTimeSupport (rescale a c f) := by
  obtain ⟨T, hT, hz⟩ := hf
  refine ⟨T / c, div_nonneg hT hc.le, ?_⟩
  intro t ht x
  dsimp [rescale]
  rw [hz (c * t) (by nlinarith [(div_le_iff₀ hc).mp ht]) x, smul_zero]

theorem fromComparator_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → ℝ → V} (hf : ContDiffOn ℝ ∞ (↿f) (univ ×ˢ Ici 0)) :
    ContDiffOn ℝ ∞ (fromComparator f) futureDomain := by
  exact hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun z hz => ⟨mem_univ _, hz.1⟩)

theorem toComparator_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f futureDomain) :
    ContDiffOn ℝ ∞ (↿(toComparator f)) (univ ×ˢ Ici 0) := by
  exact hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun z hz => ⟨hz.2, mem_univ _⟩)

theorem toComparator_jet_norm (f : VelocityField) (m : ℕ) (x : Space)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedFDerivWithin ℝ m (↿(toComparator f)) (univ ×ˢ Ici 0) (x, t)‖ =
      ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ := by
  change ‖iteratedFDerivWithin ℝ m (fun z : Space × ℝ => f (z.2, z.1))
    (univ ×ˢ Ici 0) (x, t)‖ = _
  have hs : UniqueDiffOn ℝ futureDomain :=
    (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have he : (LinearIsometryEquiv.prodComm ℝ Space ℝ) ⁻¹' futureDomain = univ ×ˢ Ici 0 := by
    ext z
    simp [futureDomain, and_comm]
  simpa [he, Function.comp_def, Prod.swap] using
    (LinearIsometryEquiv.prodComm ℝ Space ℝ).norm_iteratedFDerivWithin_comp_right f hs
      (x := (x, t)) ⟨ht, mem_univ _⟩ m

/-- All real decay exponents follow from the nonnegative-exponent jet bounds. -/
theorem forceConditionPeriodic_of_decay {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici 0) f)
    (hd : ∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ ≤ C * (1 + t) ^ (-K)) :
    Comparator.ForceConditionPeriodic (toComparator f) := by
  refine ⟨⟨toComparator_smooth hf⟩, ?_, ?_⟩
  · intro t ht x i
    exact hp t ht x i
  · intro m K
    obtain ⟨C, hC, hb⟩ := hd m (max K 0) (le_max_right _ _)
    refine ⟨C, ?_⟩
    intro x t ht
    rw [toComparator_jet_norm f m x ht, div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : 0 ≤ 1 + t)]
    exact (hb t ht x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_left _ _))) hC.le)

theorem zero_initial_condition :
    Comparator.InitialVelocityConditionPeriodic (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨?_, contDiff_const⟩, ?_⟩
  · intro x
    exact Comparator.divergence_const 0 x
  · intro x i
    rfl

theorem rescale_spatialDerivative (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDerivative (rescale a c v) t x = a • spatialDerivative v (c * t) x := by
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) a) x

theorem rescale_divergence (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (rescale a c v) t x = a * spatialDivergence v (c * t) x := by
  simp [spatialDivergence, rescale_spatialDerivative, Finset.mul_sum]

theorem rescale_advection (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    advection (rescale a c v) t x = a ^ 2 • advection v (c * t) x := by
  simp [advection, rescale_spatialDerivative, rescale, smul_smul, pow_two]

theorem rescale_gradient (a c : ℝ) (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (rescale a c p) t x = a • pressureGradient p (c * t) x := by
  unfold pressureGradient rescale
  simp only [← Pi.smul_def, fderiv_const_smul_field]
  simp [smul_smul, Finset.smul_sum]

theorem rescale_laplacian (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (rescale a c v) t x = a • spatialLaplacian v (c * t) x := by
  simp only [spatialLaplacian, rescale_spatialDerivative, smul_apply]
  simp only [← Pi.smul_def, fderiv_const_smul_field]
  simp [Finset.smul_sum]

theorem rescale_temporalDerivative (a c : ℝ) (v : VelocityField) (t : ℝ) (x : Space)
    (hv : DifferentiableAt ℝ (fun s => v (s, x)) (c * t)) :
    temporalDerivative (rescale a c v) t x = (a * c) • temporalDerivative v (c * t) x := by
  have hd := (hv.hasDerivAt.scomp t ((hasDerivAt_id t).const_mul c)).const_smul a
  change deriv (fun s => a • v (c * s, x)) t =
    (a * c) • deriv (fun s => v (s, x)) (c * t)
  simpa only [Function.comp_def, Pi.smul_def, mul_one, smul_smul] using hd.deriv

theorem smooth_space_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : SpaceTime → V} (hv : ContDiffOn ℝ ∞ v futureDomain)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x => v (t, x)) := by
  rw [← contDiffOn_univ]
  exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨ht, mem_univ _⟩)

theorem differentiable_time_slice {v : VelocityField}
    (hv : ContDiffOn ℝ ∞ v futureDomain) {t : ℝ} (ht : 0 < t) (x : Space) :
    DifferentiableAt ℝ (fun s => v (s, x)) t := by
  have h : ContDiffAt ℝ ∞ v (t, x) :=
    hv.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem)
  exact (h.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
    (by simp)

/-- The original project conventions for a global viscosity-one solution. -/
structure GlobalSolutionOne (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ v futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ p futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) v
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) p
  initial_velocity : ∀ x : Space, v (0, x) = 0
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0
  navier_stokes : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v p t x = f (t, x)

/-- Forget periodicity while preserving the global equation and initial data. -/
theorem GlobalSolutionOne.toSolutionOn {f v : VelocityField} {p : PressureField}
    (solution : GlobalSolutionOne f v p) :
    SolutionOn 1 0 (fun _ => 0) (Ici 0) f v p where
  velocity_smooth := solution.velocity_smooth
  pressure_smooth := solution.pressure_smooth
  initial_velocity := solution.initial_velocity
  divergence_free := solution.divergence_free
  navier_stokes := by
    intro time _ positive position
    simpa only [viscousResidual_one] using solution.navier_stokes time positive position

/-- The equation in project coordinates, assuming only the common comparator contract. -/
theorem comparator_equation_core {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothness ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t := by
  have hv := smooth_space_slice (fromComparator_smooth h.velocity_smooth) ht.le
  rw [temporalDerivative_eq _ ht, laplacian_eq _ _ _ (hv.of_le (by
    exact (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)), gradient_eq]
  change derivWithin (v x) (Ici 0) t + fderiv ℝ (v · t) x (v x t) -
    ν • Δ (v · t) x + gradient (p · t) x = f x t
  rw [h.navier_stokes x t ht.le]
  abel

theorem comparator_equation {ν : ℝ} {u₀ : Space → Space} {f v : Space → ℝ → Space}
    {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    temporalDerivative (fromComparator v) t x + advection (fromComparator v) t x -
      ν • spatialLaplacian (fromComparator v) t x +
      pressureGradient (fromComparator p) t x = f x t :=
  comparator_equation_core h.toNavierStokesExistenceAndSmoothness ht x

/-- Residual scaling needs only a nonzero viscosity and differentiability of the
single time slice at the rescaled point; no spatial regularity is assumed. -/
theorem rescale_residual_of_differentiable {ν : ℝ} (hν : ν ≠ 0)
    {v : VelocityField} {p : PressureField} {t : ℝ} {x : Space}
    (hv : DifferentiableAt ℝ (fun s => v (s, x)) (ν⁻¹ * t)) :
    navierStokesResidual (rescale ν⁻¹ ν⁻¹ v) (rescale (ν⁻¹ ^ 2) ν⁻¹ p) t x =
      ν⁻¹ ^ 2 • viscousResidual ν v p (ν⁻¹ * t) x := by
  rw [navierStokesResidual, rescale_temporalDerivative _ _ _ _ _ hv,
    rescale_advection, rescale_laplacian, rescale_gradient, viscousResidual]
  have hcoef : ν⁻¹ * ν⁻¹ * ν = ν⁻¹ := by field_simp
  simp only [smul_add, smul_sub, smul_smul, pow_two, hcoef]

/-- Normalizing time and amplitudes converts the viscosity-`ν` residual to viscosity one. -/
theorem rescale_residual {ν : ℝ} (hν : 0 < ν) {v : VelocityField} {p : PressureField}
    (hv : ContDiffOn ℝ ∞ v futureDomain) {t : ℝ} (ht : 0 < t) (x : Space) :
    navierStokesResidual (rescale ν⁻¹ ν⁻¹ v) (rescale (ν⁻¹ ^ 2) ν⁻¹ p) t x =
      ν⁻¹ ^ 2 • viscousResidual ν v p (ν⁻¹ * t) x :=
  rescale_residual_of_differentiable hν.ne'
    (differentiable_time_slice hv (mul_pos (inv_pos.mpr hν) ht) x)

/-- Normalize the common comparator contract; geometric and energy conditions
can then be transported independently. -/
theorem normalized_solution_core {ν : ℝ} (hν : 0 < ν) {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothness ν (fun _ => 0)
      (toComparator (rescaledForce ν f)) v p) :
    SolutionOn 1 0 (fun _ => 0) (Ici 0) f (rescale ν⁻¹ ν⁻¹ (fromComparator v))
      (rescale (ν⁻¹ ^ 2) ν⁻¹ (fromComparator p)) := by
  have hc : 0 < ν⁻¹ := inv_pos.mpr hν
  have hv := fromComparator_smooth h.velocity_smooth
  have hp := fromComparator_smooth h.pressure_smooth
  refine ⟨rescale_smooth hv _ hc.le, rescale_smooth hp _ hc.le, ?_, ?_, ?_⟩
  · intro x
    simp [rescale, fromComparator, h.initial_condition]
  · intro t ht x
    rw [rescale_divergence, divergence_eq]
    change ν⁻¹ * Comparator.divergence (v · (ν⁻¹ * t)) x = 0
    rw [h.div_free x (ν⁻¹ * t) (mul_nonneg hc.le ht), mul_zero]
  · intro t _ ht x
    rw [viscousResidual_one, rescale_residual hν hv ht x, viscousResidual,
      comparator_equation_core h (mul_pos hc ht) x]
    simp [toComparator, rescaledForce, rescale, smul_smul, hν.ne']

/-- Pull a hypothetical viscosity-`ν` solution back to viscosity one. -/
theorem normalized_solution {ν : ℝ} (hν : 0 < ν) {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν (fun _ => 0)
      (toComparator (rescaledForce ν f)) v p) :
    GlobalSolutionOne f (rescale ν⁻¹ ν⁻¹ (fromComparator v))
      (rescale (ν⁻¹ ^ 2) ν⁻¹ (fromComparator p)) := by
  have core := normalized_solution_core hν h.toNavierStokesExistenceAndSmoothness
  refine ⟨core.velocity_smooth, core.pressure_smooth, ?_, ?_, core.initial_velocity,
    core.divergence_free, ?_⟩
  · exact rescale_periodic (fun t ht x i => h.isOnePeriodic_velocity t ht x i)
      _ (inv_pos.mpr hν).le
  · exact rescale_periodic (fun t ht x i => h.isOnePeriodic_pressure t ht x i)
      _ (inv_pos.mpr hν).le
  · intro t ht x
    simpa only [viscousResidual_one] using core.navier_stokes t ht.le ht x

end NavierStokes.ComparatorBridge
