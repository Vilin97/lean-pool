/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import LeanPool.NavierStokesAndEuler.NavierStokes.SolutionDifference

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Conservative difference equations tested on compactly supported functions

All integrals use Euclidean Lebesgue measure. Compact support is required only
of the test function; the velocities and pressures need no support or decay
assumptions for the identities in this module.
-/

@[expose] public section



noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.ConservativeDifference

open NavierStokes.ProblemStatement
open NavierStokes.SolutionDifference (spatialPartial)
open NavierStokes.SolutionDifference
open Comparison (tensorDiff)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- The ordinary scalar Laplacian, with the same coordinate directions as the
vector Laplacian in the Navier--Stokes residual. -/
def scalarLaplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialPartial i (spatialPartial i f) x

theorem scalarLaplacian_contDiff {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLaplacian f) :=
  ContDiff.sum fun i _ => spatial_partial_contDiff (spatial_partial_contDiff hf i) i

theorem compact_scalarLaplacian {f : Space → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (scalarLaplacian f) := by
  have hh (i : Fin 3) := CompactEnergy.compact_partial
    (CompactEnergy.compact_partial hf i) i
  change HasCompactSupport (fun x => ∑ i : Fin 3, spatialPartial i (spatialPartial i f) x)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using!
    (hh 0).add ((hh 1).add (hh 2))

theorem partial_mul {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y * g y) x =
      f x * spatialPartial i g x + g x * spatialPartial i f x := by
  unfold spatialPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  rfl

theorem partial_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Space → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y - g y) x =
      spatialPartial i f x - spatialPartial i g x := by
  unfold spatialPartial
  rw [fderiv_fun_sub (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  rfl

theorem partial_component {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (i k : Fin 3) (x : Space) :
    spatialPartial i (fun y => f y k) x = spatialPartial i f x k :=
  fderiv_component hf k x (coordinateVector i)

theorem pressureGradient_component (p : PressureField) (t : ℝ)
    (x : Space) (k : Fin 3) :
    pressureGradient p t x k = spatialPartial k (fun y => p (t, y)) x := by
  change (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (∑ i : Fin 3, spatialPartial i (fun y => p (t, y)) x • coordinateVector i) = _
  simp [map_sum, coordinateVector]

theorem spatialLaplacian_component {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    spatialLaplacian u t x k = scalarLaplacian (fun y => u (t, y) k) x := by
  change (EuclideanSpace.proj k : Space →L[ℝ] ℝ)
    (∑ i : Fin 3, spatialPartial i (spatialPartial i (fun y => u (t, y))) x) = _
  rw [map_sum]
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [show spatialPartial i (fun y => u (t, y) k) =
    (fun y => spatialPartial i (fun z => u (t, z)) y k) from
    funext (fun y => partial_component hu i k y)]
  exact (partial_component (spatial_partial_contDiff hu i) i k x).symm

theorem advection_component {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    advection u t x k =
      ∑ i : Fin 3, u (t, x) i * spatialPartial i (fun y => u (t, y) k) x := by
  rw [show advection u t x k =
      fderiv ℝ (fun y => u (t, y) k) x (u (t, x)) from
    (fderiv_component hu k x (u (t, x))).symm]
  exact fderiv_apply_eq_sum _ _ _

/-- Divergence of the velocity outer product, before using incompressibility. -/
theorem outerProduct_divergence {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x))) (x : Space) (k : Fin 3) :
    (∑ i : Fin 3, spatialPartial i (fun y => u (t, y) k * u (t, y) i) x) =
      u (t, x) k * spatialDivergence u t x + advection u t x k := by
  simp_rw [partial_mul (component_contDiff hu k) (component_contDiff hu _)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← advection_component hu]
  simp_rw [partial_component hu]
  rfl

theorem tensorDiff_contDiff {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (i j : Fin 3) :
    ContDiff ℝ ∞ (tensorDiff u v t i j) :=
  ((component_contDiff hu i).mul (component_contDiff hu j)).sub
    ((component_contDiff hv i).mul (component_contDiff hv j))

theorem tensorDiff_divergence {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (x : Space) (k : Fin 3)
    (hdivu : spatialDivergence u t x = 0)
    (hdivv : spatialDivergence v t x = 0) :
    (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) =
      advection u t x k - advection v t x k := by
  unfold tensorDiff
  simp_rw [partial_sub ((component_contDiff hu k).mul (component_contDiff hu _))
    ((component_contDiff hv k).mul (component_contDiff hv _))]
  rw [Finset.sum_sub_distrib, outerProduct_divergence hu,
    outerProduct_divergence hv, hdivu, hdivv]
  simp

/-- The exact conservative equation for a difference of smooth solutions
having the same viscosity-one residual. -/
theorem conservative_difference_equation {u v : VelocityField} {p q : PressureField}
    {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hdivu : spatialDivergence u t x = 0)
    (hdivv : spatialDivergence v t x = 0)
    (hNS : navierStokesResidual u p t x = navierStokesResidual v q t x)
    (k : Fin 3) :
    temporalDerivative (u - v) t x k = spatialLaplacian (u - v) t x k -
      (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) -
      spatialPartial k (fun y => (p - q) (t, y)) x := by
  have heq := congrArg (fun z : Space => z k)
    (difference_equation hu hv hp hq htu htv hNS)
  have hadv := congrArg (fun z : Space => z k) (advection_difference hu hv x)
  simp only [PiLp.sub_apply, PiLp.add_apply] at heq hadv
  rw [pressureGradient_component] at heq
  rw [tensorDiff_divergence hu hv x k hdivu hdivv]
  linarith

/-- Twice integrating by parts transfers a scalar Laplacian to the compact
test function, regardless of growth of the other smooth function. -/
theorem integral_scalarLaplacian_mul {f ψ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ x, scalarLaplacian f x * ψ x) = ∫ x, f x * scalarLaplacian ψ x := by
  have hil (i : Fin 3) :
      Integrable (fun x => spatialPartial i (spatialPartial i f) x * ψ x) :=
    ((spatial_partial_contDiff (spatial_partial_contDiff hf i) i).continuous.mul
      hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hir (i : Fin 3) :
      Integrable (fun x => f x * spatialPartial i (spatialPartial i ψ) x) :=
    (hf.continuous.mul
      (spatial_partial_contDiff (spatial_partial_contDiff hψ i)
          i).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ i) i).mul_left
  simp only [scalarLaplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hil i),
    integral_finsetSum _ (fun i _ => hir i)]
  apply Finset.sum_congr rfl
  intro i _
  have h1 := CompactEnergy.integral_mul_partial hψ (spatial_partial_contDiff hf i) hcψ i
  have h2 := CompactEnergy.integral_mul_partial (spatial_partial_contDiff hψ i) hf
    (CompactEnergy.compact_partial hcψ i) i
  change (∫ x, ψ x * spatialPartial i (spatialPartial i f) x) =
    -(∫ x, spatialPartial i f x * spatialPartial i ψ x) at h1
  change (∫ x, spatialPartial i ψ x * spatialPartial i f x) =
    -(∫ x, f x * spatialPartial i (spatialPartial i ψ) x) at h2
  calc
    _ = ∫ x, ψ x * spatialPartial i (spatialPartial i f) x := by
      exact integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    _ = -(∫ x, spatialPartial i f x * spatialPartial i ψ x) := h1
    _ = -(∫ x, spatialPartial i ψ x * spatialPartial i f x) := by
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    _ = -(-(∫ x, f x * spatialPartial i (spatialPartial i ψ) x)) := congrArg Neg.neg h2
    _ = _ := neg_neg _

theorem integrable_mul_test {f ψ : Space → ℝ} (hf : Continuous f)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) :=
  (hf.mul hψ).integrable_of_hasCompactSupport hcψ.mul_left

theorem integral_tensorDiff_divergence_mul {u v : VelocityField} {t : ℝ}
    {ψ : Space → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) * ψ x) =
      -(∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
  have hi (i : Fin 3) :
      Integrable (fun x => spatialPartial i (tensorDiff u v t k i) x * ψ x) :=
    integrable_mul_test (spatial_partial_contDiff (tensorDiff_contDiff hu hv k i) i).continuous
      hψ.continuous hcψ
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [spatialPartial, mul_comm] using
    CompactEnergy.integral_mul_partial hψ (tensorDiff_contDiff hu hv k i) hcψ i

/-- Testing the conservative equation against a compact scalar test transfers
all spatial derivatives off the velocity difference and tensor difference.
No global integrability assumption is imposed on either pressure. -/
theorem weak_pressure_gradient {u v : VelocityField} {p q : PressureField}
    {t : ℝ} {ψ : Space → ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x) -
      (∫ x, temporalDerivative (u - v) t x k * ψ x) +
      ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x := by
  have hL : Continuous (fun x => spatialLaplacian (u - v) t x k) :=
    (component_contDiff (spatialLaplacian_contDiff (hu.sub hv)) k).continuous
  have hG : Continuous (fun x => ∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) :=
    (ContDiff.sum fun i _ => spatial_partial_contDiff (tensorDiff_contDiff hu hv k i) i).continuous
  have hP : Continuous (spatialPartial k (fun y => (p - q) (t, y))) :=
    (spatial_partial_contDiff (hp.sub hq) k).continuous
  have hdt : Continuous (fun x => temporalDerivative (u - v) t x k) := by
    have heq : (fun x => temporalDerivative (u - v) t x k) =
        (fun x => spatialLaplacian (u - v) t x k -
          (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) -
          spatialPartial k (fun y => (p - q) (t, y)) x) :=
      funext fun x => conservative_difference_equation hu hv hp hq (htu x) (htv x)
        (hdivu x) (hdivv x) (hNS x) k
    rw [heq]
    exact (hL.sub hG).sub hP
  have hiL := integrable_mul_test hL hψ.continuous hcψ
  have hiG := integrable_mul_test hG hψ.continuous hcψ
  have hidt := integrable_mul_test hdt hψ.continuous hcψ
  have hiLD : Integrable (fun x => spatialLaplacian (u - v) t x k * ψ x -
      temporalDerivative (u - v) t x k * ψ x) := hiL.sub hidt
  have hpoint : (fun x => spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (fun x => spatialLaplacian (u - v) t x k * ψ x -
        temporalDerivative (u - v) t x k * ψ x -
        (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) * ψ x) := by
    funext x
    have h := conservative_difference_equation hu hv hp hq (htu x) (htv x)
      (hdivu x) (hdivv x) (hNS x) k
    have hpEq : spatialPartial k (fun y => (p - q) (t, y)) x =
        spatialLaplacian (u - v) t x k - temporalDerivative (u - v) t x k -
        (∑ i : Fin 3, spatialPartial i (tensorDiff u v t k i) x) := by linarith
    rw [hpEq]
    ring
  have hLap : (∫ x, spatialLaplacian (u - v) t x k * ψ x) =
      ∫ x, (u - v) (t, x) k * scalarLaplacian ψ x := by
    simp_rw [spatialLaplacian_component (u := u - v) (t := t) (hu.sub hv)]
    exact integral_scalarLaplacian_mul (component_contDiff (hu.sub hv) k) hψ hcψ
  rw [hpoint, integral_sub hiLD hiG, integral_sub hiL hidt,
    hLap, integral_tensorDiff_divergence_mul hu hv hψ hcψ k]
  ring

/-- A slab version of the compact weak identity with time differentiability
supplied by joint smoothness. -/
theorem weak_pressure_gradient_on_slab {a b t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b))
    (ht : t ∈ Ioo a b)
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x) -
      (∫ x, temporalDerivative (u - v) t x k * ψ x) +
      ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x := by
  exact weak_pressure_gradient (spatial_smooth hu (Ioo_subset_Icc_self ht))
    (spatial_smooth hv (Ioo_subset_Icc_self ht)) (spatial_smooth hp (Ioo_subset_Icc_self ht))
    (spatial_smooth hq (Ioo_subset_Icc_self ht))
    (fun x => time_differentiable_at_interior hu ht x)
    (fun x => time_differentiable_at_interior hv ht x) hdivu hdivv hNS hψ hcψ k

theorem partial_partial_eq_fderiv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (spatialPartial j f) x =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) := by
  have hdf := (hf.fderiv_right infty_add_one_le).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i) = _
  rw [fderiv_clm_apply hdf (differentiableAt_const (coordinateVector j))]
  simp

theorem partial_comm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (spatialPartial j f) x =
      spatialPartial j (spatialPartial i f) x := by
  rw [partial_partial_eq_fderiv hf, partial_partial_eq_fderiv hf]
  exact ((hf.of_le (nat_le_infty 2)).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem partial_sum {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (k : Fin 3) (x : Space) :
    spatialPartial k (fun y => ∑ i : Fin 3, f i y) x =
      ∑ i : Fin 3, spatialPartial k (f i) x := by
  unfold spatialPartial
  rw [fderiv_fun_sum (fun i _ => (hf i).differentiable (by simp) x)]
  simp

theorem partial_scalarLaplacian {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (k : Fin 3) (x : Space) :
    spatialPartial k (scalarLaplacian f) x = scalarLaplacian (spatialPartial k f) x := by
  change spatialPartial k (fun y => ∑ i : Fin 3,
    spatialPartial i (spatialPartial i f) y) x = _
  rw [partial_sum (f := fun i => spatialPartial i (spatialPartial i f))
    (fun i => spatial_partial_contDiff (spatial_partial_contDiff hf i) i)]
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [partial_comm (f := spatialPartial i f) (spatial_partial_contDiff hf i) k i x]
  exact congrArg (fun g : Space → ℝ => spatialPartial i g x)
    (funext (fun y => partial_comm hf k i y))

/-- A compact scalar test detects the ordinary divergence, even when the
vector field has no compact support. -/
theorem integral_divergence_free_test {w : Space → Space} {ψ : Space → ℝ}
    (hw : ContDiff ℝ ∞ w) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i w x i) = 0) :
    (∑ i : Fin 3, ∫ x, w x i * spatialPartial i ψ x) = 0 := by
  have hi (i : Fin 3) : Integrable (fun x => ψ x * spatialPartial i w x i) :=
    (hψ.continuous.mul
      (component_contDiff (spatial_partial_contDiff hw i)
          i).continuous).integrable_of_hasCompactSupport
      hcψ.mul_right
  have hparts (i : Fin 3) : (∫ x, w x i * spatialPartial i ψ x) =
      -(∫ x, ψ x * spatialPartial i w x i) := by
    have h := CompactEnergy.integral_mul_partial hψ (component_contDiff hw i) hcψ i
    simp_rw [partial_component hw] at h
    linarith
  rw [Finset.sum_congr rfl (fun i _ => hparts i), Finset.sum_neg_distrib]
  have hsum : (∫ x, ψ x * ∑ i : Fin 3, spatialPartial i w x i) =
      ∑ i : Fin 3, ∫ x, ψ x * spatialPartial i w x i := by
    simp only [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hi i)
  rw [← hsum]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

/-- Differentiation of one component paired with a fixed compact spatial
test. The compact support supplies a common spatial domain for differentiation. -/
theorem component_test_hasDerivAt {a b t : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    HasDerivAt (fun s => ∫ x, w (s, x) k * ψ x)
      (∫ x, temporalDerivative w t x k * ψ x) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => w z k * ψ z.2)
      (Icc a b ×ˢ univ) :=
    (((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hw).mul
      (hψ.comp contDiff_snd).contDiffOn).of_le (nat_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt
    hcψ hF ?_ ht ?_
  · intro s hs x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  · intro x
    have htime : HasDerivAt (fun s => w (s, x)) (temporalDerivative w t x) t :=
      (time_differentiable_at_interior hw ht x).hasDerivAt
    exact ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t htime).mul_const
        (ψ x)

/-- The time derivative has zero distributional divergence. This follows by
differentiating a compact pairing that is identically zero on the time interval. -/
theorem integral_time_derivative_divergence_free {a b t : ℝ} {w : VelocityField}
    {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hdiv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence w s x = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ x, temporalDerivative w t x k * spatialPartial k ψ x) = 0 := by
  have hderiv : HasDerivAt
      (fun s => ∑ k : Fin 3, ∫ x, w (s, x) k * spatialPartial k ψ x)
      (∑ k : Fin 3, ∫ x, temporalDerivative w t x k * spatialPartial k ψ x) t :=
    HasDerivAt.fun_sum fun k _ => component_test_hasDerivAt hw ht
      (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) k
  have heq : (fun s => ∑ k : Fin 3, ∫ x, w (s, x) k * spatialPartial k ψ x) =ᶠ[𝓝 t]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact integral_divergence_free_test (spatial_smooth hw (Ioo_subset_Icc_self hs))
      hψ hcψ (hdiv s hs)
  exact (hderiv.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t (0 : ℝ))

theorem integral_gradient_pairing {f ψ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∑ k : Fin 3, ∫ x, spatialPartial k f x * spatialPartial k ψ x) =
      -(∫ x, f x * scalarLaplacian ψ x) := by
  have hparts (k : Fin 3) :
      (∫ x, spatialPartial k f x * spatialPartial k ψ x) =
        -(∫ x, f x * spatialPartial k (spatialPartial k ψ) x) := by
    have h := CompactEnergy.integral_mul_partial (spatial_partial_contDiff hψ k) hf
      (CompactEnergy.compact_partial hcψ k) k
    change (∫ x, spatialPartial k ψ x * spatialPartial k f x) =
      -(∫ x, f x * spatialPartial k (spatialPartial k ψ) x) at h
    calc
      _ = ∫ x, spatialPartial k ψ x * spatialPartial k f x :=
        integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
      _ = _ := h
  have hi (k : Fin 3) :
      Integrable (fun x => f x * spatialPartial k (spatialPartial k ψ) x) :=
    integrable_mul_test hf.continuous
      (spatial_partial_contDiff (spatial_partial_contDiff hψ k) k).continuous
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) k)
  rw [Finset.sum_congr rfl (fun k _ => hparts k), Finset.sum_neg_distrib]
  congr 1
  simp only [scalarLaplacian, Finset.mul_sum]
  exact (integral_finsetSum _ (fun k _ => hi k)).symm

/-- The pressure difference solves the compact-test Poisson equation obtained
from the actual Navier--Stokes residual and incompressibility. No pressure
normalization, growth hypothesis, or integrability at infinity is used. -/
theorem weak_pressure_poisson {a b t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b))
    (ht : t ∈ Ioo a b)
    (hdivu : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, (p - q) (t, x) * scalarLaplacian ψ x) =
      -(∑ k : Fin 3, ∑ i : Fin 3,
        ∫ x, tensorDiff u v t k i x * spatialPartial i (spatialPartial k ψ) x) := by
  have hw : ContDiffOn ℝ ∞ (u - v) (Comparison.slab a b) := hu.sub hv
  have hwspace := spatial_smooth hw (Ioo_subset_Icc_self ht)
  have hdivw : ∀ s ∈ Ioo a b, ∀ x, spatialDivergence (u - v) s x = 0 := by
    intro s hs x
    rw [spatialDivergence_sub (spatial_smooth hu (Ioo_subset_Icc_self hs))
      (spatial_smooth hv (Ioo_subset_Icc_self hs)), hdivu s hs, hdivv s hs, sub_self]
  have hL : (∑ k : Fin 3, ∫ x, (u - v) (t, x) k *
      scalarLaplacian (spatialPartial k ψ) x) = 0 := by
    simp_rw [← partial_scalarLaplacian hψ]
    exact integral_divergence_free_test hwspace (scalarLaplacian_contDiff hψ)
      (compact_scalarLaplacian hcψ) (hdivw t ht)
  have hT := integral_time_derivative_divergence_free hw ht hdivw hψ hcψ
  have hsum : (∑ k : Fin 3, ∫ x,
      spatialPartial k (fun y => (p - q) (t, y)) x * spatialPartial k ψ x) =
      ∑ k : Fin 3, ((∫ x, (u - v) (t, x) k * scalarLaplacian (spatialPartial k ψ) x) -
        (∫ x, temporalDerivative (u - v) t x k * spatialPartial k ψ x) +
        ∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i (spatialPartial k ψ) x) := by
    apply Finset.sum_congr rfl
    intro k _
    exact weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht) hNS
      (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) k
  rw [integral_gradient_pairing (f := fun y => (p - q) (t, y))
      ((spatial_smooth hp (Ioo_subset_Icc_self ht)).sub (spatial_smooth hq (Ioo_subset_Icc_self
          ht)))
      hψ hcψ, Finset.sum_add_distrib, Finset.sum_sub_distrib, hL, hT] at hsum
  linarith

end NavierStokesR3.ConservativeDifference
