/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFiniteEnergy
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFlux
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
import Mathlib.MeasureTheory.Function.L2Space
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedInterpolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicIntegration
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy

/-!
# Whole-space finite-energy comparison

The reference velocity has one compact spatial support throughout the closed
time interval. The competing velocity has only smoothness and a uniform
finite-energy bound. No growth, decay, support or derivative bound is assumed
for the competing pressure or velocity. The pressure flux estimate is derived
from the actual equation by the imported pressure recovery and commutator
theorems.
-/

section

/-!
# Closing the whole-space comparison estimate

This module isolates the final PDE energy calculation. Its explicit pressure
flux hypothesis is discharged by the pressure reconstruction modules in the
whole-space uniqueness theorem; it is not a competitor hypothesis.
-/

section

/-!
# The compactly weighted difference-energy identity on R³

The cutoff alone has compact support. Both velocities and both pressures may
be arbitrary smooth fields on the time slab. Every integral below is an
ordinary Lebesgue volume integral on Euclidean three-space.
-/

section

/-!
# The Laplacian in a compactly weighted energy identity

All integrals are ordinary volume integrals on Euclidean three-space. The
weight is smooth and compactly supported; the vector field is smooth but is
not required to have compact support or globally integrable derivatives.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private theorem laplacian_nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem laplacian_partial_smul {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => χ y • w y) x =
      χ x • spatialPartial i w x + spatialPartial i χ x • w x := by
  unfold spatialPartial
  rw [fderiv_fun_smul (hχ.differentiable (by simp) x)
    (hw.differentiable (by simp) x)]
  rfl

theorem laplacian_integrable_weighted_partial_sq {χ : Space → ℝ} {w : Space → Space}
    (hχ : Continuous χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    Integrable (fun x => χ x * ‖spatialPartial i w x‖ ^ 2) :=
  (hχ.mul ((spatial_partial_contDiff hw i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
    hcχ.mul_right

theorem laplacian_integrable_weighted_gradient_sq {χ : Space → ℝ} {w : Space → Space}
    (hχ : Continuous χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => χ x * ∑ i : Fin 3, ‖spatialPartial i w x‖ ^ 2) := by
  have hsum : (fun x => χ x * ∑ i : Fin 3, ‖spatialPartial i w x‖ ^ 2) =
      (fun x => ∑ i : Fin 3, χ x * ‖spatialPartial i w x‖ ^ 2) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [hsum]
  exact integrable_finsetSum _ (fun i _ =>
    laplacian_integrable_weighted_partial_sq hχ hw hcχ i)

theorem laplacian_integrable_cutoff_second_partial {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : Continuous w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    Integrable (fun x => ‖w x‖ ^ 2 * spatialPartial i (spatialPartial i χ) x) :=
  ((hw.norm.pow 2).mul
    (spatial_partial_contDiff (spatial_partial_contDiff hχ i)
        i).continuous).integrable_of_hasCompactSupport
    (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcχ i) i).mul_left

theorem laplacian_integrable_cutoff_laplacian {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : Continuous w) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => ‖w x‖ ^ 2 *
      ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) := by
  have hsum : (fun x => ‖w x‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) =
      (fun x => ∑ i : Fin 3, ‖w x‖ ^ 2 * spatialPartial i (spatialPartial i χ) x) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [hsum]
  exact integrable_finsetSum _ (fun i _ =>
    laplacian_integrable_cutoff_second_partial hχ hw hcχ i)

theorem laplacian_integrable_weighted_laplacian {χ : Space → ℝ} {w : Space → Space}
    (hχ : Continuous χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => χ x *
      ⟪w x, ∑ i : Fin 3, spatialPartial i (spatialPartial i w) x⟫_ℝ) := by
  have hsum : Continuous (fun x =>
      ∑ i : Fin 3, spatialPartial i (spatialPartial i w) x) :=
    continuous_finsetSum _ (fun i _ =>
      (spatial_partial_contDiff (spatial_partial_contDiff hw i) i).continuous)
  exact (hχ.mul (hw.continuous.inner hsum)).integrable_of_hasCompactSupport hcχ.mul_right

/-- The one-coordinate weighted integration-by-parts identity. -/
theorem integral_weighted_second_partial {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (i : Fin 3) :
    (∫ x, χ x * ⟪w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) =
      -(∫ x, χ x * ‖spatialPartial i w x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 * spatialPartial i (spatialPartial i χ) x := by
  have hdw : ContDiff ℝ ∞ (spatialPartial i w) := spatial_partial_contDiff hw i
  have hdχ : ContDiff ℝ ∞ (spatialPartial i χ) := spatial_partial_contDiff hχ i
  have hi_cross : Integrable (fun x =>
      spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ) :=
    (hdχ.continuous.mul (hw.continuous.inner hdw.continuous)).integrable_of_hasCompactSupport
      (CompactEnergy.compact_partial hcχ i).mul_right
  have hi_grad := laplacian_integrable_weighted_partial_sq hχ.continuous hw hcχ i
  have hfirst := CompactEnergy.integral_inner_partial (hχ.smul hw) hdw hcχ.smul_right i
  have hfirst_rhs : (fun x =>
      ⟪spatialPartial i (fun y => χ y • w y) x, spatialPartial i w x⟫_ℝ) =
      (fun x => χ x * ‖spatialPartial i w x‖ ^ 2 +
        spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ) := by
    funext x
    rw [laplacian_partial_smul hχ hw i x, inner_add_left]
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq]
  change (∫ x, ⟪χ x • w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) = -(∫ x, ⟪spatialPartial i
      (fun y => χ y • w y) x, spatialPartial i w x⟫_ℝ) at hfirst
  simp only [real_inner_smul_left] at hfirst
  rw [hfirst_rhs, integral_add hi_grad hi_cross] at hfirst
  have hsecond := CompactEnergy.integral_mul_partial hdχ (hw.norm_sq ℝ)
    (CompactEnergy.compact_partial hcχ i) i
  have hsecond_lhs : (fun x =>
      spatialPartial i χ x * spatialPartial i (fun y => ‖w y‖ ^ 2) x) =
      (fun x => 2 * (spatialPartial i χ x * ⟪w x, spatialPartial i w x⟫_ℝ)) := by
    funext x
    change spatialPartial i χ x * fderiv ℝ (fun y => ‖w y‖ ^ 2) x (coordinateVector i) = _
    rw [fderiv_normsq hw]
    dsimp only [spatialPartial]
    ring
  rw [hsecond_lhs, integral_const_mul] at hsecond
  linarith

/-- Compactly weighted Laplacian energy identity for an arbitrary smooth
spatial vector field. No global integrability assumption on the vector field
or its derivatives is needed. -/
theorem integral_weighted_laplacian {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ) :
    (∫ x, χ x * ⟪w x, ∑ i : Fin 3, spatialPartial i (spatialPartial i w) x⟫_ℝ) =
      -(∫ x, χ x * ∑ i : Fin 3, ‖spatialPartial i w x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x := by
  have hi_left (i : Fin 3) : Integrable (fun x =>
      χ x * ⟪w x, spatialPartial i (spatialPartial i w) x⟫_ℝ) :=
    (hχ.continuous.mul (hw.continuous.inner
      (spatial_partial_contDiff (spatial_partial_contDiff hw i)
          i).continuous)).integrable_of_hasCompactSupport
      hcχ.mul_right
  simp only [inner_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi_left i),
    integral_finsetSum _ (fun i _ => laplacian_integrable_weighted_partial_sq hχ.continuous hw hcχ
        i),
    integral_finsetSum _ (fun i _ => laplacian_integrable_cutoff_second_partial hχ hw.continuous
        hcχ i)]
  simp_rw [integral_weighted_second_partial hχ hw hcχ]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The same identity in the velocity-field notation used by Navier--Stokes. -/
theorem integral_weighted_spatialLaplacian {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ (fun x => w (t, x)))
    (hcχ : HasCompactSupport χ) :
    (∫ x, χ x * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∫ x, χ x * ∑ i : Fin 3, ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2) +
        (1 / 2 : ℝ) * ∫ x, ‖w (t, x)‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x := by
  exact integral_weighted_laplacian hχ hw hcχ

end NavierStokesR3.LocalizedDifferenceEnergy

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (weightedEnergy weightedEnergyRate weightedDissipation gradientSq)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- A continuous factor needs no decay when multiplied by the compact cutoff. -/
theorem integrable_cutoff_mul {χ f : Space → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hf : Continuous f) :
    Integrable (fun x => χ x * f x) :=
  (hχ.mul hf).integrable_of_hasCompactSupport hcχ.mul_right

theorem integrable_weighted_energy {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : Continuous (fun x : Space => w (t, x))) :
    Integrable (fun x : Space => χ x * ‖w (t, x)‖ ^ 2) :=
  integrable_cutoff_mul hχ hcχ (hw.norm.pow 2)

theorem integrable_weighted_dissipation {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x))) :
    Integrable (fun x : Space => χ x * gradientSq (fun y => w (t, y)) x) := by
  apply integrable_cutoff_mul hχ hcχ
  exact continuous_finsetSum _ (fun i _ => (spatial_partial_contDiff hw i).continuous.norm.pow 2)

theorem weightedEnergy_nonneg {χ : Space → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    (w : VelocityField) (t : ℝ) : 0 ≤ weightedEnergy χ w t :=
  integral_nonneg (fun x => mul_nonneg (hχ x) (sq_nonneg _))

theorem weightedDissipation_nonneg {χ : Space → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    (w : VelocityField) (t : ℝ) : 0 ≤ weightedDissipation χ w t :=
  integral_nonneg (fun x => mul_nonneg (hχ x)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Energy is continuous on the closed slab, including its initial time. -/
theorem weightedEnergy_continuousOn {a b : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) :
    ContinuousOn (weightedEnergy χ w) (Icc a b) := by
  have hF : ContinuousOn (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (hχ.comp continuous_snd).continuousOn.mul (hw.continuousOn.norm.pow 2)
  apply CompactTimeIntegral.continuousOn_integral hcχ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Joint smoothness and the cutoff justify differentiation under the integral. -/
theorem weightedEnergy_hasDerivAt {a b t : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    HasDerivAt (weightedEnergy χ w) (weightedEnergyRate χ w t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (((hχ.comp contDiff_snd).contDiffOn).mul (hw.norm_sq ℝ)).of_le (nat_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt hcχ hF ?_ ht ?_
  · intro r hr x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro x
    exact (energy_density_derivative (time_differentiable_at_interior hw ht x)).const_mul (χ x)

/-- The weighted energy integrand remains integrable after time differentiation. -/
theorem integrable_weighted_energy_rate {a b t : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    Integrable (fun x : Space => χ x * (2 * ⟪w (t, x), temporalDerivative w t x⟫_ℝ)) := by
  have htime : ContinuousOn
      (fun z : SpaceTime => deriv (fun r => w (r, z.2)) z.1) (Ioo a b ×ˢ univ) :=
    CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn (hw.of_le (nat_le_infty 1))
  have htime' : Continuous (temporalDerivative w t) := by
    simpa only [temporalDerivative, deriv] using! CompactTimeIntegral.continuous_slice htime ht
  exact integrable_cutoff_mul hχ hcχ
    (continuous_const.mul ((spatial_smooth hw (Ioo_subset_Icc_self ht)).continuous.inner htime'))

/-- The localized balance follows from equality of the actual Navier--Stokes
residuals. No integrability or support condition is imposed on either velocity. -/
theorem difference_energy_balance {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x : Space, DifferentiableAt ℝ (fun r => u (r, x)) t)
    (htv : ∀ x : Space, DifferentiableAt ℝ (fun r => v (r, x)) t)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hNS : ∀ x : Space, ProblemStatement.navierStokesResidual 1 u p t x =
      ProblemStatement.navierStokesResidual 1 v q t x) :
    (1 / 2 : ℝ) * weightedEnergyRate χ (u - v) t + weightedDissipation χ (u - v) t =
      -(∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) +
      ∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x)) := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hπ : ContDiff ℝ ∞ (fun x : Space => (p - q) (t, x)) := hp.sub hq
  have hdivw : ∀ x : Space, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdivu x, hdivv x, sub_self]
  have hiL : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hiC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hw)).continuous
  have hiT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hw.fderiv_right infty_add_one_le).clm_apply hv)).continuous
  have hiP : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (pressureGradient_contDiff hπ)).continuous
  have hiLC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    hiL.sub hiC
  have hiLCT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    hiLC.sub hiT
  have hEq : (fun x : Space => χ x *
      (2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)) =
      (fun x : Space => 2 * (
        χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ)) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (by simpa using hNS x)]
    simp only [inner_sub_right]
    ring
  have hRate : weightedEnergyRate χ (u - v) t = 2 * (
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) -
      ∫ x : Space, χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    unfold weightedEnergyRate
    rw [hEq, integral_const_mul, integral_sub hiLCT hiP,
      integral_sub hiLC hiT, integral_sub hiL hiC]
  have hL := integral_weighted_spatialLaplacian hχ hw hcχ
  have hT := integral_weighted_transport hχ hw hv hcχ hdivv
  have hP : (∫ x : Space, χ x *
      ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) =
      -(∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) := by
    simp_rw [inner_pressureGradient]
    exact integral_weighted_pressure hχ hπ hw hcχ hdivw
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) =
      -weightedDissipation χ (u - v) t +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) at hL
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) =
      -(1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) at hT
  rw [hL, hT, hP] at hRate
  rw [hRate]
  ring

/-- The balance with its time derivative justified on the interior of a closed
slab. The only support hypothesis is on the scalar cutoff. -/
theorem hasDerivAt_difference_energy_balance {a b t : ℝ} {χ : Space → ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab a b))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab a b))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab a b))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab a b)) (ht : t ∈ Ioo a b)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hNS : ∀ x : Space, ProblemStatement.navierStokesResidual 1 u p t x =
      ProblemStatement.navierStokesResidual 1 v q t x) :
    HasDerivAt (weightedEnergy χ (u - v))
      (-2 * weightedDissipation χ (u - v) t -
        2 * (∫ x : Space, χ x *
          ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
        (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
        (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ χ x (v (t, x))) +
        2 * ∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) t := by
  have hd : HasDerivAt (weightedEnergy χ (u - v))
      (weightedEnergyRate χ (u - v) t) t :=
    weightedEnergy_hasDerivAt hχ hcχ (hu.sub hv) ht
  have hb := difference_energy_balance hχ hcχ
    (spatial_smooth hu (Ioo_subset_Icc_self ht)) (spatial_smooth hv (Ioo_subset_Icc_self ht))
    (spatial_smooth hp (Ioo_subset_Icc_self ht)) (spatial_smooth hq (Ioo_subset_Icc_self ht))
    (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
    hdivu hdivv hNS
  convert! hd using 1
  linarith

end NavierStokesR3.LocalizedDifferenceEnergy

end
end

end

section

/-!
# A uniform rate bound from the localized energy estimate

The Sobolev estimate for the cutoff velocity contains fixed multiplicative
constants. They are absorbed into a single coefficient before applying the
uniform Young estimate. The resulting error decays as `1 / R`, and no sign
condition on the energy coefficient or energy value is used.
-/

section

/-!
# Scalar absorption for the whole-space comparison estimate

The constants in these estimates are uniform in the cutoff radius and in the
nonnegative quantity that will represent a weighted gradient norm. All
fractional powers have real exponents.
-/

@[expose] public section

noncomputable section

open Filter

namespace NavierStokesR3.ComparisonYoung

/-- Every nonnegative subquadratic power can be absorbed into an arbitrarily
small multiple of the square, with a constant independent of the argument. -/
theorem exists_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * A ^ p ≤ δ * A ^ 2 + D := by
  have hevent : ∀ᶠ A : ℝ in atTop, C / δ ≤ A ^ (2 - p) :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 - p)).eventually
      (eventually_ge_atTop (C / δ))
  obtain ⟨b, hb⟩ := eventually_atTop.mp hevent
  let K : ℝ := max 1 b
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hD : 0 ≤ C * K ^ p := mul_nonneg hC (Real.rpow_nonneg hK _)
  refine ⟨C * K ^ p, hD, ?_⟩
  intro A hA
  by_cases hAK : A ≤ K
  · calc
      C * A ^ p ≤ C * K ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA hAK hp0) hC
      _ ≤ δ * A ^ 2 + C * K ^ p :=
        le_add_of_nonneg_left (mul_nonneg hδ.le (sq_nonneg A))
  · have hKA : K ≤ A := le_of_lt (lt_of_not_ge hAK)
    have hApos : 0 < A := lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 b).trans hKA)
    have hlarge : C ≤ A ^ (2 - p) * δ :=
      (div_le_iff₀ hδ).mp (hb A ((le_max_right 1 b).trans hKA))
    have hpow : A ^ (2 - p) * A ^ p = A ^ 2 := by
      rw [← Real.rpow_add hApos]
      norm_num
    calc
      C * A ^ p ≤ (A ^ (2 - p) * δ) * A ^ p :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hA _)
      _ = δ * (A ^ (2 - p) * A ^ p) := by ring
      _ = δ * A ^ 2 := by rw [hpow]
      _ ≤ δ * A ^ 2 + C * K ^ p := le_add_of_nonneg_right hD

/-- The same absorption estimate is uniform for a fixed unit shift. -/
theorem exists_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, C * (A + 1) ^ p ≤ δ * A ^ 2 + D := by
  obtain ⟨D, hD, hbound⟩ := exists_rpow_absorption hC (half_pos hδ) hp0 hp2
  refine ⟨D + δ, add_nonneg hD hδ.le, ?_⟩
  intro A hA
  have hboundA := hbound (A + 1) (by linarith)
  have hsquare : (A + 1) ^ 2 ≤ 2 * A ^ 2 + 2 := by
    linarith [sq_nonneg (A - 1)]
  have hscaled := mul_le_mul_of_nonneg_left hsquare (half_pos hδ).le
  linarith

/-- Dividing the shifted estimate by a radius at least one preserves the
arbitrarily small square coefficient and makes the constant decay as `1 / R`. -/
theorem exists_scaled_shifted_rpow_absorption {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hp0 : 0 ≤ p) (hp2 : p < 2) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C / R * (A + 1) ^ p ≤ δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_shifted_rpow_absorption hC hδ hp0 hp2
  refine ⟨D, hD, ?_⟩
  intro A hA R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hscaled := mul_le_mul_of_nonneg_right (hbound A hA) hInv
  have hquadratic := mul_le_mul_of_nonneg_left hInv1
    (mul_nonneg hδ.le (sq_nonneg A))
  simp only [div_eq_mul_inv]
  linarith

/-- The pressure and transport cutoff remainders are controlled by one shifted
subquadratic power. The estimate retains the full factor `1 / R`. -/
theorem cutoff_expression_le {C A R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
        (R⁻¹ * A + R ^ (-2 : ℝ)) +
      C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
      C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
        4 * C / R * (A + 1) ^ (3 / 2 : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hInv1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hx : 0 ≤ A + R⁻¹ := add_nonneg hA hInv
  have hxB : A + R⁻¹ ≤ A + 1 := add_le_add_right hInv1 A
  have hB1 : 1 ≤ A + 1 := by linarith
  have hBpos : 0 < A + 1 := by linarith
  have hR2 : R ^ (-2 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-2 : ℝ) ≤ -1))
  have hR74 : R ^ (-7 / 4 : ℝ) ≤ R⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (-7 / 4 : ℝ) ≤ -1))
  have hhalf : (A + R⁻¹) ^ (1 / 2 : ℝ) + 1 ≤
      2 * (A + 1) ^ (1 / 2 : ℝ) := by
    have hmon := Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hone := Real.one_le_rpow hB1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hlinear : R⁻¹ * A + R ^ (-2 : ℝ) ≤ R⁻¹ * (A + 1) := by
    linarith
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hprod : (A + 1) ^ (1 / 2 : ℝ) * (A + 1) =
      (A + 1) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hBpos.ne']
    norm_num
  have hfactor : ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
      (R⁻¹ * A + R ^ (-2 : ℝ)) ≤ 2 * R⁻¹ * (A + 1) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (A + 1) ^ (1 / 2 : ℝ)) * (R⁻¹ * (A + 1)) :=
        mul_le_mul hhalf hlinear hlinear0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hBpos.le _))
      _ = 2 * R⁻¹ * ((A + 1) ^ (1 / 2 : ℝ) * (A + 1)) := by ring
      _ = _ := by rw [hprod]
  have hthreeQuarters : (A + R⁻¹) ^ (3 / 4 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    (Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 4)).trans
      (Real.rpow_le_rpow_of_exponent_le hB1
        (by norm_num : (3 / 4 : ℝ) ≤ 3 / 2))
  have hthreeHalves : (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
      (A + 1) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hx hxB (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hterm1 := mul_le_mul_of_nonneg_left hfactor hC
  have hterm2 := mul_le_mul_of_nonneg_left
    (mul_le_mul hR74 hthreeQuarters (Real.rpow_nonneg hx _) hInv) hC
  have hterm3 := mul_le_mul_of_nonneg_left hthreeHalves (mul_nonneg hC hInv)
  simp only [div_eq_mul_inv]
  linarith only [hterm1, hterm2, hterm3]

/-- Scalar Young absorption of all cutoff remainders. The same nonnegative
constant works for every nonnegative gradient norm and every radius at least
one. -/
theorem exists_cutoff_absorption {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ A ≥ 0, ∀ R ≥ 1,
      C * ((A + R⁻¹) ^ (1 / 2 : ℝ) + 1) *
          (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * (A + R⁻¹) ^ (3 / 4 : ℝ) +
        C * R⁻¹ * (A + R⁻¹) ^ (3 / 2 : ℝ) ≤
          δ * A ^ 2 + D / R := by
  obtain ⟨D, hD, hbound⟩ := exists_scaled_shifted_rpow_absorption
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) hδ
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)
  exact ⟨D, hD, fun A hA R hR =>
    (cutoff_expression_le hC hA hR).trans (hbound A hA R hR)⟩

end NavierStokesR3.ComparisonYoung

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokesR3.ComparisonRateBound

private theorem rpow_le_square_mul_rpow {B Q x p : ℝ}
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hQ : 1 ≤ Q) (hBQ : B ≤ Q * x)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    B ^ p ≤ Q ^ 2 * x ^ p := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  calc
    B ^ p ≤ (Q * x) ^ p := Real.rpow_le_rpow hB hBQ hp0
    _ = Q ^ p * x ^ p := Real.mul_rpow hQ0 hx
    _ ≤ Q ^ (2 : ℝ) * x ^ p := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hQ hp2) (Real.rpow_nonneg hx _)
    _ = Q ^ 2 * x ^ p := by rw [Real.rpow_two]

/-- Fixed constants in the cutoff Sobolev estimate preserve uniform absorption
of the full pressure and transport error. -/
theorem exists_uniform_flux_absorption {C1 C2 S M δ : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      C1 / R * B ^ (3 / 2 : ℝ) +
        C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
          R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤ δ * A ^ 2 + D / R := by
  let Q : ℝ := max 1 (S * max 1 M)
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hSQ : S ≤ Q := by
    calc
      S = S * 1 := by ring
      _ ≤ S * max 1 M := mul_le_mul_of_nonneg_left (le_max_left _ _) hS
      _ ≤ Q := le_max_right _ _
  have hSMQ : S * M ≤ Q :=
    (mul_le_mul_of_nonneg_left (le_max_right 1 M) hS).trans (le_max_right _ _)
  have hQ0 : 0 ≤ Q := (mul_nonneg hS hM).trans hSMQ
  have hQsq1 : 1 ≤ Q ^ 2 := by linarith [sq_nonneg (Q - 1)]
  let C : ℝ := (C1 + C2) * Q ^ 2
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hC1 hC2) (sq_nonneg _)
  have hC1Q : C1 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) (sq_nonneg _)
  have hC2Q : C2 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) (sq_nonneg _)
  obtain ⟨D, hD, hD_bound⟩ := ComparisonYoung.exists_cutoff_absorption hC hδ
  refine ⟨D, hD, ?_⟩
  intro R hR A hA B hB hSobolev
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  let x : ℝ := A + R⁻¹
  have hx : 0 ≤ x := add_nonneg hA hInv
  have hBQ : B ≤ Q * x := by
    calc
      B ≤ S * (A + M / R) := hSobolev
      _ = S * A + (S * M) * R⁻¹ := by ring
      _ ≤ Q * A + Q * R⁻¹ := add_le_add
        (mul_le_mul_of_nonneg_right hSQ hA)
        (mul_le_mul_of_nonneg_right hSMQ hInv)
      _ = Q * x := by dsimp [x]; ring
  have hhalf : B ^ (1 / 2 : ℝ) ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hthree : B ^ (3 / 2 : ℝ) ≤ Q ^ 2 * x ^ (3 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hquarter : B ^ (3 / 4 : ℝ) ≤ Q ^ 2 * x ^ (3 / 4 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hhalfOne : B ^ (1 / 2 : ℝ) + 1 ≤ Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) + Q ^ 2 := add_le_add hhalf hQsq1
      _ = _ := by ring
  have hfactor : C2 * (B ^ (1 / 2 : ℝ) + 1) ≤ C * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ C2 * (Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hhalfOne hC2
      _ = (C2 * Q ^ 2) * (x ^ (1 / 2 : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2Q (by positivity)
  have hRminus2 : R ^ (-2 : ℝ) = 1 / R ^ 2 := by
    rw [Real.rpow_neg hRpos.le, Real.rpow_two, one_div]
  have hlinear : A / R + 1 / R ^ 2 = R⁻¹ * A + R ^ (-2 : ℝ) := by
    rw [hRminus2]
    ring
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hpressure : C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) := by
    rw [hlinear, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfactor hlinear0
  have hcommutator : C2 * (R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
    calc
      _ = (C2 * R ^ (-7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := by ring
      _ ≤ (C2 * R ^ (-7 / 4 : ℝ)) * (Q ^ 2 * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hquarter (mul_nonneg hC2 (Real.rpow_nonneg hRpos.le _))
      _ = (C2 * Q ^ 2) * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) := by ring
      _ ≤ C * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC2Q (by positivity)
      _ = _ := by ring
  have htransport : C1 / R * B ^ (3 / 2 : ℝ) ≤
      C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ C1 / R * (Q ^ 2 * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hthree (div_nonneg hC1 hRpos.le)
      _ = (C1 * Q ^ 2) * (R⁻¹ * x ^ (3 / 2 : ℝ)) := by ring
      _ ≤ C * (R⁻¹ * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC1Q (by positivity)
      _ = _ := by ring
  have hsum : C1 / R * B ^ (3 / 2 : ℝ) +
      C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) +
        C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    linarith only [hpressure, hcommutator, htransport]
  exact hsum.trans (hD_bound A hA R hR)

/-- One radius-independent constant turns the full localized energy inequality
into the differential inequality required by Gronwall. -/
theorem exists_uniform_rate_bound {C0 C1 C2 S M : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      ∀ E E' G : ℝ,
        (1 / 2 : ℝ) * E' + A ^ 2 ≤ G * E + C0 / R ^ 2 +
          C1 / R * B ^ (3 / 2 : ℝ) +
          C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
            R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) →
        E' ≤ 2 * G * E + D / R := by
  obtain ⟨D, hD, hflux⟩ := exists_uniform_flux_absorption hC1 hC2 hS hM
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨2 * (C0 + D), by positivity, ?_⟩
  intro R hR A hA B hB hSobolev E E' G henergy
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRsq : R ≤ R ^ 2 := by linarith [sq_nonneg (R - 1)]
  have hC0radius : C0 / R ^ 2 ≤ C0 / R :=
    div_le_div_of_nonneg_left hC0 hRpos hRsq
  have hbound := hflux R hR A hA B hB hSobolev
  have hdivide : 2 * (C0 + D) / R = 2 * (C0 / R + D / R) := by ring
  rw [hdivide]
  linarith only [henergy, hbound, hC0radius, sq_nonneg A]

end NavierStokesR3.ComparisonRateBound

end
end

end

section

/-!
# Non-pressure terms in the localized difference energy balance

The velocity difference need not have compact support or globally integrable
derivatives. The compact cutoff supplies local integrability; the estimates
use its weighted `L⁶` norm and the unweighted `L²` norm of the difference.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace

namespace NavierStokesR3.LocalizedFluxEstimates

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDerivative coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)

/-- The cutoff makes the coupling integral finite. -/
theorem coupling_integrable {χ : Space → ℝ} {u w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x))) :
    Integrable (fun x => χ x *
      ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) volume := by
  apply LocalizedDifferenceEnergy.integrable_cutoff_mul hχ hs
  exact hw.inner ((hu.continuous_fderiv (by simp)).clm_apply hw)

/-- The indefinite coupling is controlled by the gradient of the reference
velocity and the actual compactly weighted energy. -/
theorem neg_coupling_le_weightedEnergy {χ : Space → ℝ} {u w : VelocityField} {t G : ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hu : ContDiff ℝ 1 (fun x => u (t, x)))
    (hw : Continuous (fun x => w (t, x)))
    (hG : ∀ x, ‖spatialDerivative u t x‖ ≤ G) :
    -(∫ x, χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
      G * weightedEnergy χ w t := by
  have hi := coupling_integrable hχ hs hu hw
  have he := LocalizedDifferenceEnergy.integrable_weighted_energy hχ hs hw
  rw [← integral_neg]
  change (∫ x, -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)) ≤
    G * (∫ x, χ x * ‖w (t, x)‖ ^ 2)
  rw [← integral_const_mul]
  apply integral_mono hi.neg (he.const_mul G)
  intro x
  change -(χ x * ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ) ≤
    G * (χ x * ‖w (t, x)‖ ^ 2)
  have h := NavierStokes.PeriodicUniqueness.nonlinear_energy_bound
    (spatialDerivative u t x) (w (t, x)) (hG x)
  linarith [mul_le_mul_of_nonneg_left h (hχ0 x)]

/-- Derivative of the energy weight. -/
theorem fderiv_cutoff_eight {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
  simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
    ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv

/-- One power of the cutoff is harmless because it lies in `[0,1]`. -/
theorem norm_fderiv_cutoff_eight_apply_le {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ‖fderiv ℝ φ x‖ ≤ L) (z : Space) :
    ‖fderiv ℝ (fun y => φ y ^ 8) x z‖ ≤ (8 * L) * φ x ^ 6 * ‖z‖ := by
  have h76 : φ x ^ 7 ≤ φ x ^ 6 := by
    calc
      φ x ^ 7 = φ x ^ 6 * φ x := by ring
      _ ≤ φ x ^ 6 * 1 := mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 6)
      _ = φ x ^ 6 := mul_one _
  have hd : ‖fderiv ℝ φ x z‖ ≤ L * ‖z‖ :=
    ((fderiv ℝ φ x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
  rw [fderiv_cutoff_eight hφ, _root_.smul_apply, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * φ x ^ 7)]
  calc
    (8 * φ x ^ 7) * ‖fderiv ℝ φ x z‖ ≤ (8 * φ x ^ 7) * (L * ‖z‖) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = φ x ^ 7 * ((8 * L) * ‖z‖) := by ring
    _ ≤ φ x ^ 6 * ((8 * L) * ‖z‖) :=
      mul_le_mul_of_nonneg_right h76 (by positivity)
    _ = (8 * L) * φ x ^ 6 * ‖z‖ := by ring

/-- The reference velocity vanishes in the cutoff derivative, leaving only
the difference velocity in the transport flux. -/
theorem transport_flux_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hvanish : ∀ x, fderiv ℝ (fun y => φ y ^ 8) x (u (t, x)) = 0) :
    Integrable (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) volume ∧
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
      (8 * L) * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ) := by
  have hw : Continuous (fun x => (u - v) (t, x)) := hu.sub hv
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hT, hTb⟩ := WeightedInterpolation.cutoff_transport_bound
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hweighted
  have hswitch (x : Space) : fderiv ℝ (fun y => φ y ^ 8) x (v (t, x)) =
      -fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x)) := by
    simp only [Pi.sub_apply, map_sub, hvanish x, zero_sub, neg_neg]
  have hbound (x : Space) :
      ‖‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))‖ ≤
        (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := by
    rw [norm_mul, norm_pow, norm_norm, hswitch, norm_neg]
    calc
      ‖(u - v) (t, x)‖ ^ 2 *
          ‖fderiv ℝ (fun y => φ y ^ 8) x ((u - v) (t, x))‖ ≤
          ‖(u - v) (t, x)‖ ^ 2 * ((8 * L) * φ x ^ 6 * ‖(u - v) (t, x)‖) :=
        mul_le_mul_of_nonneg_left
          (norm_fderiv_cutoff_eight_apply_le (hφ.differentiable (by simp) x)
            (hφ0 x) (hφ1 x) hL0 (hL x) _) (sq_nonneg _)
      _ = _ := by ring
  have hmajor := hT.const_mul (8 * L)
  have hflux : Continuous (fun x => ‖(u - v) (t, x)‖ ^ 2 *
      fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))) :=
    (hw.norm.pow 2).mul (((hφ.pow 8).continuous_fderiv (by simp)).clm_apply hv)
  refine ⟨hmajor.mono' hflux.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
        ∫ x, (8 * L) * (φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = (8 * L) * (∫ x, φ x ^ 6 * ‖(u - v) (t, x)‖ ^ 3) := integral_const_mul _ _
    _ ≤ (8 * L) * (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hTb (by positivity)
    _ = _ := by ring

theorem continuous_laplacian {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (ComparisonCutoffs.laplacian χ) := by
  unfold ComparisonCutoffs.laplacian
  exact continuous_finsetSum _ fun i _ =>
    (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
      (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hχ i) i).continuous

/-- A bounded Laplacian can be paired with any square-integrable field. -/
theorem laplacian_flux_bound {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw2 : MemLp w 2 volume) {K : ℝ}
    (hK : ∀ x, ‖ComparisonCutoffs.laplacian χ x‖ ≤ K) :
    Integrable (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume ∧
      |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ K * comparisonLpNorm 2 w ^ 2 := by
  have hsquare : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hmajor := hsquare.const_mul K
  have hbound (x : Space) : ‖‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x‖ ≤
      K * ‖w x‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_norm]
    exact (mul_le_mul_of_nonneg_left (hK x) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hmeas : AEStronglyMeasurable
      (fun x => ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x) volume :=
    (hw2.aestronglyMeasurable.norm.pow 2).mul (continuous_laplacian hχ).aestronglyMeasurable
  refine ⟨hmajor.mono' hmeas (Eventually.of_forall hbound), ?_⟩
  calc
    |∫ x, ‖w x‖ ^ 2 * ComparisonCutoffs.laplacian χ x| ≤ ∫ x, K * ‖w x‖ ^ 2 :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = K * l2Sq w := integral_const_mul _ _
    _ = K * comparisonLpNorm 2 w ^ 2 := by rw [← LpNormTools.lpNorm_two_sq_eq_l2Sq hw2]

/-- Base weight, given by `ComparisonCutoffs.baseCutoff x ^ 8`. -/
def baseWeight (x : Space) : ℝ := ComparisonCutoffs.baseCutoff x ^ 8

private theorem baseWeight_smooth : ContDiff ℝ ∞ baseWeight :=
  ComparisonCutoffs.baseCutoff_smooth.pow 8

private theorem baseWeight_hasCompactSupport : HasCompactSupport baseWeight :=
  ComparisonCutoffs.baseCutoff_hasCompactSupport.comp_left
    (g := fun r : ℝ => r ^ 8) (by norm_num)

theorem exists_weight_second_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space, ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (baseWeight_hasCompactSupport.iteratedFDeriv 2).exists_bound_of_continuous
    (ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseWeight_smooth 2))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

/-- A fixed derivative bound for the unscaled energy weight. -/
def weightSecondDerivativeConstant : ℝ := Classical.choose exists_weight_second_derivative_bound

theorem weightSecondDerivativeConstant_pos : 0 < weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).1

private theorem baseWeight_iteratedFDeriv_two_le (x : Space) :
    ‖iteratedFDeriv ℝ 2 baseWeight x‖ ≤ weightSecondDerivativeConstant :=
  (Classical.choose_spec exists_weight_second_derivative_bound).2 x

private def weightDilation (R : ℝ) : Space →L[ℝ] Space :=
  R⁻¹ • ContinuousLinearMap.id ℝ Space

private theorem norm_weightDilation_le {R : ℝ} (hR : 0 < R) :
    ‖weightDilation R‖ ≤ R⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
  intro x
  change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
  rw [ComparisonCutoffs.norm_scaled hR, div_eq_inv_mul]

/-- Apply scaling to the fixed eighth-power weight before estimating its
derivatives. The second derivative has the same inverse-square scaling. -/
theorem weight_iteratedFDeriv_two_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (ComparisonCutoffs.weight R) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  change ‖iteratedFDeriv ℝ 2 (baseWeight ∘ weightDilation R) x‖ ≤ _
  rw [(weightDilation R).iteratedFDeriv_comp_right
    (contDiff_infty.1 baseWeight_smooth 2) x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)).compContinuousLinearMap
        (fun _ => weightDilation R)‖ ≤
        ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ *
          ∏ _ : Fin 2, ‖weightDilation R‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 baseWeight (weightDilation R x)‖ * (R⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ∏ _ : Fin 2, ‖weightDilation R‖ ≤ ∏ _ : Fin 2, R⁻¹ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_weightDilation_le hR)
        _ = (R⁻¹) ^ 2 := by simp
    _ ≤ weightSecondDerivativeConstant * (R⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (baseWeight_iteratedFDeriv_two_le _) (by positivity)
    _ = weightSecondDerivativeConstant / R ^ 2 := by simp [div_eq_mul_inv]

theorem weight_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (ComparisonCutoffs.weight R)) x‖ ≤
      weightSecondDerivativeConstant / R ^ 2 := by
  have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
    (f := fderiv ℝ (ComparisonCutoffs.weight R)) (x := x) (n := 0)
  simp only [norm_iteratedFDeriv_zero] at hn
  rw [hn, norm_iteratedFDeriv_fderiv]
  exact weight_iteratedFDeriv_two_le hR x

/-- The fixed constant in the inverse-square Laplacian estimate. -/
def weightLaplacianConstant : ℝ := 3 * weightSecondDerivativeConstant

theorem weightLaplacianConstant_pos : 0 < weightLaplacianConstant :=
  mul_pos (by norm_num) weightSecondDerivativeConstant_pos

theorem weight_laplacian_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
      weightLaplacianConstant / R ^ 2 := by
  calc
    ‖ComparisonCutoffs.laplacian (ComparisonCutoffs.weight R) x‖ ≤
        ∑ i : Fin 3, ‖spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, weightSecondDerivativeConstant / R ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        (ComparisonCutoffs.norm_partial_partial_le (ComparisonCutoffs.weight_smooth R)
          i i x).trans (weight_second_fderiv_le hR x)
    _ = weightLaplacianConstant / R ^ 2 := by
      simp [weightLaplacianConstant, mul_div_assoc]

/-- The Laplacian term in the energy identity is of order `R⁻² M²`.
Finiteness is explicit and only requires `L²` membership of the velocity. -/
theorem weight_laplacian_flux_bound {R : ℝ} (hR : 0 < R) {w : VelocityField} {t : ℝ}
    (hw2 : MemLp (fun x => w (t, x)) 2 volume) :
    Integrable (fun x => ‖w (t, x)‖ ^ 2 *
      ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x) volume ∧
      |∫ x, ‖w (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i (ComparisonCutoffs.weight R)) x| ≤
          (weightLaplacianConstant / R ^ 2) * comparisonLpNorm 2 (fun x => w (t, x)) ^ 2 :=
  laplacian_flux_bound (ComparisonCutoffs.weight_smooth R) hw2 (weight_laplacian_le hR)

end NavierStokesR3.LocalizedFluxEstimates

end
end

end

section

/-!
# Scalar closure of the whole-space comparison estimate

The localized energy may have derivatives only in the interior of the time
interval. The integrating-factor argument below therefore uses continuity on
the closed interval and the mean-value theorem on its interior. In particular,
no energy inequality at a time endpoint is assumed.
-/

@[expose] public section

noncomputable section

open Set

namespace NavierStokesR3.ComparisonGronwall

/-- The weighted perturbed Gronwall estimate with a nonpositive initial value.
Only interior derivatives of `E` are needed. -/
theorem exp_neg_mul_le_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, Real.exp (-K * t) * E t ≤ ε * t := by
  let G : ℝ → ℝ := fun t => Real.exp (-K * t) * E t - ε * t
  let G' : ℝ → ℝ := fun t => Real.exp (-K * t) * (E' t - K * E t) - ε
  have hgcont : ContinuousOn G (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hcont).sub (continuous_const.mul continuous_id).continuousOn
  have hgderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt G (G' t) t := by
    have hexp := ((hasDerivAt_id t).const_mul (-K)).exp
    convert! (hexp.mul (hderiv t ht)).sub ((hasDerivAt_id t).const_mul ε) using 1
    try dsimp [G, G']
    ring
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have hexp : Real.exp (-K * t) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) ht'.1.le)
      have hfirst : Real.exp (-K * t) * (E' t - K * E t) ≤
          Real.exp (-K * t) * ε :=
        mul_le_mul_of_nonneg_left (by linarith [hbound t ht']) (Real.exp_pos _).le
      have hsecond : Real.exp (-K * t) * ε ≤ ε := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hε
      dsimp only [G']
      linarith
  intro t ht
  have hle := hG ⟨le_rfl, hT⟩ ht ht.1
  have hzero : G 0 ≤ 0 := by simpa [G] using hinitial
  have hnonpos := hle.trans hzero
  exact sub_nonpos.mp hnonpos

/-- Perturbed Gronwall, retaining the actual time in the bound. -/
theorem le_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * t * Real.exp (K * t) := by
  intro t ht
  have hweighted := exp_neg_mul_le_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos (K * t)).le
  have hexp : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]
    have hcancel : -K * t + K * t = 0 := by ring
    rw [hcancel, Real.exp_zero]
  calc
    E t = Real.exp (-K * t) * E t * Real.exp (K * t) := by
      calc
        E t = E t * 1 := (mul_one _).symm
        _ = E t * (Real.exp (-K * t) * Real.exp (K * t)) := by rw [hexp]
        _ = _ := by ring
    _ ≤ ε * t * Real.exp (K * t) := hmul

/-- Perturbed Gronwall with one bound valid throughout the closed interval. -/
theorem le_uniform_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * T * Real.exp (K * T) := by
  intro t ht
  calc
    E t ≤ ε * t * Real.exp (K * t) :=
      le_exp_mul_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
    _ ≤ ε * T * Real.exp (K * T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left ht.2 hε
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hε hT

/-- A forcing error of order `1 / R` gives a uniform energy error of the same
order. The numerator depends only on `C`, `K`, and the time interval. -/
theorem le_div_radius_of_deriv_le {T K C R : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 < R)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + C / R) :
    ∀ t ∈ Icc 0 T, E t ≤ (C * T * Real.exp (K * T)) / R := by
  intro t ht
  have hle := le_uniform_exp_mul_of_deriv_le hT hK (div_nonneg hC hR.le)
    hcont hinitial.le hderiv hbound t ht
  convert! hle using 1
  ring

/-- Apply the scalar estimate to a family of localized energies. All radii
share the same constant in the numerator. -/
theorem exists_uniform_radius_bound {T K C : ℝ} {E E' : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcont : ∀ R : ℝ, 1 ≤ R → ContinuousOn (E R) (Icc 0 T))
    (hinitial : ∀ R : ℝ, 1 ≤ R → E R 0 = 0)
    (hderiv : ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T, HasDerivAt (E R) (E' R t) t)
    (hbound : ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T, E' R t ≤ K * E R t + C / R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Icc 0 T, E R t ≤ D / R := by
  refine ⟨C * T * Real.exp (K * T), mul_nonneg (mul_nonneg hC hT) (Real.exp_pos _).le,
    ?_⟩
  intro R hR
  exact le_div_radius_of_deriv_le hT hK hC (lt_of_lt_of_le zero_lt_one hR)
    (hcont R hR) (hinitial R hR) (hderiv R hR) (hbound R hR)

/-- A nonnegative scalar with a uniform `1 / R` bound for every `R ≥ 1`
vanishes. This is the final scalar step in cutoff exhaustion. -/
theorem eq_zero_of_forall_radius_bound {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hbound : ∀ R : ℝ, 1 ≤ R → x ≤ D / R) : x = 0 := by
  by_contra hzero
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  let R : ℝ := (D + 1) / x + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [div_nonneg (show 0 ≤ D + 1 by linarith) hx]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmul : x * R ≤ D := (le_div_iff₀ hRpos).mp (hbound R hR)
  have hcancel : (D + 1) / x * x = D + 1 := div_mul_cancel₀ _ hxpos.ne'
  dsimp [R] at hmul
  linarith

/-- For a fixed compact set, the cutoff bound is available only after the
radius contains that set. Such a bound is still sufficient for vanishing. -/
theorem eq_zero_of_forall_large_radius_bound {x D R₀ : ℝ} (hx : 0 ≤ x)
    (hbound : ∀ R : ℝ, max 1 R₀ ≤ R → x ≤ D / R) : x = 0 := by
  by_contra hzero
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  let R : ℝ := max (max 1 R₀) ((D + 1) / x + 1)
  have hR : max 1 R₀ ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hmul : x * R ≤ D := (le_div_iff₀ hRpos).mp (hbound R hR)
  have hsize : (D + 1) / x + 1 ≤ R := le_max_right _ _
  have hsize_mul := mul_le_mul_of_nonneg_left hsize hx
  have hcancel : (D + 1) / x * x = D + 1 := div_mul_cancel₀ _ hxpos.ne'
  linarith

end NavierStokesR3.ComparisonGronwall

end
end

end

section

/-!
# Removing the spatial energy cutoff

At a fixed time, square integrability gives an integrable dominating function.
This module removes the cutoff only after that hypothesis has been supplied.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.WholeSpaceEnergyLimit

open ProblemStatement Comparison ComparisonCutoffs

theorem integral_weight_tendsto {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) :
    Tendsto (fun R : ℝ => ∫ x : Space, weight R x * ‖w x‖ ^ 2)
      atTop (𝓝 (l2Sq w)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : Space => ‖w x‖ ^ 2)
  · exact Filter.Eventually.of_forall fun R =>
      ((weight_smooth R).continuous.mul (hw.norm.pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg R x) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_le_one R x)
  · exact hi
  · exact Filter.Eventually.of_forall fun x => by
      have h := ((cutoff_tendsto_one x).pow 8).mul_const (‖w x‖ ^ 2)
      simpa only [weight, one_pow, one_mul] using h

theorem eq_zero_of_l2Sq_eq_zero {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) (hz : l2Sq w = 0) :
    ∀ x : Space, w x = 0 := by
  have hae : (fun x : Space => ‖w x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hz
  have heq : (fun x : Space => ‖w x‖ ^ 2) = (fun _ : Space => (0 : ℝ)) :=
    Measure.eq_of_ae_eq hae (hw.norm.pow 2) continuous_const
  intro x
  have hx : ‖w x‖ ^ 2 = 0 := congrFun heq x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- A bound on actual weighted integrals, uniform over large radii, forces a
continuous square-integrable field to vanish everywhere. -/
theorem eq_zero_of_radius_bound {w : Space → Space} (hw : Continuous w)
    (hi : Integrable (fun x : Space => ‖w x‖ ^ 2)) {D R₀ : ℝ}
    (hbound : ∀ R : ℝ, max 1 R₀ ≤ R →
      (∫ x : Space, weight R x * ‖w x‖ ^ 2) ≤ D / R) :
    ∀ x : Space, w x = 0 := by
  have hlim := integral_weight_tendsto hw hi
  have hz : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atTop (𝓝 D)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have hle : l2Sq w ≤ 0 :=
    le_of_tendsto_of_tendsto hlim hz (eventually_atTop.2 ⟨max 1 R₀, hbound⟩)
  exact eq_zero_of_l2Sq_eq_zero hw hi
    (le_antisymm hle (integral_nonneg fun x => sq_nonneg _))

/-- The final scalar and cutoff step of uniqueness. The differential estimate
is an explicit input here; deriving it from the PDE and pressure is separate. -/
theorem eq_zero_of_weighted_rate_bound {w : VelocityField} {T K C R₀ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, SquareIntegrableAtTime w t)
    (hzero : ∀ x : Space, w (0, x) = 0)
    (hrate : ∀ R : ℝ, max 1 R₀ ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      weightedEnergyRate (weight R) w t ≤ K * weightedEnergy (weight R) w t + C / R) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, w (t, x) = 0 := by
  intro t ht
  have hs := NavierStokes.PeriodicUniqueness.spatial_smooth hw ht
  apply eq_zero_of_radius_bound hs.continuous (hi t ht)
    (D := C * T * Real.exp (K * T)) (R₀ := R₀)
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hcont := LocalizedDifferenceEnergy.weightedEnergy_continuousOn
    (weight_smooth R).continuous (weight_hasCompactSupport hRpos) hw
  have hinit : weightedEnergy (weight R) w 0 = 0 := by
    simp [weightedEnergy, hzero]
  exact ComparisonGronwall.le_div_radius_of_deriv_le hT hK hC hRpos hcont hinit
    (fun s hs => LocalizedDifferenceEnergy.weightedEnergy_hasDerivAt
      (weight_smooth R) (weight_hasCompactSupport hRpos) hw hs)
    (hrate R hR) t ht

end NavierStokesR3.WholeSpaceEnergyLimit

end
end

end

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace

namespace NavierStokesR3.WholeSpaceComparisonClosure

open ProblemStatement Comparison ComparisonCutoffs
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth time_differentiable_at_interior)

/-- Pressure envelope, given by `(B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) + R ^ (-7 / 4 : ℝ)
* B ^ (3 / 4 : ℝ)`. -/
def pressureEnvelope (R A B : ℝ) : ℝ :=
  (B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
    R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)

/-- Once the pressure flux has been estimated from the equations, compact
localized integration, Sobolev, Young and Gronwall imply equality everywhere.
All constants precede the radius and time quantifiers. -/
theorem eq_of_pressure_flux_bound {T M G CP R₀ : ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hG0 : 0 ≤ G) (hCP0 : 0 ≤ CP)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hwu : ∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x))
    (hvanish : ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (weight R) x (u (t, x)) = 0)
    (hpressure : ∀ R ≥ 1, ∀ t ∈ Ioo (0 : ℝ) T,
      |∫ x : Space, (p - q) (t, x) * fderiv ℝ (weight R) x ((u - v) (t, x))| ≤
        CP * pressureEnvelope R (dissipationRoot (cutoff R) (u - v) t)
          (cutoffL6 (cutoff R) (u - v) t)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  let C0 := LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / 2
  let C1 := 4 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact div_nonneg (mul_nonneg
      LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg M)) (by norm_num)
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos 1).le)
      (Real.rpow_nonneg hM0 _)
  obtain ⟨D, hD, hrate⟩ := ComparisonRateBound.exists_uniform_rate_bound hC0 hC1 hCP0
    WeightedSobolev.weightedSobolevConstant_pos.le
    (mul_nonneg (derivativeConstant_pos 1).le hM0)
  have hwzero : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, (u - v) (t, x) = 0 := by
    apply WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound (K := 2 * G) (C := D) (R₀ := R₀)
      hT (mul_nonneg (by norm_num) hG0) hD (hu.sub hv)
    · intro t ht
      exact (memLp_two_iff_integrable_sq_norm (hwu t ht).aestronglyMeasurable).mp (hwu t ht)
    · intro x
      simp only [hzero x, sub_self]
    · intro R hR t ht
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRpos : 0 < R := zero_lt_one.trans_le hR1
      have htcc : t ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self ht
      have hut := spatial_smooth hu htcc
      have hvt := spatial_smooth hv htcc
      have hwt := hut.sub hvt
      have hw2 := hwu t htcc
      let A := dissipationRoot (cutoff R) (u - v) t
      let B := cutoffL6 (cutoff R) (u - v) t
      have hA : 0 ≤ A := Real.sqrt_nonneg _
      have hB : 0 ≤ B := ENNReal.toReal_nonneg
      have hm : 0 ≤ comparisonLpNorm 2 (fun x => (u - v) (t, x)) := ENNReal.toReal_nonneg
      have hAsq : A ^ 2 = weightedDissipation (weight R) (u - v) t := by
        apply Real.sq_sqrt
        exact LocalizedDifferenceEnergy.weightedDissipation_nonneg (weight_nonneg R) _ _
      have hSob0 := WeightedSobolev.cutoffL6_le
        ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
        (hwt.of_le (by simp)) hw2 (cutoff_nonneg R) (cutoff_le_one R)
        (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
      have hSob : B ≤ WeightedSobolev.weightedSobolevConstant *
          (A + (derivativeConstant 1 * M) / R) := by
        apply hSob0.trans
        apply mul_le_mul_of_nonneg_left _ WeightedSobolev.weightedSobolevConstant_pos.le
        apply add_le_add_right
        calc
          derivativeConstant 1 / R * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤
              derivativeConstant 1 / R * M := mul_le_mul_of_nonneg_left (hM t htcc)
                (div_nonneg (derivativeConstant_pos 1).le hRpos.le)
          _ = _ := by ring
      have hc := LocalizedFluxEstimates.neg_coupling_le_weightedEnergy
        (u := u) (w := u - v) (t := t)
        (weight_smooth R).continuous (weight_hasCompactSupport hRpos) (weight_nonneg R)
        (hut.of_le (by simp)) hwt.continuous (hG t htcc)
      have hl := (LocalizedFluxEstimates.weight_laplacian_flux_bound hRpos hw2).2
      have hl' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          ∑ i : Fin 3, partialD i (partialD i (weight R)) x| ≤
          LocalizedFluxEstimates.weightLaplacianConstant * M ^ 2 / R ^ 2 := by
        apply hl.trans
        calc
          _ ≤ (LocalizedFluxEstimates.weightLaplacianConstant / R ^ 2) * M ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm (hM t htcc) 2)
              (div_nonneg LocalizedFluxEstimates.weightLaplacianConstant_pos.le (sq_nonneg _))
          _ = _ := by ring
      have htflux := (LocalizedFluxEstimates.transport_flux_bound
        ((cutoff_smooth R).of_le (by simp)) (cutoff_hasCompactSupport hRpos)
        hut.continuous hvt.continuous hw2 (cutoff_nonneg R) (cutoff_le_one R)
        (div_nonneg (derivativeConstant_pos 1).le hRpos.le) (cutoff_fderiv_le hRpos)
        (hvanish R ((le_max_right _ _).trans hR) t htcc)).2
      have htflux' : |∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
          fderiv ℝ (weight R) x (v (t, x))| ≤
          (8 * derivativeConstant 1 * M ^ (3 / 2 : ℝ)) / R * B ^ (3 / 2 : ℝ) := by
        apply htflux.trans
        calc
          _ ≤ (8 * (derivativeConstant 1 / R)) * M ^ (3 / 2 : ℝ) * B ^ (3 / 2 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB _)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hm (hM t htcc) (by norm_num))
              (mul_nonneg (by norm_num) (div_nonneg (derivativeConstant_pos 1).le hRpos.le))
          _ = _ := by ring
      have hpflux := hpressure R hR1 t ht
      have hbalance := LocalizedDifferenceEnergy.difference_energy_balance
        (weight_smooth R) (weight_hasCompactSupport hRpos) hut hvt
        (spatial_smooth hp htcc) (spatial_smooth hq htcc)
        (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
        (hdu t ht) (hdv t ht) (hNS t ht)
      apply hrate R hR1 A hA B hB hSob
        (weightedEnergy (weight R) (u - v) t) (weightedEnergyRate (weight R) (u - v) t) G
      rw [hAsq, hbalance]
      have hlle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, partialD i (partialD i (weight R)) x)).trans hl'
      have htle := (le_abs_self (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ (weight R) x (v (t, x)))).trans htflux'
      have hple : (∫ x : Space, (p - q) (t, x) *
          fderiv ℝ (weight R) x ((u - v) (t, x))) ≤ CP * pressureEnvelope R A B :=
        (le_abs_self _).trans hpflux
      have hsum := add_le_add (add_le_add
        (add_le_add hc (mul_le_mul_of_nonneg_left hlle (by norm_num : (0 : ℝ) ≤ 1 / 2)))
        (mul_le_mul_of_nonneg_left htle (by norm_num : (0 : ℝ) ≤ 1 / 2))) hple
      convert! hsum using 1
      dsimp only [C0, C1, pressureEnvelope]
      ring
  intro t ht x
  exact sub_eq_zero.mp (hwzero t ht x)

end NavierStokesR3.WholeSpaceComparisonClosure

end
end

end

section

/-!
# Constants supplied by the compactly supported comparison solution

These bounds are consequences of joint smoothness and one fixed compact
spatial support. They impose no condition on the competing solution.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace NavierStokesR3.CompactComparisonBounds

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDerivative)

/-- The shared compact support contains the support of every spatial slice. -/
theorem hasCompactSupport_slice {T : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasCompactSupport (fun x : Space => u (t, x)) :=
  hK.of_isClosed_subset isClosed_closure (hsupp t ht)

/-- The candidate's first spatial derivative is bounded on all of space and
uniformly over the closed comparison interval. -/
theorem exists_gradient_bound {T : ℝ} (hT : 0 < T) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      ‖spatialDerivative u t x‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := NavierStokes.PeriodicUniqueness.exists_gradient_bound hT hu hK
  refine ⟨G, hG.le, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact hbound t ht x hx
  · have hzero : spatialDerivative u t x = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hsupp t ht h))
    rw [hzero, norm_zero]
    exact hG.le

/-- Compact support and continuity place every candidate slice in `L³`. -/
theorem memLp_three_slice {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MemLp (fun x : Space => u (t, x)) 3 volume :=
  (CompactTimeIntegral.continuous_slice hu ht).memLp_of_hasCompactSupport
    (hasCompactSupport_slice hK hsupp ht)

/-- The ordinary cube-norm integral varies continuously with time. -/
theorem continuousOn_integral_norm_cube {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ContinuousOn (fun t => ∫ x : Space, ‖u (t, x)‖ ^ 3) (Icc (0 : ℝ) T) := by
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => ‖u z‖ ^ 3) hK (hu.norm.pow 3)
  intro t ht x hx
  have hzero : u (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
      (fun h => hx (hsupp t ht h))
  simp only [hzero, norm_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)]

/-- The finite `L³` norm has its ordinary integral formula. -/
theorem lpNorm_three_eq_integral_norm_cube_rpow {f : Space → Space}
    (hf : MemLp f 3 volume) :
    comparisonLpNorm 3 f = (∫ x : Space, ‖f x‖ ^ 3) ^ (3 : ℝ)⁻¹ := by
  have heq := MemLp.eLpNorm_eq_integral_rpow_norm
    (p := (3 : ℝ≥0∞)) (by norm_num) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat] at heq
  rw [comparisonLpNorm, heq, ENNReal.toReal_ofReal]
  · rw [one_div]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => Real.rpow_natCast (‖f x‖) 3)
  · positivity

/-- One finite `L³` bound works at every time in the comparison interval. -/
theorem exists_lpNorm_three_bound {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ t ∈ Icc (0 : ℝ) T,
      MemLp (fun x : Space => u (t, x)) 3 volume ∧
        comparisonLpNorm 3 (fun x => u (t, x)) ≤ U := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_integral_norm_cube hu hK hsupp)
  refine ⟨(max C 0) ^ (3 : ℝ)⁻¹, by positivity, ?_⟩
  intro t ht
  have hLp := memLp_three_slice hu hK hsupp ht
  refine ⟨hLp, ?_⟩
  rw [lpNorm_three_eq_integral_norm_cube_rpow hLp]
  apply Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) _ (by positivity)
  exact (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))

/-- The cutoff weight is locally constant throughout its strict plateau. -/
theorem weight_fderiv_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R)
    {x : Space} (hx : ‖x‖ < R) :
    fderiv ℝ (ComparisonCutoffs.weight R) x = 0 := by
  have heq : ComparisonCutoffs.weight R =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact ComparisonCutoffs.weight_eq_one hR hy.le
  rw [heq.fderiv_eq, fderiv_const_apply]

/-- Sufficiently large cutoffs have exactly zero derivative in the direction
of the compactly supported candidate, at every spatial point. -/
theorem exists_radius_weight_derivative_zero {T : ℝ} {u : VelocityField}
    {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      fderiv ℝ (ComparisonCutoffs.weight R) x (u (t, x)) = 0 := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max 1 (C + 1), le_max_left _ _, ?_⟩
  intro R hR t ht x
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  by_cases hx : x ∈ K
  · have hxR : ‖x‖ < R :=
      lt_of_le_of_lt (hC x hx) ((lt_add_one C).trans_le ((le_max_right _ _).trans hR))
    rw [weight_fderiv_eq_zero_of_norm_lt hRpos hxR]
    rfl
  · have hzero : u (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
        (fun h => hx (hsupp t ht h))
    rw [hzero, map_zero]

/-- On a compact time interval, smoothness and one fixed compact spatial
support already imply the target's uniform finite-energy condition. -/
theorem uniformFiniteEnergy_of_compact_slab {T : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    UniformFiniteEnergy (Icc (0 : ℝ) T) u := by
  have hcont : ContinuousOn (fun t => ∫ x : Space, ‖u (t, x)‖ ^ 2)
      (Icc (0 : ℝ) T) := by
    apply CompactTimeIntegral.continuousOn_integral
      (F := fun z : SpaceTime => ‖u z‖ ^ 2) hK (hu.continuousOn.norm.pow 2)
    intro t ht x hx
    have hzero : u (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
        (fun h => hx (hsupp t ht h))
    simp only [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨(1 / 2 : ℝ) * max C 0, by positivity, ?_⟩
  intro t ht
  have hLp : MemLp (fun x : Space => u (t, x)) 2 volume :=
    (CompactTimeIntegral.continuous_slice hu.continuousOn ht).memLp_of_hasCompactSupport
      (hasCompactSupport_slice hK hsupp ht)
  refine ⟨(memLp_two_iff_integrable_sq_norm hLp.1).1 hLp, ?_⟩
  have hbound : (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ max C 0 :=
    (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))
  exact mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)

end NavierStokesR3.CompactComparisonBounds

end
end

end

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.WholeSpaceUniqueness

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- Whole-space comparison on a positive closed time interval. Finite energy
of the reference velocity is a consequence of its compact spatial support. -/
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  let H : PressureRecovery.Hypotheses T u v p q :=
    ⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => u (t, x)) volume :=
    fun t ht => (spatial_smooth hu ht).continuous.aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => v (t, x)) volume :=
    fun t ht => (spatial_smooth hv ht).continuous.aestronglyMeasurable
  have hew := uniformFiniteEnergy_sub hum hvm heu hev
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht)) hew
  obtain ⟨U, hU0, hU⟩ := CompactComparisonBounds.exists_lpNorm_three_bound
    hu.continuousOn hK hsupp
  obtain ⟨G₀, hG₀, hTensor⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound hum hvm heu hev
  obtain ⟨CP, hCP, hpressure⟩ := PressureFlux.exists_uniform_actual_pressure_flux_bound
    H M U G₀ hM0 hU0 hG₀ hM hU hTensor
  obtain ⟨G, hG0, hG⟩ := CompactComparisonBounds.exists_gradient_bound hT hu hK hsupp
  obtain ⟨R₀, _hR₀, hvanish⟩ := CompactComparisonBounds.exists_radius_weight_derivative_zero hK
      hsupp
  apply WholeSpaceComparisonClosure.eq_of_pressure_flux_bound
    hT.le hM0 hG0 hCP hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hzero hvanish
  intro R hR t ht
  simpa only [WholeSpaceComparisonClosure.pressureEnvelope, neg_div] using hpressure R hR t ht

/-- The exact compact candidate agrees with every smooth finite-energy
competitor on each closed interval before time one. -/
theorem candidate_unique_on_Icc {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    {T : ℝ} (hT : T < 1) {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual 1 v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  by_cases hT0 : 0 < T
  · have hsub : Comparison.slab 0 T ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
    apply classical_uniqueness_on_Icc hT0 (h.velocity_smooth.mono hsub) hv
      (h.pressure_smooth.mono hsub) hq h.support_compact
    · intro t ht
      exact h.velocity_support t ⟨ht.1, ht.2.trans_lt hT⟩
    · exact hev
    · intro t ht x
      exact h.divergence_free t ⟨ht.1.le, ht.2.trans hT⟩ x
    · exact hdv
    · intro t ht x
      exact (h.navier_stokes t ⟨ht.1, ht.2.trans hT⟩ x).trans (hNSv t ht x).symm
    · intro x
      exact (h.zero_initial_velocity x).trans (hvzero x).symm
  · intro t ht x
    have ht0 : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hT0)) ht.1
    rw [ht0, h.zero_initial_velocity, hvzero]

/-- A global smooth solution with uniformly finite kinetic energy must agree
with the candidate at every time strictly before one. -/
theorem candidate_global_agrees_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    (v : GlobalFiniteEnergySolution 1 f) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v.velocity (t, x) := by
  intro t ht
  have hsub : Comparison.slab 0 t ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have he := v.energy_bounded.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ hs => hs.1)
  exact candidate_unique_on_Icc h ht.2 (v.velocity_smooth.mono hsub)
    (v.pressure_smooth.mono hsub) he
    (fun s hs => v.divergence_free s hs.1.le)
    (fun s hs => v.navier_stokes s hs.1)
    v.zero_initial_velocity t ⟨ht.1, le_rfl⟩

end NavierStokesR3.WholeSpaceUniqueness
