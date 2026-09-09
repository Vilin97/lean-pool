/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy

@[expose] public section

/-!
# The Laplacian in a compactly weighted energy identity

All integrals are ordinary volume integrals on Euclidean three-space. The
weight is smooth and compactly supported; the vector field is smooth but is
not required to have compact support or globally integrable derivatives.
-/


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
