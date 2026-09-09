/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy

@[expose] public section

/-!
# Transport and pressure with a compact spatial weight

Only the scalar weight has compact support. The velocity, transported field,
and pressure may be arbitrary smooth functions on Euclidean three-space.
-/


noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- The divergence of a scalar-weighted vector field. -/
theorem divergence_weighted {χ : Space → ℝ} {v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v) (x : Space) :
    (∑ i : Fin 3, spatialPartial i (fun y => χ y • v y) x i) =
      fderiv ℝ χ x (v x) + χ x * ∑ i : Fin 3, spatialPartial i v x i := by
  have hpartial (i : Fin 3) :
      spatialPartial i (fun y => χ y • v y) x i =
        χ x * spatialPartial i v x i + spatialPartial i χ x * v x i := by
    change (EuclideanSpace.proj i)
      (fderiv ℝ (fun y => χ y • v y) x (coordinateVector i)) = _
    rw [fderiv_fun_smul (hχ.differentiable (by simp) x)
      (hv.differentiable (by simp) x)]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
      spatialPartial]
    rfl
  simp_rw [hpartial]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, fderiv_apply_eq_sum]
  simp only [spatialPartial]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- A compact scalar weight transfers a directional derivative to the weight
when the vector field is divergence free. -/
theorem integral_weighted_fderiv_apply {χ f : Space → ℝ} {v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, χ x * fderiv ℝ f x (v x)) =
      -(∫ x, f x * fderiv ℝ χ x (v x)) := by
  have h := CompactEnergy.integral_fderiv_apply hf (hχ.smul hv)
    (show HasCompactSupport (fun x => χ x • v x) from hcχ.smul_right)
  change (∫ x, fderiv ℝ f x (χ x • v x)) = -(∫ x, f x * ∑ i : Fin 3, spatialPartial i (fun y => χ y
    • v y) x i) at h
  simpa only [map_smul, smul_eq_mul, divergence_weighted hχ hv, hdiv,
    mul_zero, add_zero] using h

/-- The transport energy becomes a flux through the compact weight. No support
or global integrability assumption is imposed on either vector field. -/
theorem integral_weighted_transport {χ : Space → ℝ} {w v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) =
      -(1 / 2 : ℝ) * ∫ x, ‖w x‖ ^ 2 * fderiv ℝ χ x (v x) := by
  have h := integral_weighted_fderiv_apply hχ (hw.norm_sq ℝ) hv hcχ hdiv
  have hfun : (fun x => χ x * fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * (χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ)) := by
    funext x
    rw [fderiv_normsq hw]
    ring
  rw [hfun, integral_const_mul] at h
  linarith

/-- The pressure term becomes a flux through the compact weight. The pressure
need not have compact support or satisfy any bound at infinity. -/
theorem integral_weighted_pressure {χ π : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hπ : ContDiff ℝ ∞ π) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i w x i) = 0) :
    (∫ x, χ x * fderiv ℝ π x (w x)) =
      -(∫ x, π x * fderiv ℝ χ x (w x)) :=
  integral_weighted_fderiv_apply hχ hπ hw hcχ hdiv

end NavierStokesR3.LocalizedDifferenceEnergy
