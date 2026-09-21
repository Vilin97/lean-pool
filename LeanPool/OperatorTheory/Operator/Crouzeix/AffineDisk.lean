/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import LeanPool.OperatorTheory.Operator.Crouzeix.AffinePolynomial
import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR

/-!
# Affine disk normalization

This file transports the unit-disk form of von Neumann's inequality to an
arbitrary closed disk.  The operator is normalized to `R⁻¹ • (A - c • 1)`,
while the polynomial is precomposed with `z ↦ R * z + c`.

## Main declarations

* `polynomialSupNorm_affineComposition_closedBall` — affine transport of the sup-norm;
* `closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le` — the centered operator-norm
  bound encloses the numerical range;
* `norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le` — von Neumann's inequality
  on an arbitrary disk;
* `isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le` — the corresponding spectral-set
  package.
-/

open scoped InnerProductSpace Pointwise Polynomial

/-- Precomposing with `z ↦ R * z + c` transports the polynomial sup-norm from the unit closed
disk to `closedBall c R`. -/
theorem polynomialSupNorm_affineComposition_closedBall
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    polynomialSupNorm (p.affineComposition (R : ℂ) c)
        (Metric.closedBall (0 : ℂ) 1) =
      polynomialSupNorm p (Metric.closedBall c R) := by
  rw [polynomialSupNorm_affineComposition_image]
  congr 1
  have h := affinity_unitClosedBall hR c
  rw [← Set.image_vadd, ← Set.image_smul, Set.image_image] at h
  simpa only [add_comm, Complex.real_smul, vadd_eq_add] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- If `A - cI` has norm at most `R`, then the closure of the numerical range of `A` lies in the
closed disk with center `c` and radius `R`. -/
theorem closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • 1‖ ≤ R) :
    closure (numericalRange A) ⊆ Metric.closedBall c R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    norm (⟪x, A x⟫_ℂ - c) = norm ⟪x, (A - c • 1) x⟫_ℂ := by
      rw [inner_sub_smul_one_apply_self A c hx]
    _ ≤ ‖x‖ * ‖(A - c • 1) x‖ := norm_inner_le_norm x _
    _ = ‖(A - c • 1) x‖ := by rw [hx, one_mul]
    _ ≤ ‖A - c • 1‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - c • 1‖ := by rw [hx, mul_one]
    _ ≤ R := hA

variable [CompleteSpace E]

/-- Von Neumann's inequality on a closed disk: if `‖A - cI‖ ≤ R` and `R > 0`, then evaluation
at `A` is bounded by the polynomial sup-norm on `closedBall c R`. -/
theorem norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by
  let T : E →L[ℂ] E := ((R : ℂ)⁻¹) • (A - c • 1)
  let q : ℂ[X] := p.affineComposition (R : ℂ) c
  have hT : ‖T‖ ≤ 1 := by
    dsimp only [T]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (inv_mul_le_one₀ hR).mpr hA
  have hAeval : Polynomial.aeval T q = Polynomial.aeval A p := by
    dsimp only [q]
    rw [Polynomial.aeval_affineComposition]
    congr 1
    dsimp only [T]
    rw [smul_smul]
    have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [mul_inv_cancel₀ hR0, one_smul, sub_add_cancel]
  calc
    ‖Polynomial.aeval A p‖ = ‖Polynomial.aeval T q‖ := congrArg norm hAeval.symm
    _ ≤ polynomialSupNorm q (Metric.closedBall (0 : ℂ) 1) :=
      vonNeumann_inequality T hT q
    _ = polynomialSupNorm p (Metric.closedBall c R) :=
      polynomialSupNorm_affineComposition_closedBall p c hR.le

/-- A disk containing `A` in the centered operator-norm sense is a polynomial spectral set for
`A`, with sharp constant `1`. -/
theorem isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) := by
  constructor
  · exact (spectrum_subset_closure_numericalRange A).trans
      (closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le A c hA)
  · intro p
    rw [one_mul]
    exact norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le A c hR hA p

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
