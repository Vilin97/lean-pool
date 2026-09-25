/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleKernel
public import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayer
public import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayerIntegral
public import LeanPool.OperatorTheory.Operator.Crouzeix.SymmetrizedBound
public import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleCauchy
public import LeanPool.OperatorTheory.Operator.NumericalRange.Bounded
public import LeanPool.OperatorTheory.Operator.Crouzeix.SymmetrizedAuxiliary
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleProduct
public import LeanPool.OperatorTheory.Operator.Crouzeix.Palencia
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleAuxiliary

/-!
# Circle-model symmetrized Crouzeix–Palencia bound (L4.2d assembly)

Let `A` be an operator whose numerical range closure lies in the open disk `ball c R`, and let
`B t = (-i γ'(t)) • R_A(γ(t))`, `γ = circleMap c R`, be the double-layer circle kernel.  Given the
double-layer representation `p(A) + G† = (2π)⁻¹ ∫₀^{2π} p(γ(t)) • (B t + (B t)†) dt` and the circle
Cauchy identity `∫₀^{2π} γ'(t) • R_A(γ(t)) dt = 2πi • 1`, the symmetrized bound
`‖p(A) + G†‖ ≤ 2 * sup_{|z - c| ≤ R} ‖p(z)‖` follows from the positive-kernel contractivity
(`SymmetrizedBound.lean`, `PositiveKernelBound.lean`): the kernel `B + B†` is positive
(`DoubleLayer.lean`), has mass `4π` (`DoubleLayerIntegral.lean`), and is integrable
(`CircleKernel.lean`).

The two analytic inputs are taken as explicit hypotheses in the main theorem; the circle Cauchy
identity is discharged (for `C(0, R)` with `‖A‖ < R`) by `CircleCauchy.lean` in the final
corollary, and the representation is the polynomial double-layer identity of
`SymmetrizedAuxiliary.lean`.

## Main declarations

* `norm_eval_circleMap_le_polynomialSupNorm_closedBall` — the scalar bound on the circle.
* `intervalIntegrable_deriv_circleMap_smul_resolvent` — integrability of the Cauchy integrand.
* `norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation` — the bound.
* `norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt` — the bound for
  the circle `C(0, R)` with `‖A‖ < R`, where the Cauchy identity is discharged by
  `CircleCauchy.lean` and only the representation hypothesis remains.
* `norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le` — the unconditional
  disk-model bound: for `‖A‖ < R` and the auxiliary operator `G` of `SmoothJordanDomain.ball 0 R`,
  `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ R} ‖p(z)‖` (representation from `SymmetrizedAuxiliary.lean`).
* `norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq` — the disk-model
  Crouzeix–Palencia inequality `‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖`, given the value
  `G = star (p.eval 0) • 1` of the disk auxiliary operator (the product bound of
  `CircleProduct.lean` and the balance identity of `Palencia.lean`).
* `norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt` — the unconditional
  **disk-model Crouzeix–Palencia inequality**: for `‖A‖ < R` and every polynomial `p`,
  `‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖` (auxiliary-operator value from `CircleAuxiliary.lean`).
-/

@[expose] public section

open Complex Polynomial spectrum
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On the circle `|z - c| = R` (with `0 ≤ R`), a polynomial is bounded by its sup-norm over the
closed disk `closedBall c R`. -/
theorem norm_eval_circleMap_le_polynomialSupNorm_closedBall (p : ℂ[X]) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (t : ℝ) :
    ‖p.eval (circleMap c R t)‖ ≤ polynomialSupNorm p (Metric.closedBall c R) :=
  norm_eval_le_polynomialSupNorm p
    (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
    (circleMap_mem_closedBall c hR t)

/-- The Cauchy integrand `γ'(t) • R_A(γ(t))` along a circle in the resolvent set is interval
integrable over `[0, 2π]`. -/
theorem intervalIntegrable_deriv_circleMap_smul_resolvent (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => deriv (circleMap c R) t • resolvent A (circleMap c R t))
      MeasureTheory.volume 0 (2 * Real.pi) := by
  have hd : Continuous (fun t : ℝ => deriv (circleMap c R) t) := by
    simp only [deriv_circleMap]
    fun_prop
  exact (hd.smul (continuous_resolvent_circleMap A hρ hR)).intervalIntegrable 0 (2 * Real.pi)

/-- **Circle-model symmetrized Crouzeix–Palencia bound**, given the double-layer representation of
`p(A) + G†` and the circle Cauchy identity for the resolvent: if the closure of the numerical range
of `A` lies in the open disk `ball c R`, then `‖p(A) + G†‖ ≤ 2 * sup_{|z - c| ≤ R} ‖p(z)‖`. -/
theorem norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hW : closure (numericalRange A) ⊆ Metric.ball c R)
    (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap c R t) •
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap c R) t • resolvent A (circleMap c R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall c R) := by
  have hρ : Metric.sphere c R ⊆ resolventSet ℂ A :=
    sphere_subset_resolventSet_of_closure_numericalRange_subset_ball A hW
  have hW' : numericalRange A ⊆ Metric.closedBall c R :=
    subset_closure.trans (hW.trans Metric.ball_subset_closedBall)
  refine norm_add_star_le_two_mul_of_doubleLayer_representation (aeval A p) G hrep
    (intervalIntegrable_circleKernel_add_adjoint A hρ hR)
    (intervalIntegrable_eval_smul_circleKernel_add_adjoint A hρ hR p)
    (fun t _ => ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (isPositive_add_adjoint_smul_resolvent_circleMap A hW' t))
    (intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy A (circleMap c R)
      (intervalIntegrable_deriv_circleMap_smul_resolvent A hρ hR) hCauchy)
    (polynomialSupNorm_nonneg p _)
    (fun t _ => norm_eval_circleMap_le_polynomialSupNorm_closedBall p c hR t)

/-! ### Discharging the Cauchy identity on `C(0, R)` for `‖A‖ < R` -/

omit [CompleteSpace E] in
/-- If `‖A‖ < R`, the closure of the numerical range lies in the open disk `ball 0 R`. -/
theorem closure_numericalRange_subset_ball_of_norm_lt (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) R := by
  have h1 : numericalRange A ⊆ Metric.closedBall (0 : ℂ) ‖A‖ := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_of_mem_numericalRange A hz
  exact (closure_minimal h1 Metric.isClosed_closedBall).trans
    (Metric.closedBall_subset_ball hR)

/-- The un-normalized circle Cauchy identity `∫₀^{2π} γ'(t) • R_A(γ(t)) dt = 2πi • 1` for
`γ = circleMap 0 R`, `‖A‖ < R`. -/
theorem intervalIntegral_deriv_circleMap_smul_resolvent_eq (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap 0 R) t • resolvent A (circleMap 0 R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have h := normalized_circleIntegral_resolvent_eq_one A hR
  have h2πi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  rw [inv_smul_eq_iff₀ h2πi] at h
  exact h

/-- **Circle-model symmetrized Crouzeix–Palencia bound** for `‖A‖ < R`, given the double-layer
representation of `p(A) + G†`: `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ R} ‖p(z)‖`. -/
theorem norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap 0 R t) •
        ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t)))) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation A
    ((norm_nonneg A).trans hR.le) (closure_numericalRange_subset_ball_of_norm_lt A hR) p G hrep
    (intervalIntegral_deriv_circleMap_smul_resolvent_eq A hR)

/-! ### The unconditional disk-model bound -/

/-- **Disk-model symmetrized Crouzeix–Palencia bound.** For `‖A‖ < R` and the auxiliary operator
`G` of the disk `ball 0 R`, `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ R} ‖p(z)‖`. -/
theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hOmega : closure (numericalRange A) ⊆ (SmoothJordanDomain.ball 0 R hRpos).carrier :=
    closure_numericalRange_subset_ball_of_norm_lt A hR
  have hCauchy : aeval A p = (2 * (Real.pi : ℂ) * I)⁻¹ •
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
        (SmoothJordanDomain.ball 0 R hRpos).boundaryParam :=
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p).symm
  have hrep := aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    A (SmoothJordanDomain.ball 0 R hRpos) p hOmega hCauchy
  exact norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt A hR p _ hrep

/-! ### The disk-model Crouzeix–Palencia inequality, given the auxiliary-operator value -/

/-- **Disk-model Crouzeix–Palencia inequality**, given the value of the disk auxiliary operator:
if `‖A‖ < R` and the conjugate-polynomial auxiliary operator of `ball 0 R` equals
`star (p.eval 0) • 1`, then `‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖`. -/
theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X])
    (hG : crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p =
      star (p.eval 0) • (1 : E →L[ℂ] E)) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds (aeval A p) _
    (norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le A hR p)
    (norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one A
      ((norm_nonneg A).trans_lt hR) hR.le p _ hG)

/-! ### The unconditional disk-model Crouzeix–Palencia inequality -/

/-- **Disk-model Crouzeix–Palencia inequality.** If `‖A‖ < R`, then for every polynomial `p`,
`‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖`. -/
theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) :=
  norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq A hR p
    (crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one A hR p)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
