/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleCauchy
public import LeanPool.OperatorTheory.Operator.Crouzeix.CircleSymmetrized
public import LeanPool.OperatorTheory.Operator.Crouzeix.AffinePolynomial

/-!
# Circle Cauchy formulas under spectral enclosure (L4.2 support)

`CircleCauchy.lean` proves the operator Cauchy formulas on a circle `C(0, R)` under the
operator-norm hypothesis `‖A‖ < R` (Neumann series).  Here they are transferred to any circle
`C(0, r)` whose open disk contains the spectrum: the integrand `z ↦ p(z) • R_A(z)` is holomorphic
on the resolvent set, which contains the closed annulus `{r ≤ |z| ≤ R}` when `σ(A) ⊆ ball 0 r`, so
Mathlib's concentric-annulus Cauchy theorem
(`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`) identifies the integral
over `C(0, r)` with the one over the Neumann circle `C(0, ‖A‖ + r)`.

Since `σ(A) ⊆ closure W(A)` (L2.2), this yields the symmetrized Crouzeix–Palencia estimate for
the disk under the *numerical-range* hypothesis `closure W(A) ⊆ ball 0 r`, replacing the
operator-norm enclosure of `CircleSymmetrized.lean`.

## Main declarations

* `circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball`,
  `circleIntegral_resolvent_eq_of_spectrum_subset_ball` — annulus deformation of the resolvent
  kernels (any center, `0 < r ≤ R`).
* `normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball`,
  `circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball` — the Cauchy formulas
  on `C(0, r)` for `σ(A) ⊆ ball 0 r`.
* `norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball`
  — `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ r} ‖p(z)‖` whenever `closure (numericalRange A) ⊆ ball 0 r`.
* `circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball` — the deformation for a general
  scalar weight `g` holomorphic off the disk, and
  `normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball` — vanishing of
  the negative Laurent modes of the resolvent under spectral enclosure.
* `circleIntegral_eval_smul_resolvent_eq_center`,
  `normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt`,
  `normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center`,
  `circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center` — the same
  formulas on a circle `C(c, r)` with arbitrary center, and
  `norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball_center`
  — the symmetrized bound for an arbitrary open disk containing `closure (numericalRange A)`.

The product side of the Crouzeix–Palencia argument is *not* upgraded here: the disk product bound
of `CircleProduct.lean` uses von Neumann's inequality, which needs `‖A‖ ≤ r`.
-/

@[expose] public section

open Complex Polynomial spectrum
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Points outside an open disk containing the spectrum lie in the resolvent set. -/
theorem mem_resolventSet_of_notMem_ball_of_spectrum_subset (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) {z : ℂ} (hz : z ∉ Metric.ball c r) :
    z ∈ resolventSet ℂ A := by
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  exact fun h => hz (hσ h)

/-- `z ↦ p(z) • R_A(z)` is differentiable at every point of the resolvent set. -/
theorem differentiableAt_eval_smul_resolvent (A : E →L[ℂ] E) (p : ℂ[X]) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    DifferentiableAt ℂ (fun w : ℂ => p.eval w • resolvent A w) z :=
  (p.differentiable z).smul (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt

/-- **Cauchy deformation for the resolvent kernel.** If the spectrum lies in `ball c r` and
`0 < r ≤ R`, the circle integrals of `p(z) • R_A(z)` over `C(c, r)` and `C(c, R)` agree. -/
theorem circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact (differentiableAt_eval_smul_resolvent A p
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ
        hz.2)).continuousAt.continuousWithinAt
  · intro z hz
    refine differentiableAt_eval_smul_resolvent A p
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ ?_)
    intro hzr
    exact hz.1.2 (Metric.ball_subset_closedBall hzr)

/-- The same deformation for the bare resolvent `z ↦ R_A(z)`. -/
theorem circleIntegral_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = circleIntegral (resolvent A) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ
        hz.2)).continuousAt.continuousWithinAt
  · intro z hz
    refine (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ ?_)).differentiableAt
    intro hzr
    exact hz.1.2 (Metric.ball_subset_closedBall hzr)

/-- **Circle Cauchy formula under spectral enclosure**: if `σ(A) ⊆ ball 0 r`, then
`(2πi)⁻¹ ∮_{|z| = r} p(z) R_A(z) dz = p(A)`. -/
theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) 0 r = aeval A p := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  rw [circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ p]
  exact normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p

/-- The un-normalized resolvent identity `∮_{|z| = r} R_A(z) dz = 2πi • 1` under spectral
enclosure. -/
theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) :
    circleIntegral (resolvent A) 0 r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  rw [circleIntegral_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one A hR

/-- **Symmetrized Crouzeix–Palencia bound under the numerical-range hypothesis.** If the closure
of the numerical range lies in the open disk `ball 0 r`, then for the auxiliary operator `G` of
that disk, `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ r} ‖p(z)‖`. -/
theorem norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 r hr) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have hOmega : closure (numericalRange A) ⊆ (SmoothJordanDomain.ball 0 r hr).carrier := hW
  have hCauchy : aeval A p = (2 * (Real.pi : ℂ) * I)⁻¹ •
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
        (SmoothJordanDomain.ball 0 r hr).boundaryParam :=
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball A hr hσ p).symm
  have hrep := aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    A (SmoothJordanDomain.ball 0 r hr) p hOmega hCauchy
  exact norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation A hr.le hW p _ hrep
    (circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball A hr hσ)

/-! ### General scalar weights and the negative Laurent modes -/

/-- Annulus deformation for a scalar-weighted resolvent kernel `g z • R_A z`, where `g` is
differentiable off the disk `ball c r` containing the spectrum. -/
theorem circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    {g : ℂ → ℂ} (hg : ∀ z, z ∉ Metric.ball c r → DifferentiableAt ℂ g z) :
    circleIntegral (fun z : ℂ => g z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => g z • resolvent A z) c R := by
  refine (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) Set.countable_empty ?_ ?_).symm
  · intro z hz
    exact ((hg z hz.2).smul (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz.2)).differentiableAt
      ).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∉ Metric.ball c r := fun h => hz.1.2 (Metric.ball_subset_closedBall h)
    exact (hg z hz').smul (spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hz')).differentiableAt

/-- Under spectral enclosure `σ(A) ⊆ ball 0 r`, the negative Laurent modes of the resolvent
vanish: `(2πi)⁻¹ ∮_{|z| = r} z⁻ⁿ • R_A(z) dz = 0` for `n ≥ 1`. -/
theorem normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 r = 0 := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  have hg : ∀ z : ℂ, z ∉ Metric.ball (0 : ℂ) r → DifferentiableAt ℂ (fun z : ℂ => z⁻¹ ^ n) z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz (Metric.mem_ball_self hr)
    exact (differentiableAt_inv hz0).pow n
  rw [circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ hg]
  exact normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero A hR n hn

/-! ### Arbitrary centers -/

/-- Translating a resolvent circle integral to the centered circle: the integral of
`p(z) • R_A(z)` over `C(c, R)` is the integral of `p(w + c) • R_{A - c}(w)` over `C(0, R)`. -/
theorem circleIntegral_eval_smul_resolvent_eq_center (A : E →L[ℂ] E) (c : ℂ) (R : ℝ) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R =
      circleIntegral (fun w : ℂ => (p.affineComposition 1 c).eval w •
        resolvent (A - c • (1 : E →L[ℂ] E)) w) 0 R := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro t _
  have hmap : circleMap c R t = circleMap 0 R t + c := by
    rw [← circleMap_sub_center c R t]
    ring
  have hderiv : deriv (circleMap c R) t = deriv (circleMap 0 R) t := by
    rw [deriv_circleMap, deriv_circleMap]
  simp only [hderiv, hmap, eval_affineComposition, one_mul, resolvent_sub_smul_one_shift]

/-- The polynomial circle Cauchy formula on `C(c, R)` for `‖A - c • 1‖ < R`. -/
theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R = aeval A p := by
  rw [circleIntegral_eval_smul_resolvent_eq_center,
    normalized_circleIntegral_eval_smul_resolvent_eq_aeval (A - c • (1 : E →L[ℂ] E)) hA,
    aeval_affineComposition, one_smul, sub_add_cancel]

/-- The polynomial circle Cauchy formula on `C(c, r)` under spectral enclosure
`σ(A) ⊆ ball c r`. -/
theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r = aeval A p := by
  have hR : ‖A - c • (1 : E →L[ℂ] E)‖ < ‖A - c • (1 : E →L[ℂ] E)‖ + r := by linarith
  rw [circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg (A - c • (1 : E →L[ℂ] E))] :
      r ≤ ‖A - c • (1 : E →L[ℂ] E)‖ + r) hσ p]
  exact normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt A c hR p

/-- The resolvent mass identity on `C(c, r)` under spectral enclosure. -/
theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have hR : ‖A - c • (1 : E →L[ℂ] E)‖ < ‖A - c • (1 : E →L[ℂ] E)‖ + r := by linarith
  rw [circleIntegral_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg (A - c • (1 : E →L[ℂ] E))] :
      r ≤ ‖A - c • (1 : E →L[ℂ] E)‖ + r) hσ]
  exact circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt A c hR

/-- **Symmetrized Crouzeix–Palencia bound for an arbitrary disk containing the numerical range.**
If `closure W(A) ⊆ ball c r`, then for the auxiliary operator `G` of that disk,
`‖p(A) + G†‖ ≤ 2 * sup_{|z - c| ≤ r} ‖p(z)‖`. -/
theorem norm_aeval_add_star_auxiliary_ball_le_of_closedNumericalRange_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c r hr) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall c r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball c r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have hOmega : closure (numericalRange A) ⊆ (SmoothJordanDomain.ball c r hr).carrier := hW
  have hCauchy : aeval A p = (2 * (Real.pi : ℂ) * I)⁻¹ •
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
        (SmoothJordanDomain.ball c r hr).boundaryParam :=
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
      A hr hσ p).symm
  have hrep := aeval_add_star_crouzeixPolynomialAuxiliaryOperator_eq_doubleLayerIntegral_of_cauchy
    A (SmoothJordanDomain.ball c r hr) p hOmega hCauchy
  exact norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation A hr.le hW p _ hrep
    (circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center A hr hσ)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
