/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.AuxOperator
import LeanPool.OperatorTheory.Operator.SpectralSet.Normal

/-!
# Crouzeix--Palencia assembly from auxiliary-operator bounds

This file isolates two algebraic routes to the Crouzeix--Palencia constant.
The project-specific sharp-product route assumes that, for `F = p(A)`, an
auxiliary operator `G` satisfies

* `‖F + G⋆‖ ≤ 2m`, and
* `‖F G‖ ≤ m²`,

then the C⋆-identity gives the quadratic inequality
`‖F‖² ≤ 2m‖F‖ + m²`, hence `‖F‖ ≤ (1 + √2)m`.

This sharp product bound is not the invariant used in the published 2017
proof.  The Crouzeix--Palencia argument, in the shorter
Ransford--Schwenninger formulation, instead combines a contractive scalar
Cauchy-transform companion with an a priori finite norm `K` for the whole
functional calculus.  Its fourth-power bootstrap gives
`K⁴ ≤ 2K³ + K²`, hence the same constant.  Both algebraic endpoints are
formalized below; their distinct analytic hypotheses remain explicit.

## Main declarations

* `norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds` -- the C⋆-algebraic
  quadratic estimate.
* `norm_fourth_power_le_of_companion_calculus_bounds` -- the published
  Ransford--Schwenninger fourth-power bridge from a contractive companion and
  a global functional-calculus bound.
* `norm_fourth_power_le_of_polynomial_companion_calculus_bounds` -- the exact
  polynomial-companion specialization, including the multiplicative triple
  estimate from compact-set sup norms.
* `norm_fourth_power_le_of_tendsto_polynomial_companions` -- passage from
  uniformly contractive polynomial companions to their operator-norm limit.
* `le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq` -- the scalar fixed
  point which closes that bridge.
* `crouzeix_palencia_of_global_polynomial_bound_of_fourth_power` -- its exact
  polynomial spectral-set capstone.
* `four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub` -- the exact symmetric
  minus antisymmetric quadratic-form identity for the auxiliary product.
* `two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq` --
  the corresponding exact Hermitian decomposition of a separated remainder.
* `re_inner_mul_lower_iff_norm_adjoint_sub_sq_le` -- its sharp lower-bound
  reformulation as a relative skew contraction.
* `crouzeix_palencia_of_auxiliary_bounds` -- packages the estimate and the
  landed spectrum inclusion as a polynomial spectral-set result.
* `crouzeix_palencia_of_polynomial_auxiliary_bounds` -- specializes that
  package to the contour operator constructed in `AuxOperator.lean`.
* `crouzeix_palencia_of_isStarNormal` -- the sharper normal-operator branch.
-/

open scoped InnerProductSpace

private theorem le_one_add_sqrt_two_mul_of_sq_le {x m : ℝ} (hm : 0 ≤ m)
    (hquad : x ^ 2 ≤ 2 * m * x + m ^ 2) : x ≤ (1 + Real.sqrt 2) * m := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_one : 1 ≤ Real.sqrt 2 := by
    nlinarith only [hsqrt_sq, hsqrt_nonneg]
  by_contra hbound
  have hlt : (1 + Real.sqrt 2) * m < x := lt_of_not_ge hbound
  have hroot_nonneg : 0 ≤ (1 + Real.sqrt 2) * m :=
    mul_nonneg (add_nonneg zero_le_one hsqrt_nonneg) hm
  have hx_pos : 0 < x := hroot_nonneg.trans_lt hlt
  have hfirst : 0 < x - (1 + Real.sqrt 2) * m := sub_pos.mpr hlt
  have hsecond : 0 < x + (Real.sqrt 2 - 1) * m :=
    add_pos_of_pos_of_nonneg hx_pos (mul_nonneg (sub_nonneg.mpr hsqrt_one) hm)
  have hprod_pos :
      0 < (x - (1 + Real.sqrt 2) * m) * (x + (Real.sqrt 2 - 1) * m) :=
    mul_pos hfirst hsecond
  have hfactor :
      (x - (1 + Real.sqrt 2) * m) * (x + (Real.sqrt 2 - 1) * m) =
        x ^ 2 - 2 * m * x - m ^ 2 := by
    nlinarith only [hsqrt_sq]
  rw [hfactor] at hprod_pos
  nlinarith only [hquad, hprod_pos]

/-- The algebraic core of the Crouzeix--Palencia estimate.  The identity
`F F⋆ = F (F + G⋆)⋆ - F G`, the C⋆-identity, and the two assumed auxiliary
bounds give a quadratic inequality whose positive root is `(1 + √2) m`. -/
theorem norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m) (hprod : ‖F * G‖ ≤ m ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hm : 0 ≤ m := by
    nlinarith only [norm_nonneg (F + star G), hsymm]
  have hidentity : F * star F = F * star (F + star G) - F * G := by
    rw [star_add, star_star, mul_add, add_sub_cancel_right]
  have hbalance : ‖F‖ ^ 2 ≤ ‖F‖ * ‖F + star G‖ + ‖F * G‖ := by
    calc
      ‖F‖ ^ 2 = ‖F * star F‖ := by
        rw [CStarRing.norm_self_mul_star]
        ring
      _ = ‖F * star (F + star G) - F * G‖ := congrArg norm hidentity
      _ ≤ ‖F * star (F + star G)‖ + ‖F * G‖ := norm_sub_le _ _
      _ ≤ ‖F‖ * ‖star (F + star G)‖ + ‖F * G‖ :=
        add_le_add (norm_mul_le _ _) le_rfl
      _ = ‖F‖ * ‖F + star G‖ + ‖F * G‖ := by rw [norm_star]
  have hquad : ‖F‖ ^ 2 ≤ 2 * m * ‖F‖ + m ^ 2 := by
    calc
      ‖F‖ ^ 2 ≤ ‖F‖ * ‖F + star G‖ + ‖F * G‖ := hbalance
      _ ≤ ‖F‖ * (2 * m) + m ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hsymm (norm_nonneg F)) hprod
      _ = 2 * m * ‖F‖ + m ^ 2 := by ring
  exact le_one_add_sqrt_two_mul_of_sq_le hm hquad

/-- The exact C⋆-identity behind the short Ransford--Schwenninger version of
the Crouzeix--Palencia argument.  In the intended application `F = f(A)` and
`G = g(A)`, so multiplicativity identifies `F * G * F` with `(f g f)(A)`. -/
theorem mul_adjoint_fourth_power_eq_symmetrized_sub_triple
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) :
    F * star F * F * star F =
      F * star (F + star G) * F * star F - F * G * F * star F := by
  simp only [star_add, star_star]
  noncomm_ring

/-- The norm form of the Ransford--Schwenninger fourth-power identity.  It
replaces a sharp standalone bound on `F * G` by control of the multiplicative
triple `F * G * F`, which is what a global functional-calculus norm supplies. -/
theorem norm_fourth_power_le_symmetrized_mul_cube_add_triple_mul
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) :
    ‖F‖ ^ 4 ≤
      ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := by
  have hidentity := mul_adjoint_fourth_power_eq_symmetrized_sub_triple F G
  have hfour : ‖F‖ ^ 4 = ‖F * star F * F * star F‖ := by
    rw [show F * star F * F * star F =
        (F * star F) * star (F * star F) by
      simp only [star_mul, star_star]
      noncomm_ring]
    rw [CStarRing.norm_self_mul_star, CStarRing.norm_self_mul_star]
    ring
  have hfirst :
      ‖F * star (F + star G) * F * star F‖ ≤
        (‖F‖ * ‖star (F + star G)‖ * ‖F‖) * ‖star F‖ := by
    calc
      _ ≤ ‖F * star (F + star G) * F‖ * ‖star F‖ := norm_mul_le _ _
      _ ≤ (‖F * star (F + star G)‖ * ‖F‖) * ‖star F‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((‖F‖ * ‖star (F + star G)‖) * ‖F‖) * ‖star F‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          (norm_nonneg _)
  calc
    ‖F‖ ^ 4 = ‖F * star F * F * star F‖ := hfour
    _ = ‖F * star (F + star G) * F * star F - F * G * F * star F‖ :=
      congrArg norm hidentity
    _ ≤ ‖F * star (F + star G) * F * star F‖ +
        ‖F * G * F * star F‖ := norm_sub_le _ _
    _ ≤ (‖F‖ * ‖star (F + star G)‖ * ‖F‖) * ‖star F‖ +
        ‖F * G * F‖ * ‖star F‖ :=
      add_le_add hfirst (norm_mul_le _ _)
    _ = ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := by
      rw [norm_star, norm_star]
      ring

/-- If a functional calculus has an a priori norm bound `K`, the companion is
symmetrically bounded by `2m`, and multiplicativity plus companion contraction
bound `F G F` by `K m³`, then the published fourth-power estimate follows.
Taking `K` to be the best global calculus constant yields
`K⁴ ≤ 2K³ + K²`, whose positive fixed point is `1 + √2`. -/
theorem norm_fourth_power_le_of_companion_calculus_bounds
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hsymm : ‖F + star G‖ ≤ 2 * m) (hF : ‖F‖ ≤ K * m)
    (htriple : ‖F * G * F‖ ≤ K * m ^ 3) :
    ‖F‖ ^ 4 ≤ (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  have hbase := norm_fourth_power_le_symmetrized_mul_cube_add_triple_mul F G
  calc
    ‖F‖ ^ 4 ≤ ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := hbase
    _ ≤ (2 * m) * (K * m) ^ 3 + (K * m ^ 3) * (K * m) := by
      gcongr
    _ = (2 * K ^ 3 + K ^ 2) * m ^ 4 := by ring

/-! ### Polynomial multiplicative triples -/

/-- Polynomial sup norms are submultiplicative on compact sets.  Compactness
supplies the boundedness needed to compare each point evaluation with the
conditionally complete supremum used by `polynomialSupNorm`. -/
theorem polynomialSupNorm_mul_le_of_isCompact
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q) S ≤
      polynomialSupNorm p S * polynomialSupNorm q S := by
  unfold polynomialSupNorm
  apply ciSup_le
  intro z
  by_cases hz : z ∈ S
  · have : Nonempty (z ∈ S) := ⟨hz⟩
    apply ciSup_le
    intro hz'
    rw [Polynomial.eval_mul, norm_mul]
    exact mul_le_mul
      (norm_eval_le_polynomialSupNorm p
        (bddAbove_norm_eval_image_of_isCompact p hS) hz')
      (norm_eval_le_polynomialSupNorm q
        (bddAbove_norm_eval_image_of_isCompact q hS) hz')
      (norm_nonneg _) (polynomialSupNorm_nonneg p S)
  · have : IsEmpty (z ∈ S) := ⟨fun h ↦ hz h⟩
    rw [iSup_of_empty', Real.sSup_empty]
    exact mul_nonneg (polynomialSupNorm_nonneg p S)
      (polynomialSupNorm_nonneg q S)

/-- The compact-set sup norm of the multiplicative triple `p*q*p` is at
most `‖p‖²‖q‖`. -/
theorem polynomialSupNorm_mul_mul_le_of_isCompact
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q * p) S ≤
      polynomialSupNorm p S ^ 2 * polynomialSupNorm q S := by
  calc
    polynomialSupNorm (p * q * p) S ≤
        polynomialSupNorm (p * q) S * polynomialSupNorm p S :=
      polynomialSupNorm_mul_le_of_isCompact hS (p * q) p
    _ ≤ (polynomialSupNorm p S * polynomialSupNorm q S) *
        polynomialSupNorm p S :=
      mul_le_mul_of_nonneg_right
        (polynomialSupNorm_mul_le_of_isCompact hS p q)
        (polynomialSupNorm_nonneg p S)
    _ = polynomialSupNorm p S ^ 2 * polynomialSupNorm q S := by ring

/-- The nonnegative fixed point of the Ransford--Schwenninger fourth-power
bootstrap is at most `1 + √2`. -/
theorem le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
    {K : ℝ} (hK : 0 ≤ K) (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2) :
    K ≤ 1 + Real.sqrt 2 := by
  by_cases hKzero : K = 0
  · rw [hKzero]
    exact add_nonneg zero_le_one (Real.sqrt_nonneg 2)
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
  have hKsqpos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hquad : K ^ 2 ≤ 2 * K + 1 := by
    nlinarith only [hfour, hKsqpos]
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  by_contra hbound
  have hlt : 1 + Real.sqrt 2 < K := lt_of_not_ge hbound
  nlinarith only [hquad, hsqrt_sq, hsqrt_nonneg, hlt]

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem isCompact_closure_numericalRange_palencia (A : E →L[ℂ] E) :
    IsCompact (closure (numericalRange A)) := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact hbounded.isCompact_closure

/-- A global polynomial-calculus bound controls the evaluated multiplicative
triple by the product of the three compact-set polynomial sup norms.  This is
the algebraic approximation bridge needed when the scalar Cauchy companion
has itself been represented by a polynomial. -/
theorem norm_polynomial_calculus_triple_le
    (A : E →L[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q * Polynomial.aeval A p‖ ≤
      K * (polynomialSupNorm p S ^ 2 * polynomialSupNorm q S) := by
  calc
    ‖Polynomial.aeval A p * Polynomial.aeval A q * Polynomial.aeval A p‖ =
        ‖Polynomial.aeval A (p * q * p)‖ := by
      rw [Polynomial.aeval_mul, Polynomial.aeval_mul]
    _ ≤ K * polynomialSupNorm (p * q * p) S := hcalc _
    _ ≤ K * (polynomialSupNorm p S ^ 2 * polynomialSupNorm q S) :=
      mul_le_mul_of_nonneg_left
        (polynomialSupNorm_mul_mul_le_of_isCompact hS p q) hK

variable [CompleteSpace E]

/-- The published fourth-power estimate specialized to a polynomial
companion `q`.  A global calculus constant bounds both `p(A)` and the
multiplicative triple `(p*q*p)(A)`; compact-set sup-norm
submultiplicativity and `‖p‖ₛ,‖q‖ₛ ≤ m` give the required `K m³` bound.

The analytic Crouzeix--Palencia companion need not be a polynomial, so using
this theorem for that companion still requires a norm-preserving polynomial
approximation argument. -/
theorem norm_fourth_power_le_of_polynomial_companion_calculus_bounds
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ)
    (hp : polynomialSupNorm p S ≤ m)
    (hq : polynomialSupNorm q S ≤ m)
    (hsymm : ‖Polynomial.aeval A p + star (Polynomial.aeval A q)‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  apply norm_fourth_power_le_of_companion_calculus_bounds
    (Polynomial.aeval A p) (Polynomial.aeval A q) hK hm hsymm
  · exact (hcalc p).trans (mul_le_mul_of_nonneg_left hp hK)
  · refine (norm_polynomial_calculus_triple_le A hK hS hcalc p q).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    have hp0 := polynomialSupNorm_nonneg p S
    have hq0 := polynomialSupNorm_nonneg q S
    calc
      polynomialSupNorm p S ^ 2 * polynomialSupNorm q S ≤
          m ^ 2 * polynomialSupNorm q S := by gcongr
      _ ≤ m ^ 2 * m := by gcongr
      _ = m ^ 3 := by ring

/-- Polynomial companion estimates pass to an operator-norm limit.  If
`q n (A) → G` and every `q n` has sup norm at most `m`, then the global
polynomial-calculus bound controls `p(A) G p(A)` by `K m³`.

This statement isolates the exact approximation interface required for a
holomorphic Cauchy companion: construction of the approximants and their
uniform scalar bound are analytic inputs, while the limiting operator
estimate is purely functional-analytic. -/
theorem norm_triple_le_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G)) :
    ‖Polynomial.aeval A p * G * Polynomial.aeval A p‖ ≤ K * m ^ 3 := by
  have htripleLim : Filter.Tendsto
      (fun n ↦ Polynomial.aeval A p * Polynomial.aeval A (q n) *
        Polynomial.aeval A p) Filter.atTop
      (nhds (Polynomial.aeval A p * G * Polynomial.aeval A p)) :=
    (tendsto_const_nhds.mul hlim).mul tendsto_const_nhds
  apply le_of_tendsto htripleLim.norm
  filter_upwards with n
  refine (norm_polynomial_calculus_triple_le A hK hS hcalc p (q n)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hK
  have hp0 := polynomialSupNorm_nonneg p S
  have hq0 := polynomialSupNorm_nonneg (q n) S
  have hqn := hq n
  calc
    polynomialSupNorm p S ^ 2 * polynomialSupNorm (q n) S ≤
        m ^ 2 * polynomialSupNorm (q n) S := by gcongr
    _ ≤ m ^ 2 * m := by gcongr
    _ = m ^ 3 := by ring

/-- The published fourth-power estimate for an operator companion obtained as
the operator-norm limit of uniformly sup-norm-bounded polynomial companions.
This packages the limiting step needed after a norm-preserving polynomial
approximation theorem for the scalar Cauchy companion. -/
theorem norm_fourth_power_le_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G))
    (hsymm : ‖Polynomial.aeval A p + star G‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  apply norm_fourth_power_le_of_companion_calculus_bounds
    (Polynomial.aeval A p) G hK hm hsymm
  · exact (hcalc p).trans (mul_le_mul_of_nonneg_left hp hK)
  · exact norm_triple_le_of_tendsto_polynomial_companions
      A hK hS hcalc p hp G q hq hlim

/-- A nonnegative global polynomial-calculus constant satisfying the
Ransford--Schwenninger fourth-power inequality is at most `1 + √2`, and hence
gives the exact Crouzeix--Palencia polynomial spectral-set conclusion. -/
theorem crouzeix_palencia_of_global_polynomial_bound_of_fourth_power
    (A : E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2)
    (hcalc : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  refine ⟨spectrum_subset_closure_numericalRange A, ?_⟩
  intro p
  have hfixed :=
    le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq hK hfour
  exact (hcalc p).trans (mul_le_mul_of_nonneg_right hfixed
    (polynomialSupNorm_nonneg p (closure (numericalRange A))))

omit [CompleteSpace E] in
/-- On any control set containing the spectrum, a finite polynomial-calculus
bound together with a uniform fourth-power improvement closes the
best-constant bootstrap.  The proof takes the supremum of all normalized
polynomial-calculus ratios, proves that this supremum is itself an admissible
global constant, and applies the improvement at that exact constant. -/
theorem
    isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
    (A : E →L[ℂ] E) (S : Set ℂ) (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S)
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p S ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by
  let m : Polynomial ℂ → ℝ := fun p ↦
    polynomialSupNorm p S
  let ratio : Polynomial ℂ → ℝ := fun p ↦
    if m p = 0 then 0 else ‖Polynomial.aeval A p‖ / m p
  let ratios : Set ℝ := Set.range ratio
  let K : ℝ := sSup ratios
  obtain ⟨K₀, hK₀, hcalc₀⟩ := hfinite
  have hm_nonneg (p : Polynomial ℂ) : 0 ≤ m p := by
    exact polynomialSupNorm_nonneg p S
  have hratio_nonneg (p : Polynomial ℂ) : 0 ≤ ratio p := by
    by_cases hp : m p = 0
    · simp only [ratio, hp, ite_eq_left, le_rfl]
    · simp only [ratio, hp, ite_false]
      exact div_nonneg (norm_nonneg _) (hm_nonneg p)
  have hratios_nonempty : ratios.Nonempty := Set.range_nonempty ratio
  have hratios_bdd : BddAbove ratios := by
    refine ⟨K₀, ?_⟩
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    by_cases hp : m p = 0
    · simp only [ratio, hp, ite_eq_left]
      exact hK₀
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      simp only [ratio, hp, ite_false]
      exact (div_le_iff₀ hmp).2 (hcalc₀ p)
  have hratio_le (p : Polynomial ℂ) : ratio p ≤ K := by
    exact le_csSup hratios_bdd (Set.mem_range_self p)
  have hK : 0 ≤ K := by
    exact (hratio_nonneg 0).trans (hratio_le 0)
  have hcalc : ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * m p := by
    intro p
    by_cases hp : m p = 0
    · have hcalc₀' : ‖Polynomial.aeval A p‖ ≤ K₀ * m p := by
        simpa only [m] using hcalc₀ p
      have hnorm : ‖Polynomial.aeval A p‖ = 0 := by
        apply le_antisymm
        · rw [hp, mul_zero] at hcalc₀'
          exact hcalc₀'
        · exact norm_nonneg _
      rw [hp, mul_zero, hnorm]
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      apply (div_le_iff₀ hmp).1
      simpa only [ratio, hp, ite_false] using hratio_le p
  let C : ℝ := 2 * K ^ 3 + K ^ 2
  let B : ℝ := Real.sqrt (Real.sqrt C)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBpow : B ^ 4 = C := by
    calc
      B ^ 4 = (Real.sqrt C) ^ 2 := by
        dsimp only [B]
        rw [show Real.sqrt (Real.sqrt C) ^ 4 =
          (Real.sqrt (Real.sqrt C) ^ 2) ^ 2 by ring,
          Real.sq_sqrt (Real.sqrt_nonneg C)]
      _ = C := Real.sq_sqrt hC
  have hratios_le_B : ∀ y ∈ ratios, y ≤ B := by
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    by_cases hp : m p = 0
    · simp only [ratio, hp, ite_eq_left]
      exact hB
    · have hmp : 0 < m p := lt_of_le_of_ne (hm_nonneg p) (Ne.symm hp)
      have hpow : ratio p ^ 4 ≤ C := by
        calc
          ratio p ^ 4 = ‖Polynomial.aeval A p‖ ^ 4 / m p ^ 4 := by
            simp only [ratio, hp, ite_false, div_pow]
          _ ≤ C := (div_le_iff₀ (pow_pos hmp 4)).2 (hfour K hK hcalc p)
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hB
      rwa [hBpow]
  have hKleB : K ≤ B := csSup_le hratios_nonempty hratios_le_B
  have hKfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2 := by
    change K ^ 4 ≤ C
    calc
      K ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hK hKleB 4
      _ = C := hBpow
  refine ⟨hspectrum, ?_⟩
  intro p
  have hfixed :=
    le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq hK hKfour
  exact (hcalc p).trans (mul_le_mul_of_nonneg_right hfixed
    (polynomialSupNorm_nonneg p S))

/-- A finite polynomial-calculus bound on the closed numerical range,
together with a uniform fourth-power improvement, gives the exact
Crouzeix--Palencia conclusion. -/
theorem
    crouzeix_palencia_of_finite_global_bound_of_uniform_fourth_power_improvement
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p (closure (numericalRange A)) ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  exact
    isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
      A (closure (numericalRange A))
        (spectrum_subset_closure_numericalRange A) hfinite hfour

/-- On a compact control set containing the spectrum, a finite global
polynomial-calculus bound and uniformly contractive polynomial approximants
to each auxiliary companion imply the `(1 + √2)` spectral-set bound. -/
theorem
    isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (S : Set ℂ) (hS : IsCompact S)
    (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p S)
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) S ≤ polynomialSupNorm p S) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p S) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by
  apply
    isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
      A S hspectrum hfinite
  intro K hK hcalc p
  obtain ⟨G, q, hq, hlim, hsymm⟩ := hcompanion p
  exact norm_fourth_power_le_of_tendsto_polynomial_companions
    A hK (polynomialSupNorm_nonneg p S) hS hcalc p le_rfl
      G q hq hlim hsymm

/-- A finite global polynomial-calculus bound and uniformly contractive
polynomial approximants to each auxiliary companion imply the exact
Crouzeix--Palencia conclusion.  The operator-norm limit supplies the
multiplicative triple estimate, while the preceding best-constant bootstrap
globalizes its per-polynomial fourth-power improvement. -/
theorem
    crouzeix_palencia_of_finite_global_bound_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) (closure (numericalRange A)) ≤
          polynomialSupNorm p (closure (numericalRange A))) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  exact
    isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
      A (closure (numericalRange A))
        (isCompact_closure_numericalRange_palencia A)
        (spectrum_subset_closure_numericalRange A) hfinite hcompanion

/-- The Crouzeix--Palencia balance only needs the product estimate on
unit-vector quadratic forms.  Evaluating
`F F† = F (F + G†)† - F G` at a unit vector bounds `‖F† x‖`; normalization
then recovers the operator norm.  Thus a numerical-radius bound on `F G`
is sufficient for the exact `(1 + √2)` constant. -/
theorem norm_le_one_add_sqrt_two_mul_of_auxiliary_inner_bounds
    (F G : E →L[ℂ] E) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m)
    (hprod : ∀ x : E, ‖x‖ = 1 → ‖⟪x, (F * G) x⟫_ℂ‖ ≤ m ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hm : 0 ≤ m := by
    nlinarith only [norm_nonneg (F + star G), hsymm]
  have hC : 0 ≤ (1 + Real.sqrt 2) * m :=
    mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2)) hm
  have hidentity : F * star F = F * star (F + star G) - F * G := by
    rw [star_add, star_star, mul_add, add_sub_cancel_right]
  have hunit : ∀ x : E, ‖x‖ = 1 →
      ‖(star F) x‖ ≤ (1 + Real.sqrt 2) * m := by
    intro x hx
    have hinnerSelf : ⟪(star F) x, (star F) x⟫_ℂ =
        ⟪x, (F * star F) x⟫_ℂ := by
      rw [mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_left F ((star F) x) x
    have hfirst : ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ ≤
        2 * m * ‖(star F) x‖ := by
      rw [mul_apply_eq_comp]
      rw [← ContinuousLinearMap.adjoint_inner_left F]
      calc
        ‖⟪(star F) x, star (F + star G) x⟫_ℂ‖ ≤
            ‖(star F) x‖ * ‖star (F + star G) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by
          calc
            ‖(star F) x‖ * ‖star (F + star G) x‖ ≤
                ‖(star F) x‖ * (‖star (F + star G)‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_left ((star (F + star G)).le_opNorm x)
                (norm_nonneg _)
            _ = ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by ring
        _ ≤ ‖(star F) x‖ * (2 * m) * 1 := by
          rw [norm_star, hx]
          gcongr
        _ = 2 * m * ‖(star F) x‖ := by ring
    have hquad : ‖(star F) x‖ ^ 2 ≤
        2 * m * ‖(star F) x‖ + m ^ 2 := by
      calc
        ‖(star F) x‖ ^ 2 = ‖⟪(star F) x, (star F) x⟫_ℂ‖ := by
          simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
            abs_of_nonneg (norm_nonneg _)]
        _ = ‖⟪x, (F * star F) x⟫_ℂ‖ := congrArg norm hinnerSelf
        _ = ‖⟪x, (F * star (F + star G) - F * G) x⟫_ℂ‖ := by rw [hidentity]
        _ ≤ ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ +
            ‖⟪x, (F * G) x⟫_ℂ‖ := by
          rw [sub_apply, inner_sub_right]
          exact norm_sub_le _ _
        _ ≤ 2 * m * ‖(star F) x‖ + m ^ 2 := add_le_add hfirst (hprod x hx)
    exact le_one_add_sqrt_two_mul_of_sq_le hm hquad
  rw [← norm_star F]
  apply ContinuousLinearMap.opNorm_le_bound' (star F) hC
  intro x hx
  have hxpos : 0 < ‖x‖ := (norm_pos_iff.mpr (norm_ne_zero_iff.mp hx))
  let y : E := ((‖x‖ : ℂ)⁻¹) • x
  have hy : ‖y‖ = 1 := norm_inv_norm_smul (norm_ne_zero_iff.mp hx)
  have hFy := hunit y hy
  have hnorm : ‖(star F) y‖ = ‖x‖⁻¹ * ‖(star F) x‖ := by
    simp only [y, map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hxpos]
  rw [hnorm] at hFy
  calc
    ‖(star F) x‖ = ‖x‖ * (‖x‖⁻¹ * ‖(star F) x‖) := by
      field_simp
    _ ≤ ‖x‖ * ((1 + Real.sqrt 2) * m) :=
      mul_le_mul_of_nonneg_left hFy (norm_nonneg x)
    _ = (1 + Real.sqrt 2) * m * ‖x‖ := by ring

/-- The Hermitian part of an auxiliary product is exactly the difference
between the squared symmetric and antisymmetric components.  This is the
operator-vector form of the polarization identity
`4 Re(FG) = (F† + G)†(F† + G) - (F† - G)†(F† - G)`; it requires no
commutation hypothesis. -/
theorem four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub
    (F G : E →L[ℂ] E) (x : E) :
    4 * RCLike.re ⟪x, (F * G) x⟫_ℂ =
      ‖(star F + G) x‖ ^ 2 - ‖(star F - G) x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),
    ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp only [add_apply, sub_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, map_add, map_sub]
  have hcross : ⟪star F x, G x⟫_ℂ = ⟪x, (F * G) x⟫_ℂ := by
    change ⟪ContinuousLinearMap.adjoint F x, G x⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp]
  rw [hcross]
  have hcross' : RCLike.re ⟪G x, star F x⟫_ℂ =
      RCLike.re ⟪x, (F * G) x⟫_ℂ := by
    rw [inner_re_symm]
    exact congrArg RCLike.re hcross
  rw [hcross']
  ring

/-- If an auxiliary product is separated as `F G = H - Q`, then twice the
Hermitian remainder is exactly twice the Hermitian main term, minus the
symmetric square, plus the antisymmetric square.  Thus positivity of the
double-layer/Kadison part and control of the skew part are distinct pieces;
no triangle inequality or commutation hypothesis enters this identity. -/
theorem two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq
    (F G H Q : E →L[ℂ] E) (hdecomp : F * G = H - Q) :
    (2 : ℂ) • (Q + star Q) =
      (2 : ℂ) • (H + star H) -
        (F + star G) * (star F + G) +
        (F - star G) * (star F - G) := by
  have hH : H = F * G + Q := by
    rw [hdecomp]
    module
  rw [hH]
  simp only [two_smul, star_add, star_mul]
  noncomm_ring

/-- The one-sided product estimate used in the Palencia balance is exactly a
relative bound on the antisymmetric auxiliary component. -/
theorem re_inner_mul_lower_iff_norm_adjoint_sub_sq_le
    (F G : E →L[ℂ] E) (x : E) (m : ℝ) :
    -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ ↔
      ‖(star F - G) x‖ ^ 2 ≤ ‖(star F + G) x‖ ^ 2 + 4 * m ^ 2 := by
  have hidentity := four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub F G x
  constructor <;> intro hbound <;> nlinarith only [hidentity, hbound]

/-- The Crouzeix--Palencia balance only uses the lower real part of the
auxiliary product.  In the identity
`F F† = F (F + G†)† - F G`, an upper bound for `F F†` requires only
`-m² ≤ re ⟪x, F G x⟫` on unit vectors.  No bound on the modulus, numerical
radius, or operator norm of `F G` is needed. -/
theorem norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
    (F G : E →L[ℂ] E) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m)
    (hprod : ∀ x : E, ‖x‖ = 1 →
      -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hm : 0 ≤ m := by
    nlinarith only [norm_nonneg (F + star G), hsymm]
  have hC : 0 ≤ (1 + Real.sqrt 2) * m :=
    mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2)) hm
  have hidentity : F * star F = F * star (F + star G) - F * G := by
    rw [star_add, star_star, mul_add, add_sub_cancel_right]
  have hunit : ∀ x : E, ‖x‖ = 1 →
      ‖(star F) x‖ ≤ (1 + Real.sqrt 2) * m := by
    intro x hx
    have hinnerSelf : ⟪(star F) x, (star F) x⟫_ℂ =
        ⟪x, (F * star F) x⟫_ℂ := by
      rw [mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_left F ((star F) x) x
    have hfirst : ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ ≤
        2 * m * ‖(star F) x‖ := by
      rw [mul_apply_eq_comp]
      rw [← ContinuousLinearMap.adjoint_inner_left F]
      calc
        ‖⟪(star F) x, star (F + star G) x⟫_ℂ‖ ≤
            ‖(star F) x‖ * ‖star (F + star G) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by
          calc
            ‖(star F) x‖ * ‖star (F + star G) x‖ ≤
                ‖(star F) x‖ * (‖star (F + star G)‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_left ((star (F + star G)).le_opNorm x)
                (norm_nonneg _)
            _ = ‖(star F) x‖ * ‖star (F + star G)‖ * ‖x‖ := by ring
        _ ≤ ‖(star F) x‖ * (2 * m) * 1 := by
          rw [norm_star, hx]
          gcongr
        _ = 2 * m * ‖(star F) x‖ := by ring
    have hquad : ‖(star F) x‖ ^ 2 ≤
        2 * m * ‖(star F) x‖ + m ^ 2 := by
      calc
        ‖(star F) x‖ ^ 2 = RCLike.re ⟪(star F) x, (star F) x⟫_ℂ := by
          rw [inner_self_eq_norm_sq]
        _ = RCLike.re ⟪x, (F * star F) x⟫_ℂ := congrArg RCLike.re hinnerSelf
        _ = RCLike.re ⟪x,
            (F * star (F + star G) - F * G) x⟫_ℂ := by rw [hidentity]
        _ = RCLike.re ⟪x, (F * star (F + star G)) x⟫_ℂ -
            RCLike.re ⟪x, (F * G) x⟫_ℂ := by
          rw [sub_apply, inner_sub_right, map_sub]
        _ ≤ ‖⟪x, (F * star (F + star G)) x⟫_ℂ‖ + m ^ 2 := by
          have hre := RCLike.re_le_norm ⟪x, (F * star (F + star G)) x⟫_ℂ
          nlinarith only [hre, hprod x hx]
        _ ≤ 2 * m * ‖(star F) x‖ + m ^ 2 := add_le_add hfirst le_rfl
    exact le_one_add_sqrt_two_mul_of_sq_le hm hquad
  rw [← norm_star F]
  apply ContinuousLinearMap.opNorm_le_bound' (star F) hC
  intro x hx
  have hxpos : 0 < ‖x‖ := (norm_pos_iff.mpr (norm_ne_zero_iff.mp hx))
  let y : E := ((‖x‖ : ℂ)⁻¹) • x
  have hy : ‖y‖ = 1 := norm_inv_norm_smul (norm_ne_zero_iff.mp hx)
  have hFy := hunit y hy
  have hnorm : ‖(star F) y‖ = ‖x‖⁻¹ * ‖(star F) x‖ := by
    simp only [y, map_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hxpos]
  rw [hnorm] at hFy
  calc
    ‖(star F) x‖ = ‖x‖ * (‖x‖⁻¹ * ‖(star F) x‖) := by
      field_simp
    _ ≤ ‖x‖ * ((1 + Real.sqrt 2) * m) :=
      mul_le_mul_of_nonneg_left hFy (norm_nonneg x)
    _ = (1 + Real.sqrt 2) * m * ‖x‖ := by ring

/-- A relative contraction of the antisymmetric auxiliary component is the
exact extra input needed beyond the symmetrized bound.  By the polarization
identity above, bounding `‖(F† - G)x‖²` by `‖(F† + G)x‖² + 4m²` is equivalent
to the signed product estimate used by the sharp Palencia balance. -/
theorem norm_le_one_add_sqrt_two_mul_of_auxiliary_skew_bounds
    (F G : E →L[ℂ] E) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m)
    (hskew : ∀ x : E, ‖x‖ = 1 →
      ‖(star F - G) x‖ ^ 2 ≤ ‖(star F + G) x‖ ^ 2 + 4 * m ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  apply norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
    F G hsymm
  intro x hx
  exact (re_inner_mul_lower_iff_norm_adjoint_sub_sq_le F G x m).mpr
    (hskew x hx)

/-- If every polynomial admits an auxiliary operator with the symmetrized
bound and the sharp product bound only on unit-vector quadratic forms, then
the closed numerical range is a `(1 + √2)`-polynomial spectral set. -/
theorem crouzeix_palencia_of_auxiliary_inner_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ∀ x : E, ‖x‖ = 1 →
        ‖⟪x, (Polynomial.aeval A p * G) x⟫_ℂ‖ ≤
          polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨G, hsymm, hprod⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_auxiliary_inner_bounds
      (Polynomial.aeval A p) G hsymm hprod

/-- If every polynomial admits an auxiliary operator with the symmetrized
bound and the sharp one-sided lower bound on the real part of its product,
then the closed numerical range is a `(1 + √2)`-polynomial spectral set. -/
theorem crouzeix_palencia_of_auxiliary_re_inner_lower_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ∀ x : E, ‖x‖ = 1 →
        -(polynomialSupNorm p (closure (numericalRange A)) ^ 2) ≤
          RCLike.re ⟪x, (Polynomial.aeval A p * G) x⟫_ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨G, hsymm, hprod⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
      (Polynomial.aeval A p) G hsymm hprod

/-- If every polynomial admits an auxiliary operator satisfying the two
Crouzeix--Palencia bounds, then the closure of the numerical range is a
`(1 + √2)`-polynomial spectral set.  This is the sorry-free assembly consumed
once L4.2c--e construct `G` and establish the bounds. -/
theorem crouzeix_palencia_of_auxiliary_bounds (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * G‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨G, hsymm, hprod⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds
      (Polynomial.aeval A p) G hsymm hprod

/-- The L4.2d/e interface specialized to the contour operator from
`AuxOperator.lean`: once its symmetrized and product bounds hold for every
polynomial, the Crouzeix--Palencia spectral-set conclusion follows. -/
theorem crouzeix_palencia_of_polynomial_auxiliary_bounds
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hbounds : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_auxiliary_bounds A
  intro p
  exact ⟨crouzeixPolynomialAuxiliaryOperator A Omega p, hbounds p⟩

/-- The Crouzeix--Palencia conclusion for a normal operator.  In this branch
the sharper constant `1` follows from the continuous functional calculus and
the polynomial spectral mapping theorem; monotonicity then gives the stated
`1 + √2` constant. -/
theorem crouzeix_palencia_of_isStarNormal (A : E →L[ℂ] E) [IsStarNormal A] :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    have hm : 0 ≤ polynomialSupNorm p (closure (numericalRange A)) :=
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
    calc
      ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (closure (numericalRange A)) :=
        norm_aeval_le_polynomialSupNorm_of_isStarNormal A
          (isCompact_closure_numericalRange_palencia A)
          (spectrum_subset_closure_numericalRange A) p
      _ = 1 * polynomialSupNorm p (closure (numericalRange A)) := by rw [one_mul]
      _ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (closure (numericalRange A)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg 2)) hm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
