/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import LeanPool.LiCriterion.Lc.LiCriterion.XiOrderBridge

/-!
# Fidelity: the Taylor coefficients are Li's `λₙ`

`taylorCoeff riemannXi n` is defined analytically, as the `n`-th Taylor coefficient at `0` of
the logarithmic derivative of `s ↦ ξ(1/(1-s))`.  Li (1997) and Bombieri–Lagarias instead give
the *arithmetic* form, a sum over the nontrivial zeros:

  `λₘ = ∑_ρ (1 - (1 - 1/ρ)^m)`.

This file proves that the two agree, so that the statement of record is checkably about Li's
sequence and not merely about a Taylor coefficient that resembles it.

## Main results

* `taylorCoeff_eq_weighted_tsum` : the sum formula, now *unconditional* -- the genus-one
  summability and the Hadamard factorization are supplied from `order ξ ≤ 1`;
* `liSummand_pairedZero` : under `ρ ↦ 1 - ρ` the base `1 - 1/ρ` is inverted, so the paired
  summand is `(1 - (1-1/ρ)^{-(n+1)}) + (1 - (1-1/ρ)^{n+1})`;
* `taylorCoeff_eq_li_symmetrized` : the fidelity statement itself.

## Why the sum is symmetrised

`∑_ρ (1 - (1 - 1/ρ)^m)` is *not* absolutely convergent: the individual terms decay like
`1/‖ρ‖`, and only the pairing `ρ ↔ 1 - ρ` produces the `1/‖ρ‖²` decay that makes the sum
converge -- this is exactly what "genus one" means here.  `tsum` in Mathlib is unconditional
summability, so writing the criterion as a bare `∑'` over the zeros would be a *false*
statement, not merely a weaker one.  The half-sum of Li's summand and its mirror image is the
symmetric summation convention under which Li's formula actually holds, and
`analyticOrderNatAt_riemannXi_one_sub` together with `zero_pairing` shows the pairing really is
a symmetry of the zero multiset.
-/

@[expose] public section

namespace LiCriterion

open Complex

/-! ### The sum formula, unconditionally -/

/-- **The Li sum formula, with no hypotheses.**
    `weighted_paired_sum_formula_of_standard_hypotheses`
with its two analytic inputs discharged from `order ξ ≤ 1`. -/
theorem taylorCoeff_eq_weighted_tsum (n : ℕ) :
    taylorCoeff riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ :=
  weighted_paired_sum_formula_of_standard_hypotheses
    (xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one)
    (xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder
      xi_order_le_one) n

/-! ### The pairing inverts the base `1 - 1/ρ` -/

/-- For a nontrivial zero `ρ`, the bases attached to `ρ` and to `1 - ρ` are reciprocal:
`(1 - 1/ρ) * (1 - 1/(1-ρ)) = 1`. -/
lemma one_sub_inv_mul_one_sub_inv_one_sub (ρ : NontrivialZero) :
    (1 - 1 / ρ.val) * (1 - 1 / (1 - ρ.val)) = 1 := by
  have h0 : ρ.val ≠ 0 := NontrivialZero.ne_zero ρ
  have h1 : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (NontrivialZero.ne_one ρ))
  field_simp
  ring

/-- The base attached to `ρ` is nonzero. -/
lemma one_sub_inv_ne_zero (ρ : NontrivialZero) : (1 : ℂ) - 1 / ρ.val ≠ 0 := by
  intro h
  have := one_sub_inv_mul_one_sub_inv_one_sub ρ
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- **The pairing inverts the exponent.**  `Aₙ(1-ρ) = 1 - (1 - 1/ρ)^{n+1}`, so that the paired
summand `Tₙ(ρ)` is `(1 - w^{-(n+1)}) + (1 - w^{n+1})` with `w = 1 - 1/ρ`. -/
lemma liSummand_pairedZero (n : ℕ) (ρ : NontrivialZero) :
    liSummand n (pairedZero ρ) = 1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1) := by
  have hw : (1 : ℂ) - 1 / ρ.val ≠ 0 := one_sub_inv_ne_zero ρ
  have hinv : (1 : ℂ) - 1 / (pairedZero ρ).val = (1 - 1 / ρ.val)⁻¹ := by
    rw [pairedZero_val]
    field_simp
    linear_combination (one_sub_inv_mul_one_sub_inv_one_sub ρ)
  rw [liSummand, hinv, inv_zpow, zpow_neg, inv_inv]

/-! ### The pairing is a symmetry of the zero multiset -/

/-- **The functional equation for `ξ`**: `ξ(1-s) = ξ(s)`, from `completedRiemannZeta₀_one_sub`. -/
lemma riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-- The multiplicity of a zero is invariant under `ρ ↦ 1 - ρ`.  Together with `zero_pairing`
this says the pairing is a symmetry of the zero multiset, which is what makes the symmetrized
sum below the right notion. -/
lemma analyticOrderNatAt_riemannXi_one_sub (s : ℂ) :
    analyticOrderNatAt riemannXi (1 - s) = analyticOrderNatAt riemannXi s := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) s := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun w : ℂ => 1 - w) s ≠ 0 := by simp
  have hcomp : (riemannXi ∘ fun w : ℂ => 1 - w) = riemannXi :=
    funext fun w => riemannXi_one_sub w
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := riemannXi) (g := fun w : ℂ => 1 - w) hg hg'
  rw [hcomp] at h
  simp only [analyticOrderNatAt, h]

/-! ### Li's formula, symmetrized -/

/-- The paired summand written out: `Tₙ(ρ) = (1 - w^{-(n+1)}) + (1 - w^{n+1})` with
`w = 1 - 1/ρ`.  The second term is Li's summand at exponent `n+1`; the first is its mirror
image under `ρ ↦ 1 - ρ`. -/
lemma liPairedSummand_eq (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ =
      (1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1))) + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1)) := by
  rw [liPairedSummand, liSummand_pairedZero, liSummand]

/-- **Fidelity, symmetrized form.**  The `n`-th Taylor coefficient of `ξ` under the Cayley map is
the half-sum, over the nontrivial zeros counted with multiplicity, of Li's summand
`1 - (1 - 1/ρ)^{n+1}` and its mirror image under `ρ ↦ 1 - ρ`.

This is the criterion's `λ_{n+1}` in the arithmetic form of Li (1997) and Bombieri–Lagarias,
written symmetrically so that no invariance of the multiplicity under the pairing is needed. -/
theorem taylorCoeff_eq_li_symmetrized (n : ℕ) :
    taylorCoeff riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) *
            ((1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1)))
              + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1))) := by
  rw [taylorCoeff_eq_weighted_tsum n]
  congr 1
  refine tsum_congr fun ρ => ?_
  rw [liPairedSummand_eq]

/-- **The symmetrized zero sum converges.**  The weighted paired family summed in
`taylorCoeff_eq_li_symmetrized` is summable, so the `∑'` there denotes the genuine symmetric
sum over the zeros and not Lean's default value for a non-summable family.  Unconditional: the
genus-1 weighted summability comes from `order ξ ≤ 1`. -/
theorem summable_li_symmetrized (n : ℕ) :
    Summable (fun ρ : NontrivialZero =>
      (analyticOrderNatAt riemannXi ρ.val : ℂ) *
        ((1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1)))
          + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1)))) := by
  refine (summable_weighted_Li_paired_summand_of_weighted_genus
    (xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one) n).congr
    fun ρ => ?_
  rw [liPairedSummand_eq]

end LiCriterion
