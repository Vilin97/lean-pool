/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Basic

/-! The global side of S2b-1: the `X`-free part of `U_r(A / D_{5n})` is
the functional `locValue r` (same formulas, global constants) on `t A / D_{5n}`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

lemma locPoly_X_mul (r : ℚ) (q : ℚ[X]) : locPoly r (X * q) = Zeta32.polynomialMoment r q := by
  rw [locPoly_eq, polynomialMoment_eq]

lemma locPoly_C (s c : ℚ) : locPoly s (C c) = 2 * s * c := by
  rw [← monomial_zero_left, locPoly_monomial, locMoment]
  simp; ring

lemma X_mul_prod_erase (M : Finset ℕ) {j : ℕ} (hj : j ∈ M) :
    X * ∏ m' ∈ M.erase j, (X + C (m' : ℚ)) =
      mprod M - C (j : ℚ) * ∏ m' ∈ M.erase j, (X + C (m' : ℚ)) := by
  rw [mprod, ← Finset.mul_prod_erase M _ hj]; ring

/-- `X · A` in partial-fraction form over `D_{5n}`. -/
lemma XA_pf (A : ℚ[X]) (M : Finset ℕ) :
    X * A = (X * (A /ₘ mprod M) + C (∑ j ∈ M, resN A M j)) * mprod M +
      ∑ j ∈ M, C (-(j : ℚ) * resN A M j) * ∏ m' ∈ M.erase j, (X + C (m' : ℚ)) := by
  conv_lhs => rw [pf_nat A M]
  rw [mul_add, Finset.mul_sum]
  have h : ∀ j ∈ M, X * (C (resN A M j) * ∏ m' ∈ M.erase j, (X + C (m' : ℚ))) =
      C (resN A M j) * mprod M +
        C (-(j : ℚ) * resN A M j) * ∏ m' ∈ M.erase j, (X + C (m' : ℚ)) := by
    intro j hj
    rw [mul_left_comm, X_mul_prod_erase M hj, C_mul, C_neg]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]
  ring

/-- The `X`-free part of `Lfun` is `locValue r (X A) [1, 5n]`. -/
theorem Lfun_coeff_zero (r : ℚ) (n : ℕ) (A : ℚ[X]) :
    (Lfun r n A).coeff 0 = locValue r (X * A) (Finset.Icc 1 (5 * n)) := by
  set M := Finset.Icc 1 (5 * n) with hM
  have hD : Zeta32.D (5 * n) = mprod M := rfl
  rw [XA_pf A M, locValue_pf, dist_locPoly_add, locPoly_X_mul, locPoly_C]
  unfold Lfun
  simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
  rw [hD, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resP_Pl5]
  change resN A M j * _ = _
  unfold Zeta32.beta locPole
  ring

end

end Zeta32.PrimeEdge

end
