/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Interfaces
public import LeanPool.Zeta5Irrational.SimplePoles
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Partial fractions for `t^k R_n(t) = X^k D_n^4 / D_{5n}` with the `polynomialPart` and
`residue` of `Zeta32/Family.lean`.

The generic part (`piPl`, `polyPart`, `resP`, `partial_fractionsP`) is
-- adapted from dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/SimplePoles.lean
(itself extracted from Apery/Arith/PoleFun.lean in mo271/Zeta5 by Moritz Firsching, Apache-2.0);
the specialization to `D (5*n)` follows Li2 `OriginalPartialFractions.lean`. -/

public section

open Finset Polynomial
open scoped BigOperators

namespace Zeta32.Analytic.Contour.SimplePoles

export Zeta5Irrational (piPl piPl_monic natDegree_piPl polyPart resP lagrange_basis_eq
  partial_fractionsP natDegree_polyPart_le)

end Zeta32.Analytic.Contour.SimplePoles

namespace Zeta32.Analytic.Contour

noncomputable section

/-- The poles `-1, …, -m` as integers. -/
def negativePoles (m : ℕ) : Finset ℤ := (Finset.Icc 1 m).image (fun j : ℕ => -(j : ℤ))

lemma negative_nat_injective : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
  intro a b h
  simpa using h

lemma negativePoles_product (m : ℕ) : SimplePoles.piPl (negativePoles m) = D m := by
  unfold SimplePoles.piPl negativePoles D
  rw [Finset.prod_image fun a _ b _ h => negative_nat_injective h]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [sub_eq_add_neg]

/-- **Partial fractions** for the entries of the family: `X^k D_n^4 = q D_{5n} + Σ c_j
∏_{l≠j}(X+l)`. -/
theorem numerator_partial_fractions (n k : ℕ) :
    numerator n k = polynomialPart n k * D (5*n) +
      ∑ j ∈ Finset.Icc 1 (5*n), C (residue n k j) *
        ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, (X + C (l : ℚ)) := by
  have h := SimplePoles.partial_fractionsP (numerator n k) (negativePoles (5*n))
  rw [SimplePoles.polyPart, negativePoles_product] at h
  conv_lhs => rw [h]
  congr 1
  unfold negativePoles
  rw [Finset.sum_image fun a _ b _ he => negative_nat_injective he]
  apply Finset.sum_congr rfl
  intro j _
  have hres : SimplePoles.resP (numerator n k)
      ((Finset.Icc 1 (5*n)).image (fun j : ℕ => -(j : ℤ))) (-(j : ℤ)) = residue n k j := by
    unfold SimplePoles.resP residue
    rw [← Finset.image_erase negative_nat_injective, Finset.prod_image
      fun a _ b _ he => negative_nat_injective he]
    simp only [Int.cast_neg, Int.cast_natCast, neg_sub_neg]
  rw [hres, ← Finset.image_erase negative_nat_injective, Finset.prod_image
    fun a _ b _ he => negative_nat_injective he]
  simp only [Int.cast_neg, Int.cast_natCast, C_neg, sub_neg_eq_add]

lemma aeval_D (m : ℕ) (z : ℂ) : aeval z (D m) = ∏ j ∈ Finset.Icc 1 m, (z + (j : ℂ)) := by
  simp [D, map_prod]

lemma prod_add_nat_ne_zero (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∏ j ∈ Finset.Icc 1 m, (z + (j : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- Complex form of the partial fractions: `z^k R_n(z) = q(z) + Σ_j c_j/(z+j)` for `Re z > 0`. -/
theorem pow_mul_Rfun_eq (n k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    z ^ k * Rfun n z = aeval z (polynomialPart n k) +
      ∑ j ∈ Finset.Icc 1 (5*n), (residue n k j : ℂ) / (z + (j : ℂ)) := by
  have hD := prod_add_nat_ne_zero (5*n) hz
  have hpf := congrArg (fun p : ℚ[X] => aeval z p) (numerator_partial_fractions n k)
  simp only [map_add, map_mul, map_sum, aeval_C, map_prod, aeval_X, aeval_D,
    numerator, map_pow] at hpf
  unfold Rfun
  rw [← mul_div_assoc, hpf, add_div, mul_div_assoc, div_self hD, mul_one, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : z + (j : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [← Finset.mul_prod_erase _ _ hj]
  have hE : ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, (z + (l : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l _ h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    linarith
  simp only [eq_ratCast, map_natCast] at *
  field_simp

end

end Zeta32.Analytic.Contour

end
