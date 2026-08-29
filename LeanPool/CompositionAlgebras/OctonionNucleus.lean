/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import LeanPool.CompositionAlgebras.Octonions

-- Only seven coordinate equations from three associators are needed below.

/-!
# The octonion nucleus lies in `ℝ · 1`

The **nucleus** of a not-necessarily-associative algebra is the set of elements that
associate with everything.  For the octonions it is as small as it can be: `ℝ · 1`.  The
statement below is the "third slot" form -- `c` associates in the last position, `(x y) c =
x (y c)`, for all `x, y` -- and concludes that `c` has no imaginary part.  Equivalently:
`𝕆` is as far from associative as an alternative algebra gets, since by the alternative
laws any two elements already generate an associative subalgebra.

The proof is the finite Cayley-table check the memo describes. For each of the seven Fano
triples `(i, j, k)` the associator `[e_i, e_j, c]` is expanded in coordinates; each
`c.coords m` outside the quaternion subalgebra `span{e_0, e_i, e_j, e_k}` picks up a
relation `c.coords m = -c.coords m`. Three triples cover all seven imaginary indices:
`(1,2,4)` kills `3,5,6,7`, `(2,3,5)` kills `1,4`, and `(3,4,6)` kills `2`.

`decide` handles the `Fin 8` guards.  Nothing here or anywhere in this development is
discharged by kernel-external evaluation, so nothing below rests on the compiler.
-/
namespace Octonion

theorem coord_eq {a b : Octonion} (hab : a = b) (k : Fin 8) : a.coords k = b.coords k := by
  rw [hab]

theorem tbl_1_2 : mul (basisVec 1) (basisVec 2) = basisVec 4 := by
  ext m; fin_cases m <;> simp [mul, basisVec]

theorem tbl_2_3 : mul (basisVec 2) (basisVec 3) = basisVec 5 := by
  ext m; fin_cases m <;> simp [mul, basisVec]

theorem tbl_3_4 : mul (basisVec 3) (basisVec 4) = basisVec 6 := by
  ext m; fin_cases m <;> simp [mul, basisVec]

/-- The substantive inclusion: an element in the third-slot nucleus has no imaginary part. -/
theorem nucleus_real (c : Octonion)
    (h : ∀ x y : Octonion, mul (mul x y) c = mul x (mul y c)) :
    c.coords 1 = 0 ∧ c.coords 2 = 0 ∧ c.coords 3 = 0 ∧ c.coords 4 = 0 ∧
    c.coords 5 = 0 ∧ c.coords 6 = 0 ∧ c.coords 7 = 0 := by
  have H12 := h (basisVec 1) (basisVec 2)
  rw [tbl_1_2] at H12
  have H23 := h (basisVec 2) (basisVec 3)
  rw [tbl_2_3] at H23
  have H34 := h (basisVec 3) (basisVec 4)
  rw [tbl_3_4] at H34
  have u3 := coord_eq H12 3
  have u5 := coord_eq H12 5
  have u6 := coord_eq H12 6
  have u7 := coord_eq H12 7
  have v6 := coord_eq H23 6
  have v7 := coord_eq H23 7
  have w7 := coord_eq H34 7
  simp only [mul, basisVec, Fin.isValue] at u3 u5 u6 u7
  simp +decide only [ite_true, ite_false, add_zero, zero_add, zero_sub,
    sub_zero, zero_mul, one_mul, sub_neg_eq_add, sub_self] at u3 u5 u6 u7
  simp only [mul, basisVec, Fin.isValue] at v6 v7
  simp +decide only [ite_true, ite_false, add_zero, zero_add, zero_sub,
    sub_zero, zero_mul, one_mul, sub_neg_eq_add, sub_self] at v6 v7
  simp only [mul, basisVec, Fin.isValue] at w7
  simp +decide only [ite_true, ite_false, add_zero, zero_add, zero_sub,
    sub_zero, zero_mul, one_mul, sub_neg_eq_add, sub_self] at w7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith

end Octonion
