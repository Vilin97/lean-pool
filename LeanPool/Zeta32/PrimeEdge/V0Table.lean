/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Local
public import LeanPool.Zeta32.PrimeEdge.Blocks
public import LeanPool.Zeta32.PrimeEdge.Index

/-! **S2b-4**: the leading local values `V⁰(u^e r_type)` are the exact
rationals of Blocks.lean (code/local_blocks_453.py). Each is a finite computation:
polynomial division by `(u+1)…(u+4)` resp. `(u+1)(u+2)(u+3)`, Lagrange residues, `V⁰(u^e) = e
B_{e-1}`
and `V⁰((u+m)^{-1}) = 2 H_m^{(3)}`. -/

public section

open Polynomial
open scoped BigOperators

namespace Zeta32.PrimeEdge.V0Aux

/-! Helpers (namespace `V0Aux` to avoid clashes with sibling files). -/

lemma locPoly_zero (s : ℚ) : locPoly s 0 = 0 := by
  exact Zeta32.PrimeEdge.locPoly_zero_linear s

lemma locPoly_add (s : ℚ) (P Q : ℚ[X]) : locPoly s (P + Q) = locPoly s P + locPoly s Q := by
  exact Zeta32.PrimeEdge.locPoly_add_linear s P Q

lemma locPoly_C_mul_X_pow (s a : ℚ) (k : ℕ) : locPoly s (C a * X ^ k) = a * locMoment s k := by
  unfold locPoly
  rw [C_mul_X_pow_eq_monomial]
  exact sum_monomial_index a _ (zero_mul _)

/-- If `S = q · T + R` with `T = ∏_{m ∈ M} (X + m)` and `deg R < |M|`, then the polynomial part
of `locValue` is `locPoly q`. -/
lemma locValue_eq_of_decomp (s : ℚ) (M : Finset ℕ) (S q R : ℚ[X])
    (hR : R.natDegree < M.card) (hS : S = q * ∏ m ∈ M, (X + C (m : ℚ)) + R) :
    locValue s S M = locPoly s q +
      ∑ m ∈ M, S.eval (-(m : ℚ)) / (∏ m' ∈ M.erase m, ((m' : ℚ) - m)) * locPole s m := by
  have hmon : (∏ m ∈ M, (X + C (m : ℚ))).Monic :=
    monic_prod_of_monic _ _ fun m _ => monic_X_add_C _
  have hdeg : (∏ m ∈ M, (X + C (m : ℚ))).natDegree = M.card := by
    rw [natDegree_prod_of_monic M _ fun m _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  have hq : S /ₘ ∏ m ∈ M, (X + C (m : ℚ)) = q := by
    refine (div_modByMonic_unique q R hmon ⟨?_, ?_⟩).1
    · rw [hS]; ring
    · exact degree_lt_degree (hdeg ▸ hR)
  unfold locValue
  rw [hq]

lemma H3_vals : Zeta32.H 3 1 = 1 ∧ Zeta32.H 3 2 = 9/8 ∧ Zeta32.H 3 3 = 251/216 ∧
    Zeta32.H 3 4 = 2035/1728 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Zeta32.H]
  · rw [show Finset.Icc 1 1 = {1} by decide]; norm_num
  · rw [show Finset.Icc 1 2 = {1, 2} by decide]; norm_num [Finset.sum_insert]
  · rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]; norm_num [Finset.sum_insert]
  · rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]; norm_num [Finset.sum_insert]

/-- Close `locValue 0 S M = v` from an explicit quotient `q` and remainder `R` with
`natDegree R ≤ d < |M|`. -/
macro "v0_decomp " q:term:max R:term:max d:term:max : tactic => `(tactic| (
  rw [locValue_eq_of_decomp 0 _ _ $q $R
    (lt_of_le_of_lt (b := $d) (by compute_degree <;> norm_num) (by decide))
    (by norm_num [Finset.prod_insert, map_ofNat C] <;> ring)]
  simp only [locPoly_add, locPoly_C_mul_X_pow, locPoly_zero]
  norm_num [Finset.sum_insert, Finset.prod_insert, Finset.erase_insert_of_ne, locMoment, locPole,
    H3_vals]))

lemma zero_1 : locValue 0 (X ^ 1) {1, 2, 3, 4} = 1/1296 := by
  v0_decomp (0) (X ^ 1) (3)

lemma zero_2 : locValue 0 (X ^ 2) {1, 2, 3, 4} = 7/648 := by
  v0_decomp (0) (X ^ 2) (3)

lemma zero_3 : locValue 0 (X ^ 3) {1, 2, 3, 4} = 1565/648 := by
  v0_decomp (0) (X ^ 3) (3)

lemma zero_4 : locValue 0 (X ^ 4) {1, 2, 3, 4} = -15575/648 := by
  v0_decomp (C 1 * X ^ 0)
    (C (-10) * X ^ 3 + C (-35) * X ^ 2 + C (-50) * X ^ 1 + C (-24) * X ^ 0) (3)

lemma zero_5 : locValue 0 (X ^ 5) {1, 2, 3, 4} = 101261/648 := by
  v0_decomp (C 1 * X ^ 1 + C (-10) * X ^ 0)
    (C 65 * X ^ 3 + C 300 * X ^ 2 + C 476 * X ^ 1 + C 240 * X ^ 0) (3)

lemma zero_6 : locValue 0 (X ^ 6) {1, 2, 3, 4} = -545255/648 := by
  v0_decomp (C 1 * X ^ 2 + C (-10) * X ^ 1 + C 65 * X ^ 0)
    (C (-350) * X ^ 3 + C (-1799) * X ^ 2 + C (-3010) * X ^ 1 + C (-1560) * X ^ 0) (3)

lemma zero_7 : locValue 0 (X ^ 7) {1, 2, 3, 4} = 2649929/648 := by
  v0_decomp (C 1 * X ^ 3 + C (-10) * X ^ 2 + C 65 * X ^ 1 + C (-350) * X ^ 0)
    (C 1701 * X ^ 3 + C 9240 * X ^ 2 + C 15940 * X ^ 1 + C 8400 * X ^ 0) (3)

lemma high_3 : locValue 0 (X ^ 3) {1, 2, 3} = -115/8 := by
  v0_decomp (C 1 * X ^ 0) (C (-6) * X ^ 2 + C (-11) * X ^ 1 + C (-6) * X ^ 0) (2)

lemma high_4 : locValue 0 (X ^ 4) {1, 2, 3} = 481/8 := by
  v0_decomp (C 1 * X ^ 1 + C (-6) * X ^ 0) (C 25 * X ^ 2 + C 60 * X ^ 1 + C 36 * X ^ 0) (2)

lemma high_5 : locValue 0 (X ^ 5) {1, 2, 3} = -1731/8 := by
  v0_decomp (C 1 * X ^ 2 + C (-6) * X ^ 1 + C 25 * X ^ 0)
    (C (-90) * X ^ 2 + C (-239) * X ^ 1 + C (-150) * X ^ 0) (2)

end Zeta32.PrimeEdge.V0Aux

namespace Zeta32.PrimeEdge

open V0Aux

variable {p : ℕ}

/-- `V⁰(u^e r_0) = zeroMoment e`, `r_0 = u/((u+1)(u+2)(u+3)(u+4))`. -/
theorem V0_zero_table (e : Fin 7) :
    locValue 0 (X ^ (e.val + 1)) {1, 2, 3, 4} = zeroMoment e := by
  fin_cases e
  · exact zero_1
  · exact zero_2
  · exact zero_3
  · exact zero_4
  · exact zero_5
  · exact zero_6
  · exact zero_7

/-- `V⁰(u^e r_L) = lowMoment e`, `r_L = u³/((u+1)(u+2)(u+3)(u+4))`. -/
theorem V0_low_table (e : Fin 5) :
    locValue 0 (X ^ (e.val + 3)) {1, 2, 3, 4} = lowMoment e := by
  have h : lowMoment e = zeroMoment ⟨e.val + 2, by omega⟩ := by fin_cases e <;> rfl
  rw [h, ← V0_zero_table]

/-- `V⁰(u^e r_H) = highMoment e`, `r_H = u³/((u+1)(u+2)(u+3))`. -/
theorem V0_high_table (e : Fin 3) :
    locValue 0 (X ^ (e.val + 3)) {1, 2, 3} = highMoment e := by
  fin_cases e
  · exact high_3
  · exact high_4
  · exact high_5

lemma blockMoment_zero (p : ℕ) (e : Fin 7) : blockMoment p 0 e.val = zeroMoment e := by
  simp only [blockMoment]
  exact V0_zero_table e

lemma blockMoment_low {p b : ℕ} (hb0 : b ≠ 0) (hb : b + 5 ≤ p) (e : Fin 5) :
    blockMoment p b e.val = lowMoment e := by
  simp only [blockMoment, ite_eq_right hb0, ite_eq_left hb]
  exact V0_low_table e

lemma blockMoment_high {p b : ℕ} (hb0 : b ≠ 0) (hb : ¬ b + 5 ≤ p) (e : Fin 3) :
    blockMoment p b e.val = highMoment e := by
  simp only [blockMoment, ite_eq_right hb0, ite_eq_right hb]
  exact V0_high_table e

end Zeta32.PrimeEdge

end
