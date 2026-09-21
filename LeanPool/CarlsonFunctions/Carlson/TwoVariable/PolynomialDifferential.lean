/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.RPolynomial
public import LeanPool.CarlsonFunctions.Pochhammer.Identities

/-! # Differential and contiguous identities for two-variable Carlson polynomials -/

open Complex Polynomial Finset
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- Homogeneity of the two-variable Pochhammer numerator, including exceptional parameters. -/
theorem carlsonRPolynomialNumerator₂_smul (n : ℕ) (p q c x y : ℂ) :
    carlsonRPolynomialNumerator₂ n p q (c * x) (c * y) =
      c ^ n * carlsonRPolynomialNumerator₂ n p q x y := by
  simp only [carlsonRPolynomialNumerator₂, mul_pow, mul_sum]
  apply sum_congr rfl
  intro ij hij
  rw [← mem_antidiagonal.mp hij, pow_add]
  ring

/-- Two-variable specialization of the division-free linear transformation. -/
theorem carlsonRPolynomialNumerator₂_transform (n : ℕ) (p q x y : ℂ) :
    carlsonRPolynomialNumerator₂ n p q x y =
      (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n (1 - p - q - n) q x (x - y) := by
  have H := carlsonRPolynomialNumerator_transform n (0 : Fin 2) (pair p q) (pair x y)
  have hb : carlsonRTransformParameters n 0 (pair p q) = pair (1 - p - q - n) q := by
    ext i
    fin_cases i <;> simp [carlsonRTransformParameters, pair, Fin.sum_univ_two]
    ring
  have hz : carlsonRTransformVariables 0 (pair x y) = pair x (x - y) := by
    ext i
    fin_cases i <;> simp [carlsonRTransformVariables, pair]
  rw [hb, hz] at H
  simpa only [carlsonRPolynomialNumerator_pair] using H

/-- The weighted sum of the two parameter shifts only depends on the total parameter. -/
theorem carlsonRPolynomialNumerator₂_weighted_shift (n : ℕ) (p q x y : ℂ) :
    p * carlsonRPolynomialNumerator₂ n (p + 1) q x y +
      q * carlsonRPolynomialNumerator₂ n p (q + 1) x y =
        (p + q + n) * carlsonRPolynomialNumerator₂ n p q x y := by
  simp only [carlsonRPolynomialNumerator₂, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro ij hij
  have hn : (n : ℂ) = ij.1 + ij.2 := by exact_mod_cast (mem_antidiagonal.mp hij).symm
  have hp := ascPochhammer_eval_shift p ij.1
  have hq := ascPochhammer_eval_shift q ij.2
  rw [hn]
  linear_combination
    (n.choose ij.1 : ℂ) * (ascPochhammer ℂ ij.2).eval q * x ^ ij.1 * y ^ ij.2 * hp +
    (n.choose ij.1 : ℂ) * (ascPochhammer ℂ ij.1).eval p * x ^ ij.1 * y ^ ij.2 * hq

/-- Coordinate derivatives of the explicit two-variable numerator. -/
theorem hasDerivAt_carlsonRPolynomialNumerator₂_left (n : ℕ) (p q x y : ℂ) :
    HasDerivAt (fun w => carlsonRPolynomialNumerator₂ (n + 1) p q w y)
      ((n + 1 : ℂ) * p * carlsonRPolynomialNumerator₂ n (p + 1) q x y) x := by
  have H := hasDerivAt_carlsonRPolynomialNumerator_update_succ n (0 : Fin 2)
    (pair p q) (pair x y)
  have hb : addDirichletUnit (pair p q) 0 = pair (p + 1) q := by
    ext i; fin_cases i <;> simp [addDirichletUnit, pair]
  rw [hb] at H
  simp only [carlsonRPolynomialNumerator_pair, pair_zero] at H
  convert H using 1
  funext w
  rw [← carlsonRPolynomialNumerator_pair]
  congr 1
  ext i
  fin_cases i <;> simp [pair]

theorem hasDerivAt_carlsonRPolynomialNumerator₂_right (n : ℕ) (p q x y : ℂ) :
    HasDerivAt (fun w => carlsonRPolynomialNumerator₂ (n + 1) p q x w)
      ((n + 1 : ℂ) * q * carlsonRPolynomialNumerator₂ n p (q + 1) x y) y := by
  simpa only [carlsonRPolynomialNumerator₂_swap n,
    carlsonRPolynomialNumerator₂_swap (n + 1)] using
      hasDerivAt_carlsonRPolynomialNumerator₂_left n q p y x

/-- Simultaneously translating the nodes lowers the degree without shifting the parameters. -/
theorem hasDerivAt_carlsonRPolynomialNumerator₂_translate (n : ℕ) (p q x y w : ℂ) :
    HasDerivAt (fun t => carlsonRPolynomialNumerator₂ (n + 1) p q (x + t) (y + t))
      ((n + 1 : ℂ) * (p + q + n) *
        carlsonRPolynomialNumerator₂ n p q (x + w) (y + w)) w := by
  let F : ℂ × ℂ → ℂ := fun z => carlsonRPolynomialNumerator₂ (n + 1) p q z.1 z.2
  have hF : Differentiable ℂ F := by
    unfold F carlsonRPolynomialNumerator₂
    fun_prop
  let L := fderiv ℂ F (x + w, y + w)
  have hleft : L (1, 0) = (n + 1 : ℂ) * p *
      carlsonRPolynomialNumerator₂ n (p + 1) q (x + w) (y + w) := by
    exact ((hF _).hasFDerivAt.comp_hasDerivAt (x + w)
      ((hasDerivAt_id _).prodMk (hasDerivAt_const _ (y + w)))).unique
        (hasDerivAt_carlsonRPolynomialNumerator₂_left n p q (x + w) (y + w))
  have hright : L (0, 1) = (n + 1 : ℂ) * q *
      carlsonRPolynomialNumerator₂ n p (q + 1) (x + w) (y + w) := by
    exact ((hF _).hasFDerivAt.comp_hasDerivAt (y + w)
      ((hasDerivAt_const _ (x + w)).prodMk (hasDerivAt_id _))).unique
        (hasDerivAt_carlsonRPolynomialNumerator₂_right n p q (x + w) (y + w))
  have H := (hF _).hasFDerivAt.comp_hasDerivAt w
    (((hasDerivAt_id w).const_add x).prodMk ((hasDerivAt_id w).const_add y))
  change HasDerivAt _ (L (1, 1)) w at H
  rw [show ((1, 1) : ℂ × ℂ) = (1, 0) + (0, 1) by ext <;> simp,
    map_add, hleft, hright, mul_assoc, mul_assoc, ← mul_add,
    carlsonRPolynomialNumerator₂_weighted_shift] at H
  simpa only [mul_assoc, Function.comp_def, id_eq, F] using! H

/-- A division-free contiguous relation transferring one unit between the parameters. -/
theorem carlsonRPolynomialNumerator₂_contiguous (n : ℕ) (p q x y : ℂ) :
    (q - 1) * carlsonRPolynomialNumerator₂ (n + 1) p q x y +
      (n + 1 : ℂ) * (p + q + n) * x *
        carlsonRPolynomialNumerator₂ n (p + 1) (q - 1) x y =
      (q + n) * carlsonRPolynomialNumerator₂ (n + 1) (p + 1) (q - 1) x y := by
  have hboundary : (q - 1) * (ascPochhammer ℂ (n + 1)).eval q =
      (q + n) * (ascPochhammer ℂ (n + 1)).eval (q - 1) := by
    simpa only [sub_add_cancel, Nat.cast_add, Nat.cast_one, sub_add_add_cancel] using
      ascPochhammer_eval_shift (q - 1) (n + 1)
  simp only [carlsonRPolynomialNumerator₂, Finset.Nat.sum_antidiagonal_succ,
    Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, eval_one, pow_zero, one_mul,
    mul_one, mul_add, mul_sum]
  rw [← mul_assoc, hboundary, mul_assoc]
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro ij hij
  have hn : (n : ℂ) = ij.1 + ij.2 := by exact_mod_cast (mem_antidiagonal.mp hij).symm
  have hc : ((ij.1 : ℂ) + 1) * ((n + 1).choose (ij.1 + 1) : ℂ) =
      (n + 1 : ℂ) * (n.choose ij.1 : ℂ) := by
    exact_mod_cast (by simpa only [mul_comm] using
      (Nat.add_one_mul_choose_eq n ij.1).symm :
      (ij.1 + 1) * (n + 1).choose (ij.1 + 1) = (n + 1) * n.choose ij.1)
  have hp := congrArg (Polynomial.eval p) (ascPochhammer_succ_left ℂ ij.1)
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one] at hp
  have hq := ascPochhammer_eval_shift (q - 1) ij.2
  simp only [sub_add_cancel] at hq
  simp only [hp, ascPochhammer_succ_eval, pow_succ]
  rw [hn] at hc ⊢
  linear_combination
    ((n + 1).choose (ij.1 + 1) : ℂ) * p *
      (ascPochhammer ℂ ij.1).eval (p + 1) * x ^ (ij.1 + 1) * y ^ ij.2 * hq -
    (p + q + (ij.1 : ℂ) + ij.2) * (ascPochhammer ℂ ij.1).eval (p + 1) *
      (ascPochhammer ℂ ij.2).eval (q - 1) * x ^ (ij.1 + 1) * y ^ ij.2 * hc

end DirichletTransform.TwoVariable
end
