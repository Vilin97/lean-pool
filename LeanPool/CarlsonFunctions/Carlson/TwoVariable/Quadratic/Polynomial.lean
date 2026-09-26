/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.Quadratic.Geometry
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.PolynomialDifferential
public import LeanPool.CarlsonFunctions.Pochhammer.Identities

/-! # Polynomial quadratic transformations

The squared-node regression theorem is retained alongside the correct involutive identity. -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

lemma numerator₂_zero_right (n : ℕ) (p q x : ℂ) :
    carlsonRPolynomialNumerator₂ n p q x 0 = (ascPochhammer ℂ n).eval p * x ^ n := by
  rw [← carlsonRPolynomialNumerator_pair]
  convert! carlsonRPolynomialNumerator_single n (0 : Fin 2) (pair p q) x using 1
  congr 1
  ext i
  fin_cases i <;> simp [pair]

private lemma eq_of_translate_sub_deriv_zero (F G : ℂ → ℂ → ℂ)
    (hzero : ∀ x, F x 0 = G x 0)
    (hd : ∀ x y w, HasDerivAt (fun t => F (x + t) (y + t) - G (x + t) (y + t)) 0 w)
    (x y : ℂ) : F x y = G x y := by
  have H := is_const_of_deriv_eq_zero (fun w => (hd x y w).differentiableAt)
    (fun w => (hd x y w).deriv) 0 (-y)
  simpa only [add_zero, add_neg_cancel, hzero, sub_self, sub_eq_zero] using H

private lemma hasDerivAt_numerator₂_quadratic_translate (n : ℕ) (p q x y w : ℂ) :
    HasDerivAt (fun t => carlsonRPolynomialNumerator₂ (n + 1) p q
      (arithmeticMeanSq (x + t) (y + t)) (geometricMeanSq (x + t) (y + t)))
      ((n + 1 : ℂ) * (p + q + n) *
        carlsonRPolynomialNumerator₂ n p q
          (arithmeticMeanSq (x + w) (y + w)) (geometricMeanSq (x + w) (y + w)) *
        (x + y + 2 * w)) w := by
  let d := ((x - y) / 2) ^ 2
  let s := fun t : ℂ => ((x + y) / 2 + t) ^ 2
  have hs : HasDerivAt s (x + y + 2 * w) w := by
    convert! (((hasDerivAt_id w).const_add ((x + y) / 2)).pow 2) using 1
    simp only [id_eq]
    ring
  have H := (hasDerivAt_carlsonRPolynomialNumerator₂_translate n p q 0 (-d) (s w)).comp w hs
  have hA (t : ℂ) : 0 + s t = arithmeticMeanSq (x + t) (y + t) := by
    dsimp [s, arithmeticMeanSq]; ring
  have hG (t : ℂ) : -d + s t = geometricMeanSq (x + t) (y + t) := by
    dsimp [d, s, geometricMeanSq]; ring
  simpa only [Function.comp_def, hA, hG] using! H

private lemma meanSq_zero_pow (n : ℕ) (x : ℂ) :
    4 ^ n * arithmeticMeanSq x 0 ^ n = x ^ (2 * n) := by
  rw [← mul_pow, pow_mul]
  congr 1
  dsimp [arithmeticMeanSq]
  ring
/-- Polynomial quadratic transformations before inserting redundant Pochhammer factors. -/
private theorem numerator₂_firstQuadratic (n : ℕ) (β x y : ℂ) :
    carlsonRPolynomialNumerator₂ (2 * n) β β x y =
        4 ^ n * (ascPochhammer ℂ n).eval β *
          carlsonRPolynomialNumerator₂ n (β + n) (1 / 2 - n)
            (arithmeticMeanSq x y) (geometricMeanSq x y) ∧
    carlsonRPolynomialNumerator₂ (2 * n + 1) β β x y =
        2 * 4 ^ n * (ascPochhammer ℂ (n + 1)).eval β * ((x + y) / 2) *
          carlsonRPolynomialNumerator₂ n (1 + β + n) (-1 / 2 - n)
            (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  induction n generalizing β x y with
  | zero =>
    simp [carlsonRPolynomialNumerator₂, Finset.Nat.antidiagonal_succ]
    ring
  | succ n ih =>
    have heven (x y : ℂ) : carlsonRPolynomialNumerator₂ (2 * (n + 1)) β β x y =
        4 ^ (n + 1) * (ascPochhammer ℂ (n + 1)).eval β *
          carlsonRPolynomialNumerator₂ (n + 1) (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ))
            (arithmeticMeanSq x y) (geometricMeanSq x y) := by
      apply eq_of_translate_sub_deriv_zero
      · intro v
        rw [numerator₂_zero_right, geometricMeanSq, mul_zero, numerator₂_zero_right,
          show 2 * (n + 1) = (n + 1) + (n + 1) by omega,
          ascPochhammer_add_eval β (n + 1) (n + 1)]
        have H := meanSq_zero_pow (n + 1) v
        rw [show (n + 1) + (n + 1) = 2 * (n + 1) by omega]
        linear_combination
          -(ascPochhammer ℂ (n + 1)).eval β *
            (ascPochhammer ℂ (n + 1)).eval (β + (n + 1 : ℕ)) * H
      · intro u v w
        have hl := hasDerivAt_carlsonRPolynomialNumerator₂_translate (2 * n + 1) β β u v w
        have hr := (hasDerivAt_numerator₂_quadratic_translate n
          (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ)) u v w).const_mul
            (4 ^ (n + 1) * (ascPochhammer ℂ (n + 1)).eval β)
        convert! hl.sub hr using 1
        rw [(ih β (u + w) (v + w)).2]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, pow_succ]
        have hp : β + ((n : ℂ) + 1) = 1 + β + n := by ring
        have hq : (1 : ℂ) / 2 - ((n : ℂ) + 1) = -1 / 2 - n := by ring
        rw [hp, hq]
        ring
    refine ⟨heven x y, ?_⟩
    apply eq_of_translate_sub_deriv_zero
    · intro v
      rw [numerator₂_zero_right, geometricMeanSq, mul_zero, numerator₂_zero_right,
        show 2 * (n + 1) + 1 = ((n + 1) + 1) + (n + 1) by omega,
        ascPochhammer_add_eval β ((n + 1) + 1) (n + 1)]
      have hp : 1 + β + (n + 1 : ℕ) = β + ((n + 1) + 1 : ℕ) := by push_cast; ring
      rw [hp]
      have H := meanSq_zero_pow (n + 1) v
      simp only [add_zero]
      rw [show ((n + 1) + 1) + (n + 1) = 2 * (n + 1) + 1 by omega, pow_succ]
      linear_combination
        -(ascPochhammer ℂ ((n + 1) + 1)).eval β *
          (ascPochhammer ℂ (n + 1)).eval (β + ((n + 1) + 1 : ℕ)) * v * H
    · intro u v w
      have hl := hasDerivAt_carlsonRPolynomialNumerator₂_translate (2 * (n + 1)) β β u v w
      have hm : HasDerivAt (fun t : ℂ => ((u + t) + (v + t)) / 2) 1 w := by
        convert! (((hasDerivAt_id w).const_add u).add
          ((hasDerivAt_id w).const_add v)).div_const 2 using 1
        norm_num
      have hr := (hm.mul (hasDerivAt_numerator₂_quadratic_translate n
        (1 + β + (n + 1 : ℕ)) (-1 / 2 - (n + 1 : ℕ)) u v w)).const_mul
          (2 * 4 ^ (n + 1) * (ascPochhammer ℂ ((n + 1) + 1)).eval β)
      have hc := carlsonRPolynomialNumerator₂_contiguous n
        (β + (n + 1 : ℕ)) (1 / 2 - (n + 1 : ℕ))
          (arithmeticMeanSq (u + w) (v + w)) (geometricMeanSq (u + w) (v + w))
      convert! hl.sub hr using 1
      · funext t
        dsimp only [Pi.sub_apply, Pi.mul_apply]
        ring
      · rw [heven (u + w) (v + w)]
        simp only [ascPochhammer_succ_eval, Nat.cast_add, Nat.cast_mul,
          Nat.cast_one, Nat.cast_ofNat] at hc ⊢
        have hp : β + ((n : ℂ) + 1) + 1 = 1 + β + ((n : ℂ) + 1) := by ring
        have hq : (1 : ℂ) / 2 - ((n : ℂ) + 1) - 1 = -1 / 2 - ((n : ℂ) + 1) := by ring
        rw [hp, hq] at hc
        dsimp only [arithmeticMeanSq] at hc ⊢
        linear_combination
          4 * 4 ^ (n + 1) * (ascPochhammer ℂ n).eval β *
            (β + n) * (β + ((n : ℂ) + 1)) * hc

/-- The even moments on opposite nodes, in division-free form. -/
lemma numerator₂_even_opposite (n : ℕ) (β w : ℂ) :
    carlsonRPolynomialNumerator₂ (2 * n) β β w (-w) =
      4 ^ n * (ascPochhammer ℂ n).eval β *
        (ascPochhammer ℂ n).eval (1 / 2) * w ^ (2 * n) := by
  rw [(numerator₂_firstQuadratic n β w (-w)).1]
  have hA : arithmeticMeanSq w (-w) = 0 := by simp [arithmeticMeanSq]
  rw [hA, ← carlsonRPolynomialNumerator₂_swap,
    numerator₂_zero_right]
  have hp : (1 : ℂ) / 2 - n = 1 - 1 / 2 - n := by ring
  rw [hp, ascPochhammer_eval_reflect]
  rw [show geometricMeanSq w (-w) = -(w ^ 2) by dsimp [geometricMeanSq]; ring,
    neg_pow]
  rw [pow_mul]
  ring_nf
  simp

/-- Division-free polynomial form of the even-degree first quadratic transformation 6.9-8.
It is valid at exceptional parameters because no Pochhammer symbol is divided out. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_even
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n) β β x y =
      (ascPochhammer ℂ (2 * n)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (β + n) (1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  rw [(numerator₂_firstQuadratic n β x y).1, ascPochhammer_eval_double]
  ring

/-- Division-free polynomial form of the odd-degree first quadratic transformation 6.9-9. -/
theorem carlsonRPolynomialNumerator₂_firstQuadratic_odd
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (β + 1 / 2) *
        carlsonRPolynomialNumerator₂ (2 * n + 1) β β x y =
      ((x + y) / 2) * (ascPochhammer ℂ (2 * n + 1)).eval (2 * β) *
        carlsonRPolynomialNumerator₂ n (1 + β + n) (-1 / 2 - n)
          (arithmeticMeanSq x y) (geometricMeanSq x y) := by
  rw [(numerator₂_firstQuadratic n β x y).2, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval, ascPochhammer_eval_double]
  push_cast
  ring

private lemma numerator₂_rotated_quadratic (n : ℕ) (p q x y : ℂ) :
    carlsonRPolynomialNumerator₂ n (1 - p - q - n) q
      (arithmeticMeanSq ((x + y) ^ 2) ((x - y) ^ 2))
      (geometricMeanSq ((x + y) ^ 2) ((x - y) ^ 2)) =
    4 ^ n * (-1 : ℂ) ^ n * carlsonRPolynomialNumerator₂ n p q
      (arithmeticMeanSq (x ^ 2) (y ^ 2)) (geometricMeanSq (x ^ 2) (y ^ 2)) := by
  have hA : arithmeticMeanSq ((x + y) ^ 2) ((x - y) ^ 2) =
      4 * arithmeticMeanSq (x ^ 2) (y ^ 2) := by dsimp [arithmeticMeanSq]; ring
  have hG : geometricMeanSq ((x + y) ^ 2) ((x - y) ^ 2) =
      4 * (arithmeticMeanSq (x ^ 2) (y ^ 2) - geometricMeanSq (x ^ 2) (y ^ 2)) := by
    dsimp [arithmeticMeanSq, geometricMeanSq]; ring
  rw [hA, hG, carlsonRPolynomialNumerator₂_smul,
    carlsonRPolynomialNumerator₂_transform n p q]
  rw [mul_assoc, ← mul_assoc ((-1 : ℂ) ^ n), ← mul_pow]
  simp

/-- Regression check: the version of the second quadratic identity with unsquared
right-hand nodes is false, already for `n = β = 1`, `x = 2`, `y = 0`. -/
theorem secondQuadratic_unsquared_counterexample :
    (ascPochhammer ℂ 1).eval (1 - 2 * 1 - 2 * 1) *
        carlsonRPolynomialNumerator₂ 1 1 1 (2 ^ 2) (0 ^ 2) ≠
      (ascPochhammer ℂ 1).eval 1 *
        carlsonRPolynomialNumerator₂ 1 (1 / 2 - 1 - 1) (1 / 2 - 1 - 1)
          (2 + 0) (2 - 0) := by
  norm_num [carlsonRPolynomialNumerator₂, Finset.Nat.antidiagonal_succ]

/-- Division-free polynomial form of Carlson's involutive transformation 6.10-3.
Both transformed nodes must be squared: both sides are homogeneous of degree `2 * n`
in `x,y`. Omitting the squares gives the false identity refuted above. -/
theorem carlsonRPolynomialNumerator₂_secondQuadratic
    (n : ℕ) (β x y : ℂ) :
    (ascPochhammer ℂ n).eval (1 - 2 * β - 2 * n) *
        carlsonRPolynomialNumerator₂ n β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ n).eval β *
        carlsonRPolynomialNumerator₂ n (1 / 2 - β - n) (1 / 2 - β - n)
          ((x + y) ^ 2) ((x - y) ^ 2) := by
  obtain ⟨m, rfl | rfl⟩ := n.even_or_odd'
  · let γ : ℂ := 1 / 2 - β - (2 * m : ℕ)
    have hg : 1 - 2 * β - 2 * (2 * m : ℕ) = 2 * γ := by dsimp [γ]; push_cast; ring
    have hp : γ + m = 1 - (β + m) - (1 / 2 - m) - m := by
      dsimp [γ]; push_cast; ring
    have hr : γ + 1 / 2 = 1 - (β + m) - m := by dsimp [γ]; push_cast; ring
    change (ascPochhammer ℂ (2 * m)).eval (1 - 2 * β - 2 * (2 * m : ℕ)) *
      carlsonRPolynomialNumerator₂ (2 * m) β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ (2 * m)).eval β *
        carlsonRPolynomialNumerator₂ (2 * m) γ γ ((x + y) ^ 2) ((x - y) ^ 2)
    rw [hg, (numerator₂_firstQuadratic m β (x ^ 2) (y ^ 2)).1,
      (numerator₂_firstQuadratic m γ ((x + y) ^ 2) ((x - y) ^ 2)).1,
      hp, numerator₂_rotated_quadratic, ascPochhammer_eval_double,
      show 2 * m = m + m by omega, ascPochhammer_add_eval β m m, hr, ascPochhammer_eval_reflect]
    ring
  · let γ : ℂ := 1 / 2 - β - (2 * m + 1 : ℕ)
    have hg : 1 - 2 * β - 2 * (2 * m + 1 : ℕ) = 2 * γ := by dsimp [γ]; push_cast; ring
    have hp : 1 + γ + m = 1 - (1 + β + m) - (-1 / 2 - m) - m := by
      dsimp [γ]; push_cast; ring
    have hr : γ + 1 / 2 = 1 - (β + (m + 1 : ℕ)) - m := by dsimp [γ]; push_cast; ring
    have hM : (((x + y) ^ 2 + (x - y) ^ 2) / 2 : ℂ) = 2 * ((x ^ 2 + y ^ 2) / 2) := by ring
    change (ascPochhammer ℂ (2 * m + 1)).eval (1 - 2 * β - 2 * (2 * m + 1 : ℕ)) *
      carlsonRPolynomialNumerator₂ (2 * m + 1) β β (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ (2 * m + 1)).eval β *
        carlsonRPolynomialNumerator₂ (2 * m + 1) γ γ ((x + y) ^ 2) ((x - y) ^ 2)
    have hd : (ascPochhammer ℂ (2 * m + 1)).eval (2 * γ) =
        2 * 4 ^ m * (ascPochhammer ℂ (m + 1)).eval γ *
          (ascPochhammer ℂ m).eval (γ + 1 / 2) := by
      rw [ascPochhammer_succ_eval, ascPochhammer_eval_double, ascPochhammer_succ_eval]
      push_cast
      ring
    rw [hg, (numerator₂_firstQuadratic m β (x ^ 2) (y ^ 2)).2,
      (numerator₂_firstQuadratic m γ ((x + y) ^ 2) ((x - y) ^ 2)).2,
      hp, numerator₂_rotated_quadratic, hd,
      show 2 * m + 1 = (m + 1) + m by omega, ascPochhammer_add_eval β (m + 1) m,
      hr, ascPochhammer_eval_reflect, hM]
    have hparam : β + (m + 1 : ℕ) = 1 + β + m := by push_cast; ring
    rw [hparam]
    ring

/- The parameter continuations are proved in `QuadraticContinuation` and `EqualParameter`.
Extending the branch-sensitive node domains remains separate work.
No Legendre, Chebyshev, Gegenbauer, or elliptic-integral
specialization belongs in this file. -/

end DirichletTransform.TwoVariable
