/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.BigOperators

/-!

# Some stuff about complex numbers

This file contains some basic lemmas about complex numbers.

-/


open scoped ComplexConjugate BigOperators

open Complex

/--
The norm of `∑ i, α i ^ 2` is the sum of `‖α i‖ ^ 2` if and only if
the real and imaginary parts of the `α i` are pairwise proportional.
-/
theorem norm_of_sum_sq_eq_sum_norm_sq_iff {n : Type _} [Fintype n] (α : n → ℂ) :
    ‖(∑ i : n, α i ^ 2)‖ = ∑ i : n, ‖(α i)‖ ^ 2 ↔
      ∀ i j : n, (α i).re * (α j).im = (α j).re * (α i).im := by
  have complex.abs_sq : ∀ x : ℂ, ‖x‖ ^ 2 = Complex.normSq x := by
    intros
    simp_rw [norm_def, Real.sq_sqrt (normSq_nonneg _)]
  simp_rw [complex.abs_sq, norm_def]
  rw [Real.sqrt_eq_iff_eq_sq (normSq_nonneg _), eq_comm, pow_two, Finset.sum_mul_sum]
  · simp_rw [← normSq_mul, normSq_apply, re_sum, im_sum, Finset.sum_mul_sum, ←
      Finset.sum_add_distrib, pow_two, mul_re, mul_im, sub_mul, mul_sub, mul_add, add_mul]
    rw [← sub_eq_zero]
    have aux_for_ex :
      ∀ x : n × n,
        (α x.fst).re * (α x.snd).re * ((α x.fst).re * (α x.snd).re) -
                  (α x.fst).re * (α x.snd).re * ((α x.fst).im * (α x.snd).im) -
                ((α x.fst).im * (α x.snd).im * ((α x.fst).re * (α x.snd).re) -
                  (α x.fst).im * (α x.snd).im * ((α x.fst).im * (α x.snd).im)) +
              ((α x.fst).re * (α x.snd).im * ((α x.fst).re * (α x.snd).im) +
                  (α x.fst).im * (α x.snd).re * ((α x.fst).re * (α x.snd).im) +
                ((α x.fst).re * (α x.snd).im * ((α x.fst).im * (α x.snd).re) +
                  (α x.fst).im * (α x.snd).re * ((α x.fst).im * (α x.snd).re))) -
            ((α x.fst).re * (α x.fst).re * ((α x.snd).re * (α x.snd).re) -
                  (α x.fst).re * (α x.fst).re * ((α x.snd).im * (α x.snd).im) -
                ((α x.fst).im * (α x.fst).im * ((α x.snd).re * (α x.snd).re) -
                  (α x.fst).im * (α x.fst).im * ((α x.snd).im * (α x.snd).im)) +
              ((α x.fst).re * (α x.fst).im * ((α x.snd).re * (α x.snd).im) +
                  (α x.fst).im * (α x.fst).re * ((α x.snd).re * (α x.snd).im) +
                ((α x.fst).re * (α x.fst).im * ((α x.snd).im * (α x.snd).re) +
                  (α x.fst).im * (α x.fst).re * ((α x.snd).im * (α x.snd).re)))) =
          2 *
            (((α x.snd).im * (α x.fst).re) ^ 2 -
                2 * ((α x.snd).im * (α x.fst).re) * ((α x.fst).im * (α x.snd).re) +
              ((α x.fst).im * (α x.snd).re) ^ 2) := by
      intros
      simp_rw [← pow_two, sub_sub, mul_comm, ← two_mul]
      ring_nf
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_product', Finset.univ_product_univ,
      aux_for_ex, ← sub_sq, ← Finset.mul_sum, mul_eq_zero, two_ne_zero, false_or]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    · simp_rw [Finset.mem_univ, true_imp_iff, Prod.forall, sq_eq_zero_iff, sub_eq_zero,
        mul_comm]
    · simp_rw [Finset.mem_univ, true_imp_iff, sq_nonneg, forall_true_iff]
  · apply Finset.sum_nonneg
    intros
    exact normSq_nonneg _

theorem norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff (α₁ α₂ : ℂ) :
    norm (α₁ ^ 2 + α₂ ^ 2) = norm α₁ ^ 2 + norm α₂ ^ 2 ↔
      α₁.re * α₂.im = α₂.re * α₁.im := by
  let α := ![α₁, α₂]
  have h₀ : α 0 = α₁ := rfl
  have h₁ : α 1 = α₂ := rfl
  have hy :
    norm (∑ i : Fin 2, α i ^ 2) = norm (α 0 ^ 2 + α 1 ^ 2) ∧
      ∑ i : Fin 2, norm (α i) ^ 2 = norm (α 0) ^ 2 + norm (α 1) ^ 2 := by
    simp [Fin.sum_univ_two]
  simp_rw [← h₀, ← h₁, ← hy.1, ← hy.2, norm_of_sum_sq_eq_sum_norm_sq_iff,
    Fin.forall_fin_two, h₀, h₁, true_and, and_true, eq_comm, and_self_iff]

theorem norm_of_sq_add_sq_norm_sq_add_norm_sq_iff' (α₁ α₂ : ℂ) :
    norm (α₁ ^ 2 + α₂ ^ 2) = norm α₁ ^ 2 + norm α₂ ^ 2 ↔ α₁ * conj α₂ = conj α₁ * α₂ := by
  rw [norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff, ← re_add_im α₁, ← re_add_im α₂]
  simp_rw [add_re, add_im, map_add, conj_ofReal, mul_I_im, mul_I_re, starRingEnd_apply, star_mul',
    ← starRingEnd_apply, conj_I, conj_ofReal, mul_add, add_mul]
  simp only [ofReal_re, ofReal_im, MulZeroClass.mul_zero, neg_zero, add_zero,
    MulZeroClass.zero_mul, zero_add, mul_neg, neg_mul, mul_comm _ I, mul_mul_mul_comm, I_mul_I,
    neg_neg, one_mul]
  simp_rw [add_assoc, add_right_inj, ← add_assoc, add_left_inj, mul_comm _ (I * _),
    add_comm (- ((I * _) * _)) _, ← sub_eq_add_neg, mul_assoc, ← mul_sub, mul_right_inj' I_ne_zero,
    ← ofReal_mul, ← ofReal_sub]
  norm_cast
  simp_rw [sub_eq_sub_iff_add_eq_add, ← two_mul, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
    or_false, mul_comm _ (Complex.re _), eq_comm]

/--
The norm identity for a finite sum of squares is equivalent to saying that
`α i * conj (α j) = conj (α i) * α j` for every pair `i`, `j`.
-/
theorem norm_of_sum_sq_eq_sum_norm_sq_iff' {n : Type _} [Fintype n] (α : n → ℂ) :
    norm (∑ i : n, α i ^ 2) = ∑ i : n, norm (α i) ^ 2 ↔
      ∀ i j : n, α i * conj (α j) = conj (α i) * α j := by
  have := norm_of_sq_add_sq_norm_sq_add_norm_sq_iff'
  simp_rw [norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff] at this
  simp_rw [norm_of_sum_sq_eq_sum_norm_sq_iff, this]

theorem norm_of_sq_add_sq_norm_sq_add_norm_sq_iff'' (α₁ α₂ : ℂ) :
    norm (α₁ ^ 2 + α₂ ^ 2) = norm α₁ ^ 2 + norm α₂ ^ 2 ↔
      ∃ (γ : ℂ) (β₁ β₂ : ℝ), α₁ = γ * β₁ ∧ α₂ = γ * β₂ := by
  rw [norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff]
  constructor
  · intro h
    rw [← re_add_im α₂, ← re_add_im α₁]
    by_cases h1 : α₂.im = 0
    · by_cases h2 : α₂.re = 0
      · rw [h1, h2, ofReal_zero, zero_add, MulZeroClass.zero_mul]
        use α₁
        use 1
        use 0
        simp_rw [re_add_im, ofReal_zero, MulZeroClass.mul_zero, ofReal_one, mul_one,
          true_and]
      have : α₂.re = 0 ∨ α₁.im = 0 := by rw [← mul_eq_zero, ← h, h1, MulZeroClass.mul_zero]
      rcases this with (this | this)
      · contradiction
      · use 1
        use α₁.re
        use α₂.re
        simp_rw [h1, this, ofReal_zero, MulZeroClass.zero_mul, add_zero, one_mul, and_self_iff]
    by_cases h2 : α₂.re = 0
    · have : α₁.re = 0 ∨ α₂.im = 0 := by rw [← mul_eq_zero, h, h2, MulZeroClass.zero_mul]
      rcases this with (this | this)
      · use I
        use α₁.im
        use α₂.im
        simp_rw [h2, this, ofReal_zero, zero_add, mul_comm, and_self_iff]
      · contradiction
    use 1 / α₂.im + I * (1 / α₂.re)
    use α₁.re * α₂.im
    use α₂.im * α₂.re
    push Not at h1 h2
    simp_rw [add_mul, one_div, ← ofReal_inv, ← ofReal_mul, mul_comm, mul_assoc,
      mul_inv_cancel₀ h1, mul_one, h, ofReal_mul, mul_rotate _ _ (I * _), mul_assoc,
      ← ofReal_mul, inv_mul_cancel₀ h2, ofReal_one, mul_one, mul_comm I _, and_self]
  · rintro ⟨γ, β₁, β₂, ⟨rfl, rfl⟩⟩
    simp_rw [mul_comm γ _, re_ofReal_mul, im_ofReal_mul, mul_mul_mul_comm, mul_comm]

/--
The norm identity for a finite sum of squares is equivalent to all `α i`
lying on a common complex line through the origin with real coefficients.
-/
theorem norm_of_sum_sq_eq_sum_norm_sq_iff'' {n : Type _} [Fintype n] (α : n → ℂ) :
    norm (∑ i : n, α i ^ 2) = ∑ i : n, norm (α i) ^ 2 ↔
      ∃ γ : ℂ, ∀ i : n, ∃ β : ℝ, α i = γ * β := by
  have := norm_of_sq_add_sq_norm_sq_add_norm_sq_iff''
  simp_rw [norm_of_sq_add_sq_eq_norm_sq_add_norm_sq_iff] at this
  simp_rw [norm_of_sum_sq_eq_sum_norm_sq_iff, this]
  constructor
  · intro h
    by_cases H : α = 0
    · use 0
      intros
      use 0
      simp_rw [H, Pi.zero_apply, MulZeroClass.zero_mul]
    · have : ∃ i : n, α i ≠ 0 := by simp_rw [ne_eq, ← not_forall, ← funext_iff]; exact H
      have := this
      rcases this with ⟨i, hi⟩
      rcases this with ⟨j, hj⟩
      obtain ⟨γ, β₁, β₂, ⟨hβ₁, _⟩⟩ := h i j
      use γ
      intro k
      obtain ⟨γ₂, β₃, β₄, ⟨hβ₃, hβ₄⟩⟩ := h i k
      by_cases h' : β₃ = 0
      · simp_rw [h', ofReal_zero, MulZeroClass.mul_zero] at hβ₃
        contradiction
      · use β₁ * (β₄ / β₃)
        simp_rw [ofReal_mul, ← mul_assoc, ← hβ₁, hβ₃, mul_assoc, ← ofReal_mul,
          mul_div_cancel₀ _ h', hβ₄]
  · rintro ⟨γ, hγ⟩ i j
    obtain ⟨β₁, hβ₁⟩ := hγ i
    obtain ⟨β₂, hβ₂⟩ := hγ j
    exact ⟨γ, β₁, β₂, ⟨hβ₁, hβ₂⟩⟩
