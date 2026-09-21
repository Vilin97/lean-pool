/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal

open MeasureTheory Set

namespace QuadraticCarleson


/-- Expose the three sparse witnesses arising from three operator bounds.
No union of the three families is asserted here. -/
theorem exists_three_sparseBounds_of_pairing_le_three
    {C₁ C₂ C₃ p : ℝ} {T T₁ T₂ T₃ : TestOperator}
    (hdom : ∀ f g : L0Infinity,
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ENNReal.ofReal ‖operatorPairing T₁ f g‖ +
          ENNReal.ofReal ‖operatorPairing T₂ f g‖ +
            ENNReal.ofReal ‖operatorPairing T₃ f g‖)
    (h₁ : HasSparseOnePBound C₁ p T₁)
    (h₂ : HasSparseOnePBound C₂ p T₂)
    (h₃ : HasSparseOnePBound C₃ p T₃) :
    ∀ f g : L0Infinity, ∃ S₁ S₂ S₃ : Set RealInterval,
      IsSparse (1 / 4) S₁ ∧ IsSparse (1 / 4) S₂ ∧ IsSparse (1 / 4) S₃ ∧
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ENNReal.ofReal C₁ * sparseForm p f g S₁ +
          ENNReal.ofReal C₂ * sparseForm p f g S₂ +
            ENNReal.ofReal C₃ * sparseForm p f g S₃ := by
  intro f g
  rcases h₁ f g with ⟨S₁, hS₁, hb₁⟩
  rcases h₂ f g with ⟨S₂, hS₂, hb₂⟩
  rcases h₃ f g with ⟨S₃, hS₃, hb₃⟩
  refine ⟨S₁, S₂, S₃, hS₁, hS₂, hS₃, ?_⟩
  exact (hdom f g).trans (add_le_add (add_le_add hb₁ hb₂) hb₃)

/-- Three sparse operator bounds combine into one sparse operator bound.

For the given test functions, choose whichever of the three sparse forms is
largest.  Its family remains `1 / 4`-sparse, and the sum of the three
coefficients absorbs the other two forms.  Thus no geometric union, and in
particular no false disjointness assertion about the three shifted grids, is
needed. -/
theorem hasSparseOnePBound_of_pairing_le_three
    {C₁ C₂ C₃ p : ℝ} {T T₁ T₂ T₃ : TestOperator}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hdom : ∀ f g : L0Infinity,
      ENNReal.ofReal ‖operatorPairing T f g‖ ≤
        ENNReal.ofReal ‖operatorPairing T₁ f g‖ +
          ENNReal.ofReal ‖operatorPairing T₂ f g‖ +
            ENNReal.ofReal ‖operatorPairing T₃ f g‖)
    (h₁ : HasSparseOnePBound C₁ p T₁)
    (h₂ : HasSparseOnePBound C₂ p T₂)
    (h₃ : HasSparseOnePBound C₃ p T₃) :
    HasSparseOnePBound (C₁ + C₂ + C₃) p T := by
  intro f g
  rcases h₁ f g with ⟨S₁, hS₁, hb₁⟩
  rcases h₂ f g with ⟨S₂, hS₂, hb₂⟩
  rcases h₃ f g with ⟨S₃, hS₃, hb₃⟩
  have hbound : ENNReal.ofReal ‖operatorPairing T f g‖ ≤
      ENNReal.ofReal C₁ * sparseForm p f g S₁ +
        ENNReal.ofReal C₂ * sparseForm p f g S₂ +
          ENNReal.ofReal C₃ * sparseForm p f g S₃ := by
    exact (hdom f g).trans (add_le_add (add_le_add hb₁ hb₂) hb₃)
  rcases le_total (sparseForm p f g S₁) (sparseForm p f g S₂) with h₁₂ | h₂₁
  · rcases le_total (sparseForm p f g S₂) (sparseForm p f g S₃) with h₂₃ | h₃₂
    · refine ⟨S₃, hS₃, hbound.trans ?_⟩
      rw [ENNReal.ofReal_add (add_nonneg hC₁ hC₂) hC₃,
        ENNReal.ofReal_add hC₁ hC₂, add_mul, add_mul]
      exact add_le_add
        (add_le_add (mul_le_mul' le_rfl (h₁₂.trans h₂₃))
          (mul_le_mul' le_rfl h₂₃)) le_rfl
    · refine ⟨S₂, hS₂, hbound.trans ?_⟩
      rw [ENNReal.ofReal_add (add_nonneg hC₁ hC₂) hC₃,
        ENNReal.ofReal_add hC₁ hC₂, add_mul, add_mul]
      exact add_le_add (add_le_add (mul_le_mul' le_rfl h₁₂) le_rfl)
        (mul_le_mul' le_rfl h₃₂)
  · rcases le_total (sparseForm p f g S₁) (sparseForm p f g S₃) with h₁₃ | h₃₁
    · refine ⟨S₃, hS₃, hbound.trans ?_⟩
      rw [ENNReal.ofReal_add (add_nonneg hC₁ hC₂) hC₃,
        ENNReal.ofReal_add hC₁ hC₂, add_mul, add_mul]
      exact add_le_add
        (add_le_add (mul_le_mul' le_rfl h₁₃)
          (mul_le_mul' le_rfl (h₂₁.trans h₁₃))) le_rfl
    · refine ⟨S₁, hS₁, hbound.trans ?_⟩
      rw [ENNReal.ofReal_add (add_nonneg hC₁ hC₂) hC₃,
        ENNReal.ofReal_add hC₁ hC₂, add_mul, add_mul]
      exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h₂₁))
        (mul_le_mul' le_rfl h₃₁)


end QuadraticCarleson
