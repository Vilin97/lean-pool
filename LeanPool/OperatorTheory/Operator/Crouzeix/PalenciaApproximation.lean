/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.Palencia

/-!
# Crouzeix--Palencia assembly from approximate auxiliary bounds

Smooth-domain approximation naturally produces auxiliary operators whose
sharp bounds contain an arbitrarily small scalar error.  This file removes
that error after applying the algebraic Crouzeix--Palencia balance estimate.

## Main declarations

* `norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds` -- the
  abstract epsilon-limit form of the balance estimate.
* `crouzeix_palencia_of_approximate_auxiliary_bounds` -- the corresponding
  polynomial spectral-set package over the closure of the numerical range.
* `norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds` and
  `crouzeix_palencia_of_tendsto_auxiliary_bounds` -- sequence-limit forms
  suited to a smooth exhaustion.
-/

@[expose] public section

open Filter
open scoped InnerProductSpace

/-- If auxiliary operators satisfy the two sharp bounds with every positive
additive error in `m`, then the exact Crouzeix--Palencia estimate follows. -/
theorem norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F : B) {m : ℝ}
    (haux : ∀ ε : ℝ, 0 < ε → ∃ G : B,
      ‖F + star G‖ ≤ 2 * (m + ε) ∧ ‖F * G‖ ≤ (m + ε) ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  have hconstant : 0 < 1 + Real.sqrt 2 :=
    add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg 2)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < δ / (1 + Real.sqrt 2) := div_pos hδ hconstant
  obtain ⟨G, hsymm, hprod⟩ := haux (δ / (1 + Real.sqrt 2)) hε
  have hbound := norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds F G hsymm hprod
  calc
    ‖F‖ ≤ (1 + Real.sqrt 2) * (m + δ / (1 + Real.sqrt 2)) := hbound
    _ = (1 + Real.sqrt 2) * m + δ := by field_simp

/-- If the two auxiliary bounds hold along a scalar sequence converging to
`m`, then the exact Crouzeix--Palencia estimate follows. -/
theorem norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F : B) {m : ℝ} (M : ℕ → ℝ) (hM : Tendsto M atTop (nhds m))
    (haux : ∀ n : ℕ, ∃ G : B,
      ‖F + star G‖ ≤ 2 * M n ∧ ‖F * G‖ ≤ (M n) ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  apply norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds F
  intro ε hε
  have heventually : ∀ᶠ n in atTop, M n < m + ε :=
    (tendsto_order.mp hM).2 (m + ε) (lt_add_of_pos_right m hε)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨G, hsymm, hprod⟩ := haux n
  have hMnlt : M n < m + ε := hn n le_rfl
  have hMn : 0 ≤ M n := by
    linarith only [norm_nonneg (F + star G), hsymm]
  have hmε : 0 ≤ m + ε := hMn.trans hMnlt.le
  refine ⟨G, hsymm.trans ?_, hprod.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left hMnlt.le (by norm_num)
  · simp only [pow_two]
    exact mul_le_mul hMnlt.le hMnlt.le hMn hmε

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Approximate L4.2d/e auxiliary bounds for every polynomial suffice for
the exact Crouzeix--Palencia polynomial spectral-set conclusion. -/
theorem crouzeix_palencia_of_approximate_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ (p : Polynomial ℂ) (ε : ℝ), 0 < ε →
      ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤
            2 * (polynomialSupNorm p (closure (numericalRange A)) + ε) ∧
        ‖Polynomial.aeval A p * G‖ ≤
            (polynomialSupNorm p (closure (numericalRange A)) + ε) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    exact norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds
      (Polynomial.aeval A p) (fun ε hε => haux p ε hε)

/-- Stagewise L4.2d/e bounds controlled by sequences converging to the target
polynomial sup norms imply the exact spectral-set conclusion. -/
theorem crouzeix_palencia_of_tendsto_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ M : ℕ → ℝ,
      Tendsto M atTop
          (nhds (polynomialSupNorm p (closure (numericalRange A)))) ∧
      ∀ n : ℕ, ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * M n ∧
        ‖Polynomial.aeval A p * G‖ ≤ (M n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨M, hM, hstage⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds
      (Polynomial.aeval A p) M hM hstage

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
