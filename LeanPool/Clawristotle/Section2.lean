/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs

/-!
# Entropy Dissipation Identity (Section 2)

Properties of the Landau collision matrix: evenness, positive semidefiniteness,
the symmetrized weak form, and the entropy dissipation identity D(f) as a double integral.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 2: The Landau Collision Matrix
-- Reference: Definition 2 (def:landau_matrix), Lemmas 1-3
-- ============================================================================

-- ============================================================================
-- Lemma 1(b): A(z) is even: A(-z) = A(z)  [lem:A_symmetric]
-- ============================================================================

/-- Lemma 1(b): A(-z) = A(z). Reference: lem:A_symmetric -/
theorem landauMatrix_even (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    landauMatrix Ψ (-z) = landauMatrix Ψ z := by
  unfold landauMatrix innerLandauMatrix
  rw [eucNorm_neg, normSq_neg]
  congr 1
  ext i j
  simp [vecMulVec_apply]

-- ============================================================================
-- Lemma 2: Positive semidefiniteness of A(z)  [lem:A_psd]
-- ============================================================================

/-- The quadratic form of the inner Landau matrix:
    Yᵀ B(z) Y = |z|²|Y|² - (z·Y)². Reference: lem:A_psd -/
theorem innerLandauMatrix_quadForm (z Y : Fin 3 → ℝ) :
    dotProduct Y (mulVec (innerLandauMatrix z) Y) =
    normSq z * normSq Y - dotProduct z Y ^ 2 := by
  unfold innerLandauMatrix
  simp only [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_self_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, normSq]
  rw [dotProduct_comm z Y]
  ring

/-- Cauchy–Schwarz for dotProduct: (z·Y)² ≤ |z|²·|Y|².
    This follows from the Cauchy–Schwarz inequality. -/
theorem dotProduct_sq_le_normSq (z Y : Fin 3 → ℝ) :
    dotProduct z Y ^ 2 ≤ normSq z * normSq Y := by
  simp only [dotProduct, normSq, Fin.sum_univ_three, sq]
  nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
             sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
             sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]

/-- Lemma 2: Yᵀ A(z) Y ≥ 0 when Ψ(|z|) ≥ 0. Reference: lem:A_psd -/
theorem landauMatrix_posSemidef {Ψ : ℝ → ℝ} {z : Fin 3 → ℝ}
    (hΨ : 0 ≤ Ψ (eucNorm z)) (Y : Fin 3 → ℝ) :
    0 ≤ dotProduct Y (mulVec (landauMatrix Ψ z) Y) := by
  unfold landauMatrix
  rw [smul_mulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  apply mul_nonneg hΨ
  rw [innerLandauMatrix_quadForm]
  linarith [dotProduct_sq_le_normSq z Y]

/-- Lemma 2 (equality case): If Ψ(|z|) > 0, z ≠ 0, and the quadratic form vanishes,
    then Y is parallel to z. Reference: lem:A_psd -/
theorem landauMatrix_quadForm_eq_zero_iff {Ψ : ℝ → ℝ} {z : Fin 3 → ℝ}
    (hΨ : 0 < Ψ (eucNorm z)) (hz : z ≠ 0)
    (Y : Fin 3 → ℝ)
    (h : dotProduct Y (mulVec (landauMatrix Ψ z) Y) = 0) :
    ∃ l : ℝ, Y = l • z := by
  -- Step 1: Factor out Ψ > 0 to get the inner quadratic form = 0
  have hinner : dotProduct Y (mulVec (innerLandauMatrix z) Y) = 0 := by
    have hqf : Ψ (eucNorm z) * dotProduct Y (mulVec (innerLandauMatrix z) Y) = 0 := by
      have : dotProduct Y (mulVec (landauMatrix Ψ z) Y) =
        Ψ (eucNorm z) * dotProduct Y (mulVec (innerLandauMatrix z) Y) := by
        unfold landauMatrix
        rw [smul_mulVec]
        simp [dotProduct_smul, smul_eq_mul]
      linarith
    exact (mul_eq_zero.mp hqf).resolve_left (ne_of_gt hΨ)
  -- Step 2: Cauchy-Schwarz equality: normSq z * normSq Y = (z . Y)^2
  have heq : normSq z * normSq Y = dotProduct z Y ^ 2 := by
    have := innerLandauMatrix_quadForm z Y; linarith
  -- Step 3: Expand on Fin 3 to show all cross terms vanish
  have hcross :
      (z 0 * Y 1 - z 1 * Y 0) ^ 2 + (z 0 * Y 2 - z 2 * Y 0) ^ 2 +
      (z 1 * Y 2 - z 2 * Y 1) ^ 2 = 0 := by
    simp only [dotProduct, normSq, Fin.sum_univ_three, sq] at heq
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  -- Step 4: Extract individual proportionality relations z_i * Y_j = z_j * Y_i
  have h01 : z 0 * Y 1 = z 1 * Y 0 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  have h02 : z 0 * Y 2 = z 2 * Y 0 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  have h12 : z 1 * Y 2 = z 2 * Y 1 := by
    nlinarith [sq_nonneg (z 0 * Y 1 - z 1 * Y 0),
               sq_nonneg (z 0 * Y 2 - z 2 * Y 0),
               sq_nonneg (z 1 * Y 2 - z 2 * Y 1)]
  -- Step 5: Since z != 0, find a nonzero component and set l = Y_k / z_k
  have hne : ¬(z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0) := by
    intro ⟨h0, h1, h2⟩
    apply hz
    ext i
    fin_cases i <;> assumption
  rcases not_and_or.mp hne with h0 | h12ne
  · -- Case z 0 != 0: let l = Y 0 / z 0
    refine ⟨Y 0 / z 0, ?_⟩
    ext i; fin_cases i
    · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
    · simp [Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith [h01]
    · simp [Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith [h02]
  · rcases not_and_or.mp h12ne with h1 | h2
    · -- Case z 1 != 0: let l = Y 1 / z 1
      refine ⟨Y 1 / z 1, ?_⟩
      ext i; fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith [h01]
      · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h1]
      · simp [Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith [h12]
    · -- Case z 2 != 0: let l = Y 2 / z 2
      refine ⟨Y 2 / z 2, ?_⟩
      ext i; fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith [h02]
      · simp [Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith [h12]
      · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h2]

-- ============================================================================
-- Lemma 3: Projection annihilation: A(z) z = 0  [lem:zA_zero]
-- ============================================================================

/-- B(z) z = 0 (the inner matrix annihilates z). -/
theorem innerLandauMatrix_mulVec_self (z : Fin 3 → ℝ) :
    mulVec (innerLandauMatrix z) z = 0 := by
  unfold innerLandauMatrix
  simp only [sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_self_mulVec, normSq]
  ext i
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self]

/-- Lemma 3: A(z) z = 0. Reference: lem:zA_zero -/
theorem landauMatrix_mulVec_self (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    mulVec (landauMatrix Ψ z) z = 0 := by
  unfold landauMatrix
  rw [smul_mulVec, innerLandauMatrix_mulVec_self, smul_zero]

end VML
