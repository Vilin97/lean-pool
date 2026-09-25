/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExactData

/-!
# Davis--Kahan 1970, Section 9: affine trial subspace

The two zero-mode trial functions are affine in the centered coordinate
`x = 2t - 1`.  Their required `L2(0,1)` calculations depend only on the first
four centered moments.  This module packages those moments as exact bilinear
forms and derives the Ritz and residual matrices algebraically.

This is a transformative finite-moment reconstruction, not a copy of the
source prose.  A later integration lemma may identify these forms with actual
Lebesgue integrals on the unit interval.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- An affine function represented as `constant + centered * (2t - 1)`. -/
structure CenteredAffine where
  /-- The constant coefficient in the centered affine representation. -/
  fixedValue : ℝ
  /-- The coefficient of the centered coordinate `2t - 1`. -/
  centered : ℝ

namespace CenteredAffine

/-- Unit-interval `L2` inner product of two centered affine functions. -/
noncomputable def inner (p q : CenteredAffine) : ℝ :=
  p.fixedValue * q.fixedValue + p.centered * q.centered / 3

/-- Inner product after multiplication of the second function by `t`. -/
noncomputable def tInner (p q : CenteredAffine) : ℝ :=
  p.fixedValue * q.fixedValue / 2
    + (p.fixedValue * q.centered + p.centered * q.fixedValue) / 6
    + p.centered * q.centered / 6

/-- Inner product after multiplication of the second function by `t^2`. -/
noncomputable def tSqInner (p q : CenteredAffine) : ℝ :=
  p.fixedValue * q.fixedValue / 3
    + (p.fixedValue * q.centered + p.centered * q.fixedValue) / 6
    + 2 * p.centered * q.centered / 15

/-- The affine inner product is symmetric. -/
lemma inner_symm (p q : CenteredAffine) : inner p q = inner q p := by
  unfold inner
  ring

/-- The `t`-weighted inner product is symmetric. -/
lemma tInner_symm (p q : CenteredAffine) : tInner p q = tInner q p := by
  unfold tInner
  ring

/-- The `t²`-weighted inner product is symmetric. -/
lemma tSqInner_symm (p q : CenteredAffine) : tSqInner p q = tSqInner q p := by
  unfold tSqInner
  ring

end CenteredAffine

/-- First normalized affine zero mode. -/
noncomputable def trialOne : CenteredAffine where
  fixedValue := Real.sqrt 2 / 2
  centered := -(Real.sqrt 2 * Real.sqrt 3 / 2)

/-- Second normalized affine zero mode. -/
noncomputable def trialTwo : CenteredAffine where
  fixedValue := Real.sqrt 2 / 2
  centered := Real.sqrt 2 * Real.sqrt 3 / 2

private lemma sqrt75_eq_five_mul_sqrt3 :
    Real.sqrt 75 = 5 * Real.sqrt 3 := by
  have h75 : Real.sqrt (75 : ℝ) ^ 2 = 75 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h75nonneg := Real.sqrt_nonneg (75 : ℝ)
  have h3nonneg := Real.sqrt_nonneg (3 : ℝ)
  nlinarith [sq_nonneg (Real.sqrt 75 - 5 * Real.sqrt 3)]

/-- The first trial function is a unit vector in `L²(0,1)`. -/
lemma trialOne_norm_sq : CenteredAffine.inner trialOne trialOne = 1 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.inner trialOne
  dsimp
  nlinarith

/-- The second trial function is a unit vector in `L²(0,1)`. -/
lemma trialTwo_norm_sq : CenteredAffine.inner trialTwo trialTwo = 1 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.inner trialTwo
  dsimp
  nlinarith

/-- The two trial functions are orthogonal, so together they form an orthonormal
basis of the trial subspace. -/
lemma trialOne_inner_trialTwo : CenteredAffine.inner trialOne trialTwo = 0 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.inner trialOne trialTwo
  dsimp
  nlinarith

/-- The `t`-form is diagonalised by the trial pair, and its first diagonal entry is
the lower Ritz coefficient — this is where the Ritz value of equation (9.5)
comes from. -/
lemma trialOne_tInner_trialOne :
    CenteredAffine.tInner trialOne trialOne = ritzLowCoefficient := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.tInner trialOne ritzLowCoefficient
  dsimp
  -- the `centered * centered` term needs the product of `h2` and `h3`, which
  -- `nlinarith` will not form on its own
  linear_combination (1 / 4 - Real.sqrt 3 / 12) * h2 +
    (1 / 12 + (Real.sqrt 2 ^ 2 - 2) / 24) * h3

/-- Second diagonal entry of the `t`-form: the upper Ritz coefficient. -/
lemma trialTwo_tInner_trialTwo :
    CenteredAffine.tInner trialTwo trialTwo = ritzHighCoefficient := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.tInner trialTwo ritzHighCoefficient
  dsimp
  linear_combination (1 / 4 + Real.sqrt 3 / 12) * h2 +
    (1 / 12 + (Real.sqrt 2 ^ 2 - 2) / 24) * h3

/-- The `t`-form has no off-diagonal part in the trial basis, which is what makes the
trial pair a Ritz basis. -/
lemma trialOne_tInner_trialTwo :
    CenteredAffine.tInner trialOne trialTwo = 0 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.tInner trialOne trialTwo
  dsimp
  nlinarith

/-- First diagonal entry of the `t²`-form: `(11 - √75) / 30`. -/
lemma trialOne_tSqInner_trialOne :
    CenteredAffine.tSqInner trialOne trialOne =
      (11 - Real.sqrt 75) / 30 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [sqrt75_eq_five_mul_sqrt3]
  unfold CenteredAffine.tSqInner trialOne
  dsimp
  linear_combination (11 / 60 - Real.sqrt 3 / 12) * h2 +
    (1 / 15 + (Real.sqrt 2 ^ 2 - 2) / 30) * h3

/-- Second diagonal entry of the `t²`-form: `(11 + √75) / 30`. -/
lemma trialTwo_tSqInner_trialTwo :
    CenteredAffine.tSqInner trialTwo trialTwo =
      (11 + Real.sqrt 75) / 30 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [sqrt75_eq_five_mul_sqrt3]
  unfold CenteredAffine.tSqInner trialTwo
  dsimp
  linear_combination (11 / 60 + Real.sqrt 3 / 12) * h2 +
    (1 / 15 + (Real.sqrt 2 ^ 2 - 2) / 30) * h3

/-- The `t²`-form is **not** diagonal in the trial basis: its off-diagonal entry is
`-1/30`.  That nonzero entry is exactly why the residual does not vanish. -/
lemma trialOne_tSqInner_trialTwo :
    CenteredAffine.tSqInner trialOne trialTwo = -(1 : ℝ) / 30 := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold CenteredAffine.tSqInner trialOne trialTwo
  dsimp
  nlinarith

/-- The multiplication-by-`epsilon t` compression is the diagonal Ritz matrix
from equation (9.5). -/
theorem ritz_matrix_from_affine_moments (ε : ℝ) :
    ε * CenteredAffine.tInner trialOne trialOne = ritzLow ε ∧
    ε * CenteredAffine.tInner trialOne trialTwo = 0 ∧
    ε * CenteredAffine.tInner trialTwo trialTwo = ritzHigh ε := by
  constructor
  · rw [trialOne_tInner_trialOne]
    rfl
  constructor
  · rw [trialOne_tInner_trialTwo, mul_zero]
  · rw [trialTwo_tInner_trialTwo]
    rfl

/-- The initial residual Gram matrix follows from the weighted second moments. -/
theorem initial_residual_gram_from_affine_moments (ε : ℝ) :
    SymmetricTwoByTwo.mk
      (ε ^ 2 * CenteredAffine.tSqInner trialOne trialOne)
      (ε ^ 2 * CenteredAffine.tSqInner trialOne trialTwo)
      (ε ^ 2 * CenteredAffine.tSqInner trialTwo trialTwo) = residualGram ε := by
  ext <;>
    simp [residualGram, trialOne_tSqInner_trialOne,
      trialOne_tSqInner_trialTwo, trialTwo_tSqInner_trialTwo] <;>
    ring

/-- Subtracting the squared Ritz compression gives the rank-one recentered
residual Gram matrix. -/
theorem recentered_residual_gram_from_affine_moments (ε : ℝ) :
    SymmetricTwoByTwo.mk
      (ε ^ 2 * (CenteredAffine.tSqInner trialOne trialOne -
        CenteredAffine.tInner trialOne trialOne ^ 2))
      (ε ^ 2 * (CenteredAffine.tSqInner trialOne trialTwo -
        CenteredAffine.tInner trialOne trialOne *
          CenteredAffine.tInner trialOne trialTwo))
      (ε ^ 2 * (CenteredAffine.tSqInner trialTwo trialTwo -
        CenteredAffine.tInner trialTwo trialTwo ^ 2)) =
      orthogonalResidualGram ε := by
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- without `sqrt75_eq_five_mul_sqrt3` the goal carries both `√75` and `√3`
  -- with nothing relating them; the off-diagonal entry is pure `ring`, the two
  -- diagonal entries each need one use of `h3`
  ext <;>
    simp [orthogonalResidualGram, trialOne_tSqInner_trialOne,
      trialOne_tSqInner_trialTwo, trialTwo_tSqInner_trialTwo,
      trialOne_tInner_trialOne, trialOne_tInner_trialTwo,
      trialTwo_tInner_trialTwo, ritzLowCoefficient,
      ritzHighCoefficient, sqrt75_eq_five_mul_sqrt3] <;>
    first
      | ring1
      | linear_combination (-(ε ^ 2) / 36) * h3

end Section9
end DavisKahan1970
end TauCeti
