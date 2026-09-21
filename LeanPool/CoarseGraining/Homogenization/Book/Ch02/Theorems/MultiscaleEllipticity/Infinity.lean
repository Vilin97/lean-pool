/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.SmallTail

/-! # Infinity -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Infinite-Depth Chapter 2.5 Multiscale Ellipticity

This file proves the `q = infinity` boundedness, positivity, monotonicity, and
one-cube comparison lemmas.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius


theorem LambdaSqInfinity_valueSet_bddAbove {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 ≤ s) :
    BddAbove
      { M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹ *
    (a.coeffOn Q).Lam ^ 2
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine ⟨C, ?_⟩
  rintro M ⟨n, rfl⟩
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hBound :
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C := by
    calc
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
          Homogenization.maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A := by
          simpa [A] using
            maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
              (a := a) Q hk
      _ ≤ C := by
          simpa [A, C] using
            Homogenization.maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              (Q := Q) (a := A) hEll hData n
  have hMaxNonneg :
      0 ≤ maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    maxDescendantBMatrixNormAtScale_nonneg Q hk a
  have hWeight : Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) ≤ 1 :=
    infinityWeight_le_one hs n
  have hMul :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
        1 * C :=
    mul_le_mul hWeight hBound hMaxNonneg zero_le_one
  simpa using hMul

theorem lambdaSqInfinity_denominator_valueSet_bddAbove {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 ≤ s) :
    BddAbove
      { M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine ⟨C, ?_⟩
  rintro M ⟨n, rfl⟩
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hBound :
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C := by
    calc
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
          Homogenization.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A := by
          simpa [A] using
            maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
              (a := a) Q hk
      _ ≤ C := by
          simpa [A, C] using
            Homogenization.maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
              (Q := Q) (a := A) hEll hData n
  have hMaxNonneg :
      0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk a
  have hWeight : Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) ≤ 1 :=
    infinityWeight_le_one hs n
  have hMul :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
        1 * C :=
    mul_le_mul hWeight hBound hMaxNonneg zero_le_one
  simpa using hMul

theorem oneCube_b_le_LambdaSq_infinity {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    coarseBMatrixNorm Q a ≤ LambdaSq Q s .infinity a := by
  have hbdd := LambdaSqInfinity_valueSet_bddAbove Q a hs.le
  have hmem :
      coarseBMatrixNorm Q a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
    refine ⟨0, ?_⟩
    simp [maxDescendantBMatrixNormAtScale_self]
  simpa [LambdaSq, LambdaSqInfinity] using le_csSup hbdd hmem

theorem LambdaSq_infinity_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    0 < LambdaSq Q s .infinity a :=
  lt_of_lt_of_le (coarseBMatrixNorm_pos Q a)
    (oneCube_b_le_LambdaSq_infinity Q a hs)

theorem LambdaSq_infinity_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    0 ≤ LambdaSq Q s .infinity a :=
  (LambdaSq_infinity_pos Q a hs).le

theorem lambdaSqInfinity_denominator_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    0 <
      sSup
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
  have hbdd := lambdaSqInfinity_denominator_valueSet_bddAbove Q a hs.le
  have hmem :
      coarseSigmaStarInvMatrixNorm Q a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
    refine ⟨0, ?_⟩
    simp [maxDescendantSigmaStarInvMatrixNormAtScale_self]
  exact lt_of_lt_of_le (coarseSigmaStarInvMatrixNorm_pos Q a) (le_csSup hbdd hmem)

theorem lambdaSq_infinity_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    0 < lambdaSq Q s .infinity a := by
  unfold lambdaSq lambdaSqInfinity
  exact inv_pos.mpr (lambdaSqInfinity_denominator_pos Q a hs)

theorem lambdaSq_infinity_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    0 ≤ lambdaSq Q s .infinity a :=
  (lambdaSq_infinity_pos Q a hs).le

theorem lambdaSq_infinity_le_oneCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    lambdaSq Q s .infinity a ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹ := by
  let S : ℝ :=
    sSup
      { M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }
  have hSpos : 0 < S := by
    simpa [S] using lambdaSqInfinity_denominator_pos Q a hs
  have hSigpos : 0 < coarseSigmaStarInvMatrixNorm Q a :=
    coarseSigmaStarInvMatrixNorm_pos Q a
  have hbdd := lambdaSqInfinity_denominator_valueSet_bddAbove Q a hs.le
  have hmem :
      coarseSigmaStarInvMatrixNorm Q a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
    refine ⟨0, ?_⟩
    simp [maxDescendantSigmaStarInvMatrixNormAtScale_self]
  have hle : coarseSigmaStarInvMatrixNorm Q a ≤ S := by
    simpa [S] using le_csSup hbdd hmem
  have hconverted : S⁻¹ ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹ :=
    (inv_le_inv₀ hSpos hSigpos).2 hle
  simpa [S, lambdaSq, lambdaSqInfinity] using hconverted

theorem LambdaSq_infinity_antitone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    LambdaSq Q s .infinity a ≤ LambdaSq Q t .infinity a := by
  have hbdd_t := LambdaSqInfinity_valueSet_bddAbove Q a ht.le
  have hne_s :
      ({ M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  unfold LambdaSq LambdaSqInfinity
  refine csSup_le hne_s ?_
  rintro M ⟨n, rfl⟩
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hmax :
      0 ≤ maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    maxDescendantBMatrixNormAtScale_nonneg Q hk a
  have hterm :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
        Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    mul_le_mul_of_nonneg_right (infinityWeight_le_of_le hts.le n) hmax
  exact hterm.trans
    (le_csSup hbdd_t ⟨n, rfl⟩)

theorem lambdaSqInfinity_denominator_antitone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    sSup
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } ≤
      sSup
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
  have hbdd_t := lambdaSqInfinity_denominator_valueSet_bddAbove Q a ht.le
  have hne_s :
      ({ M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  refine csSup_le hne_s ?_
  rintro M ⟨n, rfl⟩
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hmax :
      0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk a
  have hterm :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤
        Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    mul_le_mul_of_nonneg_right (infinityWeight_le_of_le hts.le n) hmax
  exact hterm.trans
    (le_csSup hbdd_t ⟨n, rfl⟩)

theorem lambdaSq_infinity_mono {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    lambdaSq Q t .infinity a ≤ lambdaSq Q s .infinity a := by
  let St : ℝ :=
    sSup
      { M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * t * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }
  let Ss : ℝ :=
    sSup
      { M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }
  have hden : Ss ≤ St := by
    simpa [Ss, St] using lambdaSqInfinity_denominator_antitone Q a ht hts
  have hStpos : 0 < St := by
    simpa [St] using lambdaSqInfinity_denominator_pos Q a ht
  have hspos : 0 < s := lt_trans ht hts
  have hSspos : 0 < Ss := by
    simpa [Ss] using lambdaSqInfinity_denominator_pos Q a hspos
  have hconverted : St⁻¹ ≤ Ss⁻¹ :=
    (inv_le_inv₀ hStpos hSspos).2 hden
  simpa [St, Ss, lambdaSq, lambdaSqInfinity] using hconverted

theorem oneCube_sigmaStarInv_le_lambdaSq_infinity_inv {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    (hs : 0 < s) :
    coarseSigmaStarInvMatrixNorm Q a ≤ (lambdaSq Q s .infinity a)⁻¹ := by
  have hbdd := lambdaSqInfinity_denominator_valueSet_bddAbove Q a hs.le
  have hmem :
      coarseSigmaStarInvMatrixNorm Q a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := by
    refine ⟨0, ?_⟩
    simp [maxDescendantSigmaStarInvMatrixNormAtScale_self]
  have hle :
      coarseSigmaStarInvMatrixNorm Q a ≤
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } :=
    le_csSup hbdd hmem
  simpa [lambdaSq, lambdaSqInfinity] using hle


end

end Ch02
end Book
end Homogenization
