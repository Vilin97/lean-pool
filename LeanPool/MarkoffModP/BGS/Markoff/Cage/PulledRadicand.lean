/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Cage.ShiftedTraceCurveIrreducibility
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Pulled-back cage radicands

After writing the common normalized trace as `t^d + t⁻ᵈ` and multiplying
an incidence root by `t^d`, the retained quadratic equation becomes

`L² = (ξ² - 4) (t^(2d) + 1)² - 4 ξ² t^(2d)`.

This file proves the square-class facts needed for the direct affine-plane
Hasse--Weil model.  In particular, the off-diagonal argument is not hidden
behind a geometric-integrality assumption: the two pulled radicands are
proved squarefree and coprime explicitly.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The radicand obtained after pulling an incidence conic back along the
power-trace parameter `t ↦ t^d + t⁻ᵈ` and clearing `t⁻ᵈ`. -/
def cagePulledRadicand (xi : K) (d : ℕ) : K[X] :=
  C (xi ^ 2 - 4) * (X ^ (2 * d) + 1) ^ 2 -
    C (4 * xi ^ 2) * X ^ (2 * d)

@[simp]
lemma cagePulledRadicand_eval_zero (xi : K) {d : ℕ} (hd : 0 < d) :
    (cagePulledRadicand xi d).eval 0 = xi ^ 2 - 4 := by
  simp [cagePulledRadicand, Nat.ne_of_gt hd]

@[simp]
lemma cagePulledRadicand_eval_one (xi : K) (d : ℕ) :
    (cagePulledRadicand xi d).eval 1 = -16 := by
  simp [cagePulledRadicand]
  ring

/-- Distinct squared cage traces give radicands whose difference is a
nonzero scalar times `(t^(2d) - 1)²`. -/
lemma cagePulledRadicand_sub (xi eta : K) (d : ℕ) :
    cagePulledRadicand xi d - cagePulledRadicand eta d =
      C (xi ^ 2 - eta ^ 2) * (X ^ (2 * d) - 1) ^ 2 := by
  simp only [cagePulledRadicand, map_sub, map_pow, map_ofNat, map_mul]
  ring

/-- Formal derivative of the pulled radicand. -/
lemma cagePulledRadicand_derivative (xi : K) (d : ℕ) :
    (cagePulledRadicand xi d).derivative =
      C (((2 * d : ℕ) : K)) * X ^ (2 * d - 1) *
        (2 * C (xi ^ 2 - 4) * (X ^ (2 * d) + 1) -
          C (4 * xi ^ 2)) := by
  simp only [cagePulledRadicand,
    derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_add, derivative_one, add_zero, derivative_pow, derivative_X,
    mul_one]
  simp only [map_sub, map_pow, map_natCast, map_mul]
  ring

/-- The pulled radicand has no repeated geometric root under the exact
nondegeneracy assumptions used in the cage. -/
lemma cagePulledRadicand_separable
    (h2 : (2 : K) ≠ 0) {xi : K} (hxi : xi ≠ 0)
    (hparabolic : xi ^ 2 - 4 ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    (cagePulledRadicand xi d).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K) (cagePulledRadicand xi d)
      (cagePulledRadicand xi d).derivative).2
  intro t
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hroot, hderivative⟩
  have hphiTwo : phi 2 ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr h2
  have hphiXi : phi xi ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hxi
  have hphiA : phi (xi ^ 2 - 4) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hparabolic
  have hphiDegree : phi (((2 * d : ℕ) : K)) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr hdegree
  have ht : t ≠ 0 := by
    intro ht
    subst t
    apply hphiA
    simpa [cagePulledRadicand, phi, Nat.ne_of_gt hd] using hroot
  have hcritical :
      2 * phi (xi ^ 2 - 4) * (t ^ (2 * d) + 1) -
        phi (4 * xi ^ 2) = 0 := by
    rw [cagePulledRadicand_derivative] at hderivative
    have hderivative' :
        phi (((2 * d : ℕ) : K)) * t ^ (2 * d - 1) *
          (2 * phi (xi ^ 2 - 4) * (t ^ (2 * d) + 1) -
            phi (4 * xi ^ 2)) = 0 := by
      simpa only [aeval_def, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
        eval₂_sub, eval₂_add, eval₂_one, eval₂_ofNat] using hderivative
    exact (mul_eq_zero.mp hderivative').resolve_left
      (mul_ne_zero hphiDegree (pow_ne_zero _ ht))
  have hroot' :
      phi (xi ^ 2 - 4) * (t ^ (2 * d) + 1) ^ 2 -
        phi (4 * xi ^ 2) * t ^ (2 * d) = 0 := by
    simpa only [cagePulledRadicand, aeval_def, eval₂_mul, eval₂_C,
      eval₂_pow, eval₂_X, eval₂_sub, eval₂_add, eval₂_one] using hroot
  have hone : t ^ (2 * d) = 1 := by
    have hnonzero : phi (4 * xi ^ 2) ≠ 0 := by
      apply (map_ne_zero_iff phi phi.injective).mpr
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 ^ 2 by norm_num]
        exact pow_ne_zero 2 h2
      exact mul_ne_zero h4 (pow_ne_zero 2 hxi)
    have hproduct :
        phi (4 * xi ^ 2) * (1 - t ^ (2 * d)) = 0 := by
      linear_combination 2 * hroot' - (t ^ (2 * d) + 1) * hcritical
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hnonzero)).symm
  have : phi (16 : K) = 0 := by
    apply neg_eq_zero.mp
    calc
      -phi (16 : K) =
          2 * phi (xi ^ 2 - 4) * (1 + 1) - phi (4 * xi ^ 2) := by
            simp only [map_sub, map_pow, map_ofNat, map_mul]
            ring
      _ = 0 := by simpa [hone] using hcritical
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  exact (map_ne_zero_iff phi phi.injective).mpr h16 this

/-- Expanded form, used to read off the leading coefficient and degree. -/
lemma cagePulledRadicand_expanded (xi : K) (d : ℕ) :
    cagePulledRadicand xi d =
      C (xi ^ 2 - 4) * X ^ (4 * d) -
        C (2 * (xi ^ 2 + 4)) * X ^ (2 * d) + C (xi ^ 2 - 4) := by
  have hC2 : (C (2 : K) : K[X]) = 2 :=
    map_natCast (Polynomial.C : K →+* K[X]) 2
  have hC4 : (C (4 : K) : K[X]) = 4 :=
    map_natCast (Polynomial.C : K →+* K[X]) 4
  simp only [cagePulledRadicand, map_sub, map_pow, map_mul, map_add]
  rw [hC2, hC4]
  ring_nf

/-- The coefficient of `t^(4d)` is the nonparabolic factor `xi² - 4`. -/
lemma cagePulledRadicand_coeff_four_mul
    (xi : K) {d : ℕ} (hd : 0 < d) :
    (cagePulledRadicand xi d).coeff (4 * d) = xi ^ 2 - 4 := by
  rw [cagePulledRadicand_expanded]
  rw [coeff_add, coeff_sub, coeff_C_mul_X_pow,
    coeff_C_mul_X_pow, coeff_C]
  simp only [ite_true, ite_eq_right (show 4 * d ≠ 2 * d by omega),
    ite_eq_right (show 4 * d ≠ 0 by omega), sub_zero, add_zero]

/-- A nonparabolic pulled radicand is not a polynomial unit. -/
lemma cagePulledRadicand_not_isUnit
    {xi : K} (hparabolic : xi ^ 2 - 4 ≠ 0) {d : ℕ} (hd : 0 < d) :
    ¬ IsUnit (cagePulledRadicand xi d) := by
  apply not_isUnit_of_natDegree_pos
  have hcoeff : (cagePulledRadicand xi d).coeff (4 * d) ≠ 0 := by
    simpa [cagePulledRadicand_coeff_four_mul xi hd] using hparabolic
  have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

/-- Off the diagonal, the two pulled radicands have disjoint geometric
zero sets.  The displayed difference reduces a hypothetical common zero to
`t^(2d)=1`, where every radicand takes the value `-16`. -/
lemma cagePulledRadicand_isCoprime
    (h2 : (2 : K) ≠ 0) {xi eta : K} (hoffDiagonal : xi ^ 2 ≠ eta ^ 2)
    (d : ℕ) :
    IsCoprime (cagePulledRadicand xi d) (cagePulledRadicand eta d) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := K) (AlgebraicClosure K) (cagePulledRadicand xi d)
      (cagePulledRadicand eta d)).2
  intro t
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  by_contra hcommon
  push Not at hcommon
  rcases hcommon with ⟨hxiRoot, hetaRoot⟩
  have hdifference := congrArg (fun f : K[X] => aeval t f)
    (cagePulledRadicand_sub xi eta d)
  have hproduct :
      phi (xi ^ 2 - eta ^ 2) * (t ^ (2 * d) - 1) ^ 2 = 0 := by
    simpa only [map_sub, aeval_def, eval₂_sub, eval₂_mul, eval₂_C,
      eval₂_pow, eval₂_X, eval₂_one, hxiRoot, hetaRoot, zero_sub, neg_zero]
      using hdifference.symm
  have hscalar : phi (xi ^ 2 - eta ^ 2) ≠ 0 :=
    (map_ne_zero_iff phi phi.injective).mpr (sub_ne_zero.mpr hoffDiagonal)
  have hpower : t ^ (2 * d) = 1 := by
    have hsquare : (t ^ (2 * d) - 1) ^ 2 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hscalar
    have hbase : t ^ (2 * d) - 1 = 0 := by
      apply (mul_self_eq_zero.mp)
      simpa [pow_two] using hsquare
    exact sub_eq_zero.mp hbase
  have hminusSixteen : phi (-16 : K) = 0 := by
    calc
      phi (-16 : K) =
          phi (xi ^ 2 - 4) * (t ^ (2 * d) + 1) ^ 2 -
            phi (4 * xi ^ 2) * t ^ (2 * d) := by
              have hfour : ((1 : AlgebraicClosure K) + 1) ^ 2 = phi (4 : K) := by
                calc
                  ((1 : AlgebraicClosure K) + 1) ^ 2 = 4 := by norm_num
                  _ = phi (4 : K) := (map_natCast phi 4).symm
              rw [hpower, hfour, mul_one]
              rw [← map_mul, ← map_sub]
              congr 1
              ring
      _ = aeval t (cagePulledRadicand xi d) := by
        simp only [phi, cagePulledRadicand, aeval_def, eval₂_sub, eval₂_mul,
          eval₂_C, eval₂_pow, eval₂_X, eval₂_add, eval₂_one]
      _ = 0 := hxiRoot
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  exact (map_ne_zero_iff phi phi.injective).mpr (neg_ne_zero.mpr h16) hminusSixteen

/-- The two off-diagonal radicands and their product are squarefree. -/
lemma cagePulledRadicand_squarefree_and_product
    (h2 : (2 : K) ≠ 0) {xi eta : K}
    (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) {d : ℕ} (hd : 0 < d)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Squarefree (cagePulledRadicand xi d) ∧
      Squarefree (cagePulledRadicand eta d) ∧
      Squarefree (cagePulledRadicand xi d * cagePulledRadicand eta d) := by
  have hsepXi := cagePulledRadicand_separable h2 hxi hXi hd hdegree
  have hsepEta := cagePulledRadicand_separable h2 heta hEta hd hdegree
  have hcoprime := cagePulledRadicand_isCoprime h2 hoffDiagonal d
  exact ⟨hsepXi.squarefree, hsepEta.squarefree,
    (hsepXi.mul hsepEta hcoprime).squarefree⟩

/-- The pulled radicands define two independent quadratic square classes in
the rational function field.  This is the algebraic content of the paper's
disjoint-branch argument. -/
lemma cagePulledRadicand_squareClasses_independent_ratFunc
    (h2 : (2 : K) ≠ 0) {xi eta : K}
    (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) {d : ℕ} (hd : 0 < d)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) (cagePulledRadicand xi d)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K) (cagePulledRadicand eta d)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K)
        (cagePulledRadicand xi d * cagePulledRadicand eta d)) := by
  obtain ⟨hsqXi, hsqEta, hsqProduct⟩ :=
    cagePulledRadicand_squarefree_and_product h2 hxi heta hXi hEta
      hoffDiagonal hd hdegree
  exact ⟨not_isSquare_algebraMap_of_squarefree_not_isUnit hsqXi
      (cagePulledRadicand_not_isUnit hXi hd),
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqEta
      (cagePulledRadicand_not_isUnit hEta hd),
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqProduct (by
      intro hunit
      exact cagePulledRadicand_not_isUnit hXi hd (IsUnit.mul_iff.mp hunit).1)⟩

end

end BGS.Markoff
