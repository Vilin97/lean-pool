/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace BGS.FiniteField

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sum a function over the square map, with fiber sizes expressed by the quadratic character. -/
theorem sum_comp_sq_eq_sum_quadraticChar_add_one
    (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ y : F, f (y ^ 2) = ∑ x : F, (quadraticChar F x + 1) * f x := by
  classical
  rw [← sum_fiberwise (s := univ) (g := fun y : F => y ^ 2) (f := fun y => f (y ^ 2))]
  apply sum_congr rfl
  intro x _
  have hcard :
      ((#{y ∈ (univ : Finset F) | y ^ 2 = x} : ℕ) : ℤ) = quadraticChar F x + 1 := by
    simpa [Set.toFinset_ofPred] using quadraticChar_card_sqrts hF x
  calc
    ∑ y ∈ (univ : Finset F) with y ^ 2 = x, f (y ^ 2) =
        ∑ _y ∈ (univ : Finset F) with _y ^ 2 = x, f x := by
      apply sum_congr rfl
      intro y hy
      rw [(mem_filter.mp hy).2]
    _ = ((#{y ∈ (univ : Finset F) | y ^ 2 = x} : ℕ) : ℤ) * f x := by
      simp
    _ = (quadraticChar F x + 1) * f x := by rw [hcard]

/-- The quadratic-character sum of `1 - d * y²` is a Jacobi sum. -/
theorem sum_quadraticChar_one_sub_mul_sq
    (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ y : F, quadraticChar F (1 - d * y ^ 2) =
      -quadraticChar F d * quadraticChar F (-1) := by
  let chi := quadraticChar F
  have hzero : ∑ x : F, chi (1 - d * x) = 0 := by
    let e : F ≃ F := (Equiv.mulLeft₀ d hd).trans (Equiv.subLeft 1)
    calc
      ∑ x : F, chi (1 - d * x) = ∑ x : F, chi (e x) := by
        apply sum_congr rfl
        intro x _
        simp [e]
      _ = ∑ x : F, chi x := e.sum_comp chi
      _ = 0 := quadraticChar_sum_zero hF
  have hJacobi : jacobiSum chi chi = -chi (-1) := by
    have hinv : chi⁻¹ = chi := by
      dsimp [chi]
      exact (quadraticChar_isQuadratic F).inv
    calc
      jacobiSum chi chi = jacobiSum chi chi⁻¹ := by rw [hinv]
      _ = -chi (-1) := by
        dsimp [chi]
        exact jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  have hscaled :
      chi d * (∑ x : F, chi x * chi (1 - d * x)) = jacobiSum chi chi := by
    rw [mul_sum]
    let e : F ≃ F := Equiv.mulLeft₀ d hd
    calc
      ∑ x : F, chi d * (chi x * chi (1 - d * x)) =
          ∑ x : F, chi (e x) * chi (1 - e x) := by
        apply sum_congr rfl
        intro x _
        simp [e, mul_assoc]
      _ = ∑ x : F, chi x * chi (1 - x) :=
        e.sum_comp (fun x => chi x * chi (1 - x))
      _ = jacobiSum chi chi := rfl
  have hchi_sq : chi d ^ 2 = 1 := quadraticChar_sq_one hd
  calc
    ∑ y : F, chi (1 - d * y ^ 2) =
        ∑ x : F, (chi x + 1) * chi (1 - d * x) := by
      simpa [chi] using
        sum_comp_sq_eq_sum_quadraticChar_add_one hF (fun x => chi (1 - d * x))
    _ = (∑ x : F, chi x * chi (1 - d * x)) + ∑ x : F, chi (1 - d * x) := by
      simp_rw [add_mul, one_mul, sum_add_distrib]
    _ = ∑ x : F, chi x * chi (1 - d * x) := by rw [hzero, add_zero]
    _ =
        chi d ^ 2 * ∑ x : F, chi x * chi (1 - d * x) := by rw [hchi_sq, one_mul]
    _ = chi d * (chi d * ∑ x : F, chi x * chi (1 - d * x)) := by ring
    _ = chi d * jacobiSum chi chi := by rw [hscaled]
    _ = -chi d * chi (-1) := by rw [hJacobi]; ring

/-- A nondegenerate quadratic polynomial has quadratic-character sum `-chi(A)`. -/
theorem sum_quadraticChar_mul_sq_sub
    (hF : ringChar F ≠ 2) {A C : F} (hA : A ≠ 0) (hC : C ≠ 0) :
    ∑ y : F, quadraticChar F (A * y ^ 2 - C) = -quadraticChar F A := by
  let chi := quadraticChar F
  have hd : A / C ≠ 0 := div_ne_zero hA hC
  have hinv : chi⁻¹ = chi := by
    dsimp [chi]
    exact (quadraticChar_isQuadratic F).inv
  have hchiCinv : chi C⁻¹ = chi C := by
    rw [← MulChar.inv_apply' chi C, hinv]
  have hchiC_sq : chi C ^ 2 = 1 := quadraticChar_sq_one hC
  have hchiNegOne_sq : chi (-1) ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  calc
    ∑ y : F, chi (A * y ^ 2 - C) =
        ∑ y : F, chi ((-C) * (1 - (A / C) * y ^ 2)) := by
      apply sum_congr rfl
      intro y _
      congr 1
      field_simp [hC]
      ring
    _ = ∑ y : F, chi (-C) * chi (1 - (A / C) * y ^ 2) := by
      simp only [map_mul]
    _ = chi (-C) * ∑ y : F, chi (1 - (A / C) * y ^ 2) := by rw [mul_sum]
    _ = chi (-C) * (-chi (A / C) * chi (-1)) := by
      rw [sum_quadraticChar_one_sub_mul_sq hF hd]
    _ = -chi A := by
      rw [show -C = (-1) * C by ring, map_mul, div_eq_mul_inv, map_mul, hchiCinv]
      calc
        chi (-1) * chi C * (-(chi A * chi C) * chi (-1)) =
            -(chi A) * (chi C ^ 2) * (chi (-1) ^ 2) := by ring
        _ = -chi A := by rw [hchiC_sq, hchiNegOne_sq, mul_one, mul_one]

/-- A nondegenerate affine conic has a point outside any set of at most three forbidden first
coordinates once the field has at least eight elements. -/
theorem exists_quadratic_conic_point_away_from_three
    (hF : ringChar F ≠ 2) (hcard : 8 ≤ Fintype.card F)
    {A C : F} (hA : A ≠ 0) (hC : C ≠ 0) (bad : Finset F) (hbad : #bad ≤ 3) :
    ∃ y, y ∉ bad ∧ ∃ lambda, lambda ^ 2 = A * y ^ 2 - C := by
  classical
  let roots (y : F) : Finset F := univ.filter fun lambda => lambda ^ 2 = A * y ^ 2 - C
  let rootCount (y : F) : ℤ := #(roots y)
  have hrootCount (y : F) :
      rootCount y = quadraticChar F (A * y ^ 2 - C) + 1 := by
    dsimp [rootCount, roots]
    simpa [Set.toFinset_ofPred] using
      quadraticChar_card_sqrts hF (A * y ^ 2 - C)
  have hsum :
      ∑ y : F, rootCount y = (Fintype.card F : ℤ) - quadraticChar F A := by
    calc
      ∑ y : F, rootCount y =
          ∑ y : F, (quadraticChar F (A * y ^ 2 - C) + 1) := by
        apply sum_congr rfl
        intro y _
        exact hrootCount y
      _ = (∑ y : F, quadraticChar F (A * y ^ 2 - C)) + ∑ _y : F, 1 := by
        simp_rw [sum_add_distrib]
      _ = -quadraticChar F A + (Fintype.card F : ℤ) := by
        rw [sum_quadraticChar_mul_sq_sub hF hA hC]
        simp
      _ = (Fintype.card F : ℤ) - quadraticChar F A := by ring
  have hrootCount_le (y : F) : rootCount y ≤ 2 := by
    rw [hrootCount]
    by_cases hzero : A * y ^ 2 - C = 0
    · rw [hzero, quadraticChar_zero]
      norm_num
    · rcases quadraticChar_dichotomy hzero with h | h <;> rw [h] <;> norm_num
  by_contra hExists
  have hzeroOutside (y : F) (hy : y ∉ bad) : rootCount y = 0 := by
    have hnone : ∀ lambda : F, lambda ^ 2 ≠ A * y ^ 2 - C := by
      intro lambda hlambda
      exact hExists ⟨y, hy, lambda, hlambda⟩
    have hempty : roots y = ∅ := by
      ext lambda
      simp [roots, hnone lambda]
    simp [rootCount, hempty]
  have hrestrict : ∑ y ∈ bad, rootCount y = ∑ y : F, rootCount y := by
    apply sum_subset (subset_univ bad)
    intro y _ hy
    exact hzeroOutside y hy
  have hupper : ∑ y : F, rootCount y ≤ 6 := by
    rw [← hrestrict]
    calc
      ∑ y ∈ bad, rootCount y ≤ ∑ _y ∈ bad, (2 : ℤ) := by
        exact sum_le_sum fun y _ => hrootCount_le y
      _ = (#bad : ℤ) * 2 := by simp
      _ ≤ 6 := by exact_mod_cast Nat.mul_le_mul_right 2 hbad
  have hchi_le : quadraticChar F A ≤ 1 := by
    rcases quadraticChar_dichotomy hA with h | h
    · omega
    · omega
  have hlower : 7 ≤ ∑ y : F, rootCount y := by
    rw [hsum]
    omega
  omega

end BGS.FiniteField
