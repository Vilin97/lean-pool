/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeiBichang
-/

/-
Current goals :
1. prove `eval₂_mul`
2. prove `PowerSeries.ringHom_ext_Z`

The explicit parameter `R` with `CommRing R` in
PowerSeries might causes some incompatibility of
notations in this file. Will be fix later.

How to `rw` a term in a finsum?
-/


import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Nilpotent

import LeanPool.Neukirch.ValuationTheory.trivia

open PadicInt Classical

section

variable {R : Type _} [CommRing R]
variable {S : Type _} [CommRing S] [Nontrivial S]
variable (f : R →+* S)
variable (s : nilradical S)

namespace PowerSeries

noncomputable section trunc
-- `trunc n` truncates the deg `n` term

-- theorem trunc_X (n : ℕ) : trunc (n + 2) (X : PowerSeries R) = Polynomial.X := by
--   rw [← Polynomial.coeff_inj]
--   ext k
--   rw [coeff_trunc _ _ _]
--   sorry

def truncAddMonoidHom (n : ℕ): PowerSeries R →+ Polynomial R where
  toFun := trunc n
  map_zero' := trunc_zero _
  map_add' := trunc_add _

-- #check Polynomial.coeff_monomial
theorem trunc_sub {φ : PowerSeries R} {m n : ℕ} (h : m ≤ n) : φ.trunc n - φ.trunc m = (Finset.Ico m n).sum fun k ↦ Polynomial.monomial k (coeff R k φ) := by
  apply Polynomial.coeff_inj.mp
  ext k
  rw [Polynomial.coeff_sub, Polynomial.finset_sum_coeff]
  rw [coeff_trunc, coeff_trunc]
  simp [Polynomial.coeff_monomial]
  by_cases hkm : k < m
  · simp only [lt_of_lt_of_le hkm h, ite_true, hkm, sub_self, and_true, if_neg (not_le.mpr hkm)]
  by_cases hkn : k < n
  · simp only [hkn, ite_true, hkm, ite_false, sub_zero, and_true, if_pos (not_lt.mp hkm)]
  · simp only [hkn, ite_false, hkm, sub_self, and_false]

-- #check sub_eq_iff_eq_add
-- #check sub_eq_iff_eq_add'
theorem trunc_sub' {φ : PowerSeries R} {m n : ℕ} (h : m ≤ n) : φ.trunc n = φ.trunc m + (Finset.Ico m n).sum fun k ↦ Polynomial.monomial k (coeff R k φ) :=
  sub_eq_iff_eq_add'.mp (trunc_sub h)

theorem trunc_monomial {m n : ℕ} (a : R): (monomial R m a).trunc n = if m < n then Polynomial.monomial m a else 0 := by
  ext k
  rw [coeff_trunc, coeff_monomial]
  split_ifs with h1 h2 h3
  · rw [Polynomial.coeff_monomial, if_pos h2.symm]
  · exfalso; linarith
  · rw [Polynomial.coeff_monomial, if_neg]
    exact fun a ↦ h2 a.symm
  · exact (Polynomial.coeff_zero _).symm
  · rw [Polynomial.coeff_monomial, if_neg]; linarith
  · exact (Polynomial.coeff_zero _).symm

end trunc

section monomial

theorem X_pow_eq_monomial (n : ℕ) : (X : R⟦X⟧) ^ n = monomial R n 1 := by
  ext; simp only [coeff_X_pow, coeff_monomial]

end monomial

noncomputable section eval₂

def sum (n : ℕ) (φ : PowerSeries R) (F : ℕ → R → S) : S := (φ.trunc n).sum F

def eval₂ (f : R →+* S) (s : nilradical S) (φ : PowerSeries R) : S := (φ.trunc (choose s.2)).eval₂ f s.1

theorem eval₂_eq_sum {f : R →+* S} {s : nilradical S} {φ : PowerSeries R}:
  φ.eval₂ f s = φ.sum (choose s.2) fun e a ↦ f a * s.1 ^ e := by
  simp only [eval₂, sum, Polynomial.eval₂_eq_sum]

theorem eval₂_eq_sum_higher {f : R →+* S} {s : nilradical S} {φ : PowerSeries R} {n : ℕ} (hn : n ≥ (choose s.2)) :
  φ.eval₂ f s = φ.sum n fun e a ↦ f a * s.1 ^ e := by
  sorry

theorem eval₂_eq_Polynomial_eval₂ {f : R →+* S} {s : nilradical S} {φ : PowerSeries R} {n : ℕ} (hn : n ≥ (choose s.2)) :
  φ.eval₂ f s = (φ.trunc n).eval₂ f s.1 := by
  rw [eval₂]
  sorry

theorem eval₂_congr {f g : R →+* S} {s t : nilradical S} {φ ψ : PowerSeries R} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl

-- #check choose
-- #check Polynomial.eval₂_at_zero
theorem eval₂_at_zero {φ : PowerSeries R} : φ.eval₂ f ⟨0, IsNilpotent.zero⟩ = f (coeff R 0 φ) := by
  simp only [eval₂, Submodule.zero_eq_bot, Ideal.mem_bot, Polynomial.eval₂_at_zero, coeff_trunc]
  congr 1
  simp only [coeff_zero_eq_constantCoeff, ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  contrapose!; intro
  apply choose_IsNilpotent_ne_zero IsNilpotent.zero

theorem eval₂_zero : (0 : PowerSeries R).eval₂ f s = 0 := by
  simp only [eval₂, Submodule.zero_eq_bot, Ideal.mem_bot, trunc_zero, Polynomial.eval₂_zero]

-- #check Polynomial.eval₂_monomial
theorem eval₂_monomial {n : ℕ} {a : R} : (monomial R n a).eval₂ f s = f a * s.1 ^ n := by
  rw [eval₂_eq_sum, sum, trunc_monomial]
  split
  · simp only [map_zero, zero_mul, Polynomial.sum_monomial_index]
  · rw [Polynomial.sum_zero_index]
    refine (mul_eq_zero_of_right (f a) ?_).symm
    apply nilp_pow_ge_choose_eq_zero
    linarith

-- #check Polynomial.eval₂_C
theorem eval₂_C {a : R} : (C R a).eval₂ f s = f a := by
  rw [← monomial_zero_eq_C_apply, eval₂_monomial]
  simp only [pow_zero, mul_one]

-- #check Polynomial.eval₂_X
theorem eval₂_X : X.eval₂ f s = s := by
  rw [X_eq, eval₂_monomial]
  simp only [map_one, pow_one, one_mul]

-- #check Polynomial.eval₂_X_pow
theorem eval₂_X_pow {n : ℕ} : (X ^ n : PowerSeries R).eval₂ f s = s.1 ^ n := by
  simp only [X_pow_eq_monomial, eval₂_monomial, map_one, one_mul]

-- #check Polynomial.eval₂_add
theorem eval₂_add {φ ψ : PowerSeries R} : (φ + ψ).eval₂ f s = φ.eval₂ f s + ψ.eval₂ f s := by
  rw [eval₂, eval₂, eval₂,
      ← Polynomial.eval₂_add, trunc_add]

@[simp]
def eval₂AddMonoidHom : PowerSeries R →+ S where
  toFun := eval₂ f s
  map_zero' := eval₂_zero _ _
  map_add' := fun _ _ ↦ eval₂_add _ _

-- #check PowerSeries.C R (1 : R)
-- #check Polynomial.C (1 : R)
theorem eval₂_one : (1 : PowerSeries R).eval₂ f s = 1 := by
  rw [show (1 : PowerSeries R) = C R (1 : R) by rfl, eval₂_C, f.map_one]

#check Polynomial.eval₂_mul
theorem eval₂_mul {φ ψ : PowerSeries R} : (φ * ψ).eval₂ f s = φ.eval₂ f s * ψ.eval₂ f s := by
  rw [eval₂, eval₂, eval₂, ← Polynomial.eval₂_mul]
  simp [Polynomial.eval₂_eq_sum]
  sorry

-- For a nilpotent element `s : S`, assignment `X ↦ s` defines a ring homomorphism `PowerSeries R → S`
@[simp]
def eval₂RingHom : PowerSeries R →+* S := {
  eval₂AddMonoidHom f s with
  map_one' := eval₂_one _ _
  map_mul' := fun _ _ ↦ eval₂_mul _ _
}

end eval₂

section ringhom

theorem ringHom_ext {f g : R⟦X⟧ →+* S} (h₁ : ∀ a, f (C R a) = g (C R a))
    (h₂ : f X = g X) (h₃ : IsNilpotent (f X)) : f = g := by
  sorry

theorem ringHom_ext' {f g : R⟦X⟧ →+* S} (h₁ : f.comp (C R) = g.comp (C R))
    (h₂ : f X = g X) (h₃ : IsNilpotent (f X)): f = g := by
  sorry

-- A ring homomorphism `ℤ⟦X⟧ → R` is determined by its value on `X`.
theorem ringHom_ext_Z {R : Type} [CommRing R] {f g : ℤ⟦X⟧ →+* R} (h₁ : f X = g X) (h₂ : IsNilpotent (f X)) : f = g :=
  ringHom_ext' (RingHom.ext_int (RingHom.comp f (C ℤ)) (RingHom.comp g (C ℤ))) h₁ h₂

end ringhom

end PowerSeries

end
