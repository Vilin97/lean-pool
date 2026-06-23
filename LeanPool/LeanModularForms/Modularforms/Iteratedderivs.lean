/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Cases

/-! # Iteratedderivs -/


@[expose] public section

open  UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


theorem upper_ne_int (x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0 := by
  intro h
  have h1 : 0 < (x : ℂ).im := by simpa using im_pos x
  simp [add_eq_zero_iff_eq_neg.mp h] at h1


theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  induction k generalizing x with
  | zero =>
    simp only [iteratedDerivWithin_zero, pow_zero, Nat.factorial_zero, one_mul]
    simp at *
  | succ k IH =>
    rw [iteratedDerivWithin_succ]
    simp only [one_div, Nat.cast_succ, Nat.factorial, Nat.cast_mul]
    have := (IH hx)
    have H : derivWithin (fun (z : ℂ) => (-1: ℂ) ^ k * ↑k ! * ((z + ↑d) ^ (k + 1))⁻¹)
               {z : ℂ | 0 < z.im} x =
             (-1) ^ (↑k + 1) * ((↑k + 1) * ↑k !) * ((x + ↑d) ^ (↑k + 1 + 1))⁻¹ := by
      rw [DifferentiableAt.derivWithin]
      · simp only [deriv_const_mul_field']
        rw [show (fun z : ℂ => ((z + d) ^ (k + 1))⁻¹) = (fun z : ℂ => (z + d) ^ (k + 1))⁻¹ from rfl,
          show (fun z : ℂ => ((z + d) ^ (k + 1))) = (fun z : ℂ => (z + d)) ^ (k + 1) from rfl,
          deriv_inv'', deriv_pow, deriv_add_const', deriv_id'']
        · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, mul_one]
          rw [pow_add]
          simp only [pow_one, Pi.mul_apply, Pi.pow_apply]
          have Hw : (-(((k : ℂ) + 1) * (x + ↑d) ^ k) / ((x + ↑d) ^ k * (x + ↑d)) ^ 2) =
                    -(↑k + 1) / (x + ↑d) ^ (k + 2) := by
            rw [div_eq_div_iff]
            · norm_cast
              simp
              ring
            · norm_cast
              apply pow_ne_zero
              apply mul_ne_zero
              · apply pow_ne_zero k (upper_ne_int ⟨x, hx⟩ d)
              apply upper_ne_int ⟨x, hx⟩ d
            norm_cast
            apply pow_ne_zero (k + 2) (upper_ne_int ⟨x, hx⟩ d)
          rw [Hw]
          ring
        · fun_prop
        · fun_prop
        norm_cast
        apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
      · apply DifferentiableAt.mul
        · fun_prop
        · apply DifferentiableAt.inv
          · fun_prop
          apply pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
      · apply IsOpen.uniqueDiffWithinAt _ hx
        refine isOpen_lt ?_ ?_
        · fun_prop
        · fun_prop
    rw [←H]
    apply derivWithin_congr
    · norm_cast at *
      simp only [mem_setOf_eq, one_div, Int.reduceNegSucc, Int.reduceNeg, Int.cast_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, Int.cast_add] at *
      intro r hr
      apply IH hr
    norm_cast at *
    simp only [mem_setOf_eq, one_div, Int.reduceNegSucc, Int.reduceNeg, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Int.cast_add] at *
    apply this

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx; simp_rw [sub_eq_add_neg]; simpa using aut_iter_deriv (-d : ℤ) k hx

theorem aut_contDiffOn (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d))
    {z : ℂ | 0 < z.im} := by
  simp only [one_div]
  apply ContDiffOn.inv
  · apply ContDiffOn.sub
    · apply contDiffOn_id
    apply contDiffOn_const
  intro x hx; simpa [sub_eq_add_neg] using upper_ne_int ⟨x, hx⟩ (-d)


theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) {z : ℂ | 0 < z.im})
      ((fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  have h1 :
    (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) =
      (fun z : ℂ => 1 / (z - d)) + fun z : ℂ => 1 / (z + d) := by rfl
  rw [h1]
  simp only [one_div, Pi.add_apply] at *
  rw [iteratedDerivWithin_add hx ?_]
  · have h2 := aut_iter_deriv d k hx
    have h3 := aut_iter_deriv' d k hx
    simp only [mem_setOf_eq, one_div] at *
    rw [h2, h3]
  · have h4 := aut_contDiffOn d k
    simp only [one_div] at h4
    apply h4
    exact hx
  · have h5 := aut_contDiffOn (-d) k
    simp only [Int.cast_neg, sub_neg_eq_add, one_div] at h5
    apply h5
    exact hx
  · exact IsOpen.uniqueDiffOn (isOpen_lt (by fun_prop) (by fun_prop))

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜)




theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * m * s))
           {z : ℂ | 0 < z.im})
      (fun t => (2 * ↑π * Complex.I * m) ^ n * Complex.exp (2 * ↑π * Complex.I * m * t))
      {z : ℂ | 0 < z.im} := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen (isOpen_lt (by fun_prop) (by fun_prop)))
  exact fun x _ => congr_fun (iteratedDeriv_cexp_const_mul ..) x
