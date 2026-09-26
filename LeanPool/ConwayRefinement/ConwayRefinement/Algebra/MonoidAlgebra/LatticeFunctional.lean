/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Finsupp.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A linear functional separating finitely many lattice points

Finitely many points of a finite-rank lattice are separated by a single homomorphism to the
integers: evaluating coordinates in a base larger than twice every coordinate that occurs makes
the resulting integer determine the point, because a base-`N` representation with digits of
absolute value below `N` represents zero only if all its digits vanish.

Such a functional collapses a finite-rank exponent lattice to a single variable while keeping
prescribed exponents distinct, which is what reduces a statement about group algebras of
finite-rank lattices to the one-variable case.
-/

universe u

public section

/-- Base-`N` digits with absolute value below `N` represent zero only if they all vanish. -/
private theorem eq_zero_of_sum_mul_pow_eq_zero {k : ℕ} {N : ℤ} (hN : 0 < N) {d : Fin k → ℤ}
    (hd : ∀ i, |d i| < N) (hsum : ∑ i, d i * N ^ (i : ℕ) = 0) : ∀ i, d i = 0 := by
  induction k with
  | zero => exact fun i ↦ i.elim0
  | succ k ih =>
    rw [Fin.sum_univ_succ] at hsum
    have hshift : ∑ i : Fin k, d i.succ * N ^ ((i : ℕ) + 1) =
        N * ∑ i : Fin k, d i.succ * N ^ (i : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pow_succ]
      ring
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ] at hsum
    rw [hshift] at hsum
    have hd0 : d 0 = 0 := by
      have hdvd : N ∣ d 0 := ⟨-(∑ i : Fin k, d i.succ * N ^ (i : ℕ)), by linarith [hsum]⟩
      rcases hdvd with ⟨t, ht⟩
      by_contra hne
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [mul_zero] at ht
        exact hne ht
      have h1 : 1 ≤ |t| := Int.one_le_abs ht0
      have : N ≤ |d 0| := by
        rw [ht, abs_mul, abs_of_pos hN]
        exact le_mul_of_one_le_right hN.le h1
      exact absurd (hd 0) (not_lt.mpr this)
    have hrest : ∑ i : Fin k, d i.succ * N ^ (i : ℕ) = 0 := by
      rw [hd0, zero_add] at hsum
      exact (mul_eq_zero.mp hsum).resolve_left hN.ne'
    intro i
    refine Fin.cases hd0 (fun j ↦ ?_) i
    exact ih (fun j ↦ hd j.succ) hrest j
/-- A group homomorphism to `ℤ` that is injective on a prescribed finite set of lattice points:
evaluate in a base larger than twice every coordinate occurring. -/
theorem AddMonoidHom.exists_injOn_finInt {k : ℕ} (S : Finset (Fin k → ℤ)) :
    ∃ psi : (Fin k → ℤ) →+ ℤ, Set.InjOn psi (S : Set (Fin k → ℤ)) := by
  classical
  set M : ℕ := S.sup fun x ↦ Finset.univ.sup fun i ↦ (x i).natAbs with hM
  set N : ℤ := 2 * (M : ℤ) + 1 with hNdef
  have hNpos : (0 : ℤ) < N := by positivity
  have hbound : ∀ x ∈ S, ∀ i, |x i| ≤ (M : ℤ) := by
    intro x hx i
    have h1 : (x i).natAbs ≤ M := by
      refine le_trans (Finset.le_sup (f := fun j ↦ (x j).natAbs) (Finset.mem_univ i)) ?_
      exact Finset.le_sup (f := fun y ↦ Finset.univ.sup fun j ↦ (y j).natAbs) hx
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  refine ⟨{ toFun := fun x ↦ ∑ i, x i * N ^ (i : ℕ)
            map_zero' := by simp
            map_add' := fun x y ↦ by
              simp only [Pi.add_apply, add_mul]
              rw [Finset.sum_add_distrib] }, ?_⟩
  intro x hx y hy hxy
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hxy
  have hzero : ∑ i, (x i - y i) * N ^ (i : ℕ) = 0 := by
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, hxy, sub_self]
  have hdig : ∀ i, |x i - y i| < N := by
    intro i
    have h1 := abs_le.mp (hbound x hx i)
    have h2 := abs_le.mp (hbound y hy i)
    rw [abs_lt]
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  funext i
  have := eq_zero_of_sum_mul_pow_eq_zero hNpos hdig hzero i
  linarith [this]

/-! ### Transferring coefficients along an injective relabelling of exponents -/

namespace Finsupp

variable {H : Type*} {N : Type*} {L : Type*} [AddCommMonoid L]

/-- Relabelling exponents injectively on the support preserves each coefficient. -/
theorem mapDomain_apply_of_injOn {psi : H → N} {x : H →₀ L}
    (hinj : Set.InjOn psi (x.support : Set H)) {g : H} (hg : g ∈ x.support) :
    Finsupp.mapDomain psi x (psi g) = x g :=
  Finsupp.mapDomain_apply' (x.support : Set H) x subset_rfl hinj hg

end Finsupp

end
