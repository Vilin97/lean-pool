/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import LeanPool.LeanPolyABC.MasonStothers

/-!
# LeanPool.LeanPolyABC.Corollaries.Davenport
-/

noncomputable section

open scoped Polynomial

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

variable {k : Type _} [Field k] [DecidableEq k]

omit [DecidableEq k] in
lemma ne_zero_of_natDegree_gt_0 {a : k[X]} (ha : a.natDegree > 0) : a ≠ 0 := fun h => by
  simp only [h, natDegree_zero, gt_iff_lt, lt_self_iff_false] at ha

namespace Polynomial

omit [DecidableEq k] in
/-- Davenport's theorem

For any nonzero polynomial a, b ∈ k[t] with k of characteristic zero,
deg(a) + 2 ≤ 2 * deg(a^3 - b^2).

Proof) Apply ABC for (-a^3, b^2, a^3 - b^2).
-/
theorem davenport [CharZero k] {a b : k[X]}
    (ha : a.natDegree > 0) (hb : b.natDegree > 0) (hnz : a ^ 3 - b ^ 2 ≠ 0) :
    a.natDegree + 2 ≤ 2 * (a ^ 3 - b ^ 2).natDegree := by
  classical
  have ha3 : -a ^ 3 ≠ 0 := neg_ne_zero.mpr <| pow_ne_zero 3 <| ne_zero_of_natDegree_gt_0 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 <| ne_zero_of_natDegree_gt_0 hb
  rcases Polynomial.abc'_char0 ha3 hb2 hnz (by ring_nf) with heq | hineq
  · simp only [natDegree_neg, natDegree_pow] at heq
    omega
  · rw [Nat.succ_le_iff] at hineq
    simp only [Nat.max₃, natDegree_neg, natDegree_pow,
      radical_neg, Nat.ofNat_pos, radical_pow, max_lt_iff] at hineq
    nlinarith only [hineq.1, hineq.2, radical_natDegree_le a, radical_natDegree_le b]

end Polynomial

omit [DecidableEq k] in
-- Auxiliary lemma to remove nonzero hypothesis using coprimality and a' ≠ 0.
theorem isCoprime_nonzero_c {a b : k[X]} (h : IsCoprime a b) (ha : derivative a ≠ 0) :
    a ^ 3 - b ^ 2 ≠ 0 := by
  by_contra h_eq_zero
  rw [sub_eq_zero] at h_eq_zero
  have hp : IsCoprime (a ^ 3) (b ^ 2) := h.pow
  rw [← h_eq_zero, isCoprime_self, isUnit_pow_iff, isUnit_iff] at hp
  · rcases hp with ⟨r, _, eq_a⟩
    rw [← eq_a] at ha; exact ha derivative_C
  · norm_num

namespace Polynomial

omit [DecidableEq k] in
/-- Davenport's theorem for general field k of any characteristic

For any coprime polynomial a, b ∈ k[t] with nonzero derivatives,
deg(a) + 2 ≤ 2 * deg(a^3 - b^2).
Proof) Apply ABC for (-a^3, b^2, a^3 - b^2).
-/
theorem davenport' {a b : k[X]} (hab : IsCoprime a b) (haderiv : derivative a ≠ 0)
    (hbderiv : derivative b ≠ 0) : a.natDegree + 2 ≤ 2 * (a ^ 3 - b ^ 2).natDegree := by
  classical
  have hnz : a ^ 3 - b ^ 2 ≠ 0 := isCoprime_nonzero_c hab haderiv
  have ha : a ≠ 0 := fun ha => haderiv (ha.symm ▸ derivative_zero)
  have hb : b ≠ 0 := fun hb => hbderiv (hb.symm ▸ derivative_zero)
  have h1 : IsCoprime (a ^ 3) (a ^ 3 - b ^ 2) := by
    rwa [← IsCoprime.neg_right_iff, neg_sub, sub_eq_add_neg, neg_eq_neg_one_mul,
      IsCoprime.add_mul_right_right_iff, IsCoprime.pow_iff three_pos two_pos]
  have h2 : IsCoprime (b ^ 2) (a ^ 3 - b ^ 2) := by
    rwa [sub_eq_add_neg, neg_eq_neg_one_mul, IsCoprime.add_mul_right_right_iff,
      IsCoprime.pow_iff two_pos three_pos, isCoprime_comm]
  rcases
    Polynomial.abc (neg_ne_zero.mpr (pow_ne_zero 3 ha)) (pow_ne_zero 2 hb) hnz hab.pow.neg_left
      (by rw [sub_eq_add_neg, add_add_add_comm, neg_add_cancel, add_neg_cancel, add_zero]) with
    h | h
  · -- When we have vanishing derivatives. This condition implies 3 = 0 = 2, which is impossible for
    -- any field k.
    rw [derivative_neg, neg_eq_zero, derivative_pow, derivative_pow, Nat.add_one_sub_one,
      Nat.add_one_sub_one, mul_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero, or_iff_left haderiv,
      or_iff_left hbderiv, or_iff_left (pow_ne_zero 2 ha), or_iff_left (pow_ne_zero 1 hb)] at h
    replace h := h.1.trans h.2.1.symm
    rw [← sub_eq_zero, ← C_sub, ← Nat.cast_sub (Nat.le_succ 2), Nat.cast_one, C_1] at h
    exact (one_ne_zero h).elim
  · -- When we have inequality from ABC.
    rw [natDegree_neg, Nat.max₃, max_eq_left (natDegree_sub_le _ _), neg_mul, neg_mul, radical_neg,
      radical_hMul (h1.mul_left h2), radical_hMul hab.pow, radical_pow a three_pos,
      radical_pow b two_pos,
      natDegree_mul (mul_ne_zero (radical_ne_zero a) (radical_ne_zero b)) (radical_ne_zero _),
      natDegree_mul (radical_ne_zero a) (radical_ne_zero b), natDegree_pow, natDegree_pow, ←
      max_add_add_right] at h
    replace h :=
      le_trans h
        (add_le_add (add_le_add (radical_natDegree_le _) (radical_natDegree_le _)) <|
          radical_natDegree_le _)
    rw [max_le_iff] at h
    -- Add two inequalities and simplifying it gives the desired inequality.
    nlinarith only [add_le_add h.1 h.2]

end Polynomial

end LeanPolyABC
