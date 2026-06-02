/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import LeanPool.LeanPolyABC.Lib.Wronskian
import LeanPool.LeanPolyABC.Lib.DivRadical
import LeanPool.LeanPolyABC.Lib.Max3

/-!
# LeanPool.LeanPolyABC.MasonStothers
-/

noncomputable section

open scoped Polynomial

open Polynomial UniqueFactorizationMonoid

namespace LeanPolyABC

variable {k : Type _} [Field k] [DecidableEq k]

namespace Ne

omit [DecidableEq k] in
theorem isUnit_C {u : k} (hu : u ≠ 0) : IsUnit (C u) :=
  Polynomial.isUnit_C.mpr hu.isUnit

omit [DecidableEq k] in
theorem C_ne_zero {u : k} (hu : u ≠ 0) : C u ≠ 0 :=
  Polynomial.C_ne_zero.mpr hu

end Ne

omit [DecidableEq k] in
theorem dvd_derivative_iff {a : k[X]} : a ∣ derivative a ↔ derivative a = 0 := by
  constructor
  · intro h
    by_cases a_nz : a = 0
    · rw [a_nz]; simp only [derivative_zero]
    by_contra deriv_nz
    have deriv_lt := degree_derivative_lt a_nz
    have le_deriv := Polynomial.degree_le_of_dvd h deriv_nz
    have lt_self := le_deriv.trans_lt deriv_lt
    simp only [lt_self_iff_false] at lt_self
  · intro h; rw [h]; simp

namespace IsCoprime

omit [DecidableEq k] in
theorem wronskian_eq_zero_iff {a b : k[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 := by
  constructor
  · intro hw
    rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ _
  · intro hdab
    obtain ⟨hda, hdb⟩ := hdab
    rw [wronskian]
    rw [hda, hdb]; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, sub_self]

end IsCoprime

/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0 and deg(a) ≥ deg(rad(abc)), we have
a' = b' = c' = 0.

Proof is based on this online note by Franz Lemmermeyer
http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf, which is essentially based on Noah Snyder's
proof ("An Alternative Proof of Mason's Theorem"), but slightly different.

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. (a / rad(a)) | W, and same for b and c. `poly_mod_rad_div_diff`
3. a / rad(a), b / rad(b), c / rad(c) are all coprime, so their product abc / rad(abc) also divides
   W. `poly_coprime_div_mul_div`
4. Using the assumption on degrees, deduce that deg (abc / rad(abc)) > deg W.
5. By `polynomial.degree_le_of_dvd`, W = 0.
6. Since W(a, b) = ab' - a'b = 0 and a and b are coprime, a' = 0. Similarly we have b' = c' = 0.
   `coprime_wronskian_eq_zero_const`
-/
namespace IsCoprime

protected theorem divRadical {a b : k[X]} (h : IsCoprime a b) :
    IsCoprime (Polynomial.divRadical a) (Polynomial.divRadical b) := by
  rw [← Polynomial.hMul_radical_divRadical a] at h
  rw [← Polynomial.hMul_radical_divRadical b] at h
  exact h.of_mul_left_right.of_mul_right_right

end IsCoprime

private theorem abc_subcall
    {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (_hab : IsCoprime a b) (_hbc : IsCoprime b c) (_hca : IsCoprime c a)
    (abc_dr_dvd_w : Polynomial.divRadical (a * b * c) ∣ w) :
    c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  have hab := mul_ne_zero ha hb
  have habc := mul_ne_zero hab hc
  set abc_dr_nd := (Polynomial.divRadical (a * b * c)).natDegree with def_abc_dr_nd
  set abc_r_nd := (radical (a * b * c)).natDegree with def_abc_r_nd
  have t11 : abc_dr_nd < a.natDegree + b.natDegree := by
    calc
      abc_dr_nd ≤ w.natDegree := Polynomial.natDegree_le_of_dvd abc_dr_dvd_w hw
      _ < a.natDegree + b.natDegree := by
        rw [wab] at hw ⊢; exact wronskian.natDegree_lt_add hw
  have t4 : abc_dr_nd + abc_r_nd < a.natDegree + b.natDegree + abc_r_nd :=
    Nat.add_lt_add_right t11 abc_r_nd
  have t3 : abc_dr_nd + abc_r_nd = a.natDegree + b.natDegree + c.natDegree := by
    calc
      abc_dr_nd + abc_r_nd =
          (Polynomial.divRadical (a * b * c) * radical (a * b * c)).natDegree := by
        rw [← Polynomial.natDegree_mul (Polynomial.divRadical_ne_zero habc)
          (radical_ne_zero (a * b * c))]
      _ = (a * b * c).natDegree := by
        rw [mul_comm _ (radical _)]; rw [Polynomial.hMul_radical_divRadical (a * b * c)]
      _ = a.natDegree + b.natDegree + c.natDegree := by
        rw [Polynomial.natDegree_mul hab hc, Polynomial.natDegree_mul ha hb]
  rw [t3] at t4
  exact Nat.lt_of_add_lt_add_left t4

omit [DecidableEq k] in
private theorem rot3_add {a b c : k[X]} : a + b + c = b + c + a := by ring

omit [DecidableEq k] in
private theorem rot3_mul {a b c : k[X]} : a * b * c = b * c * a := by ring

omit [DecidableEq k] in
private theorem rot3_isCoprime {a b c : k[X]}
    (h : a + b + c = 0) (hab : IsCoprime a b) : IsCoprime b c := by
  rw [add_eq_zero_iff_neg_eq] at h
  rw [← h, IsCoprime.neg_right_iff]
  convert IsCoprime.add_mul_left_right hab.symm 1
  rw [mul_one]

namespace Polynomial

theorem abc {a b c : k[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0) ∨
      Nat.max₃ a.natDegree b.natDegree c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  -- Utility assertions
  have hbc : IsCoprime b c := rot3_isCoprime hsum hab
  have hca : IsCoprime c a := rot3_isCoprime (by rw [← rot3_add]; exact hsum) hbc
  have wbc := wronskian_eq_of_sum_zero hsum
  set w := wronskian a b with wab
  have wca : w = wronskian c a := by
    rw [rot3_add] at hsum
    have h := wronskian_eq_of_sum_zero hsum
    rw [← wbc] at h; exact h
  have abc_dr_dvd_w : Polynomial.divRadical (a * b * c) ∣ w := by
    have adr_dvd_w := Polynomial.divRadical_dvd_wronskian_left a b
    have bdr_dvd_w := Polynomial.divRadical_dvd_wronskian_right a b
    have cdr_dvd_w := Polynomial.divRadical_dvd_wronskian_right b c
    rw [← wab] at adr_dvd_w bdr_dvd_w
    rw [← wbc] at cdr_dvd_w
    have cop_ab_dr := IsCoprime.divRadical hab
    have cop_bc_dr := IsCoprime.divRadical hbc
    have cop_ca_dr := IsCoprime.divRadical hca
    have cop_abc_dr := cop_ca_dr.symm.mul_left cop_bc_dr
    have abdr_dvd_w := cop_ab_dr.mul_dvd adr_dvd_w bdr_dvd_w
    have abcdr_dvd_w := cop_abc_dr.mul_dvd abdr_dvd_w cdr_dvd_w
    convert abcdr_dvd_w using 1
    rw [← Polynomial.divRadical_hMul hab]
    rw [← Polynomial.divRadical_hMul _]
    exact hca.symm.mul_left hbc
  by_cases hw : w = 0
  · left
    rw [hw] at wab wbc
    obtain ⟨ga, gb⟩ := (IsCoprime.wronskian_eq_zero_iff hab).mp wab.symm
    obtain ⟨_, gc⟩ := (IsCoprime.wronskian_eq_zero_iff hbc).mp wbc.symm
    exact ⟨ga, gb, gc⟩
  · right
    rw [Nat.max₃_add_distrib_right, Nat.max₃_le]
    refine ⟨?_, ?_, ?_⟩
    · rw [rot3_mul] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [rot3_mul, rot3_mul] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption

theorem abc_char0 [CharZero k] {a b c : k[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0) ∨
      Nat.max₃ a.natDegree b.natDegree c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  rcases LeanPolyABC.Polynomial.abc ha hb hc hab hsum with _ | h
  · left
    repeat (any_goals constructor)
    all_goals (apply natDegree_eq_zero_of_derivative_eq_zero; tauto)
  · tauto

end Polynomial

omit [DecidableEq k] in
theorem isUnit_iff_natDegree_eq_zero {a : k[X]} (ha : a ≠ 0) :
    IsUnit a ↔ a.natDegree = 0 := by
  rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree ha]
  simp only [Nat.cast_eq_zero]

theorem natDegree_radical_eq_zero_iff {a : k[X]} :
    (radical a).natDegree = 0 ↔ a.natDegree = 0 := by
  by_cases ha : a = 0
  · rw [ha]
    simp only [radical_zero_eq_one, natDegree_zero, natDegree_one]
  · rw [← isUnit_iff_natDegree_eq_zero ha, ← isUnit_iff_natDegree_eq_zero (radical_ne_zero _)]
    rw [radical_isUnit_iff ha]

namespace Polynomial

-- Variant of Mason--Stothers not requiring coprimality of `a` and `b`
theorem abc'_char0 [CharZero k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hsum : a + b + c = 0) :
    (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0) ∨
      Nat.max₃ a.natDegree b.natDegree c.natDegree + 1 ≤
      (radical a).natDegree + (radical b).natDegree + c.natDegree := by
  rcases gcd_dvd_left a b with ⟨a', eq_a'⟩
  rcases gcd_dvd_right a b with ⟨b', eq_b'⟩
  have hab : IsCoprime a' b' := by
    rw [← gcd_isUnit_iff]
    apply isUnit_gcd_of_eq_mul_gcd eq_a' eq_b'
    apply gcd_ne_zero_of_right
    assumption
  rw [eq_a', mul_ne_zero_iff] at ha
  rcases ha with ⟨hd, ha'⟩
  rw [eq_b', mul_ne_zero_iff] at hb
  rcases hb with ⟨_, hb'⟩
  set d := gcd a b with def_d
  set c' := -(a' + b') with def_c'
  have eq_c' : c = d * c' := by
    rw [def_c', mul_neg, eq_neg_iff_add_eq_zero,
        mul_add, add_comm c _, ← eq_a', ← eq_b']
    exact hsum
  have hc' : c' ≠ 0 := by
    rw [eq_c', mul_ne_zero_iff] at hc; exact hc.right
  have hsum' : a' + b' + c' = 0 := by
    rw [eq_a', eq_b', eq_c', ← mul_add, ← mul_add, mul_eq_zero] at hsum
    rcases hsum with dz | goal
    · exact absurd dz hd
    · exact goal
  have hbc := rot3_isCoprime hsum' hab
  have hca := rot3_isCoprime (by rw [← rot3_add]; exact hsum') hbc
  rcases LeanPolyABC.Polynomial.abc_char0 ha' hb' hc' hab hsum' with heq | hineq
  · by_cases hd' : (natDegree d) = 0
    · left
      rw [eq_a', eq_b', eq_c']
      (repeat rw [Polynomial.natDegree_mul _ _]) <;> try assumption
      simp only [hd', zero_add]
      exact heq
    · right
      simp only [Polynomial.natDegree_eq_zero] at heq
      rcases heq with ⟨⟨ca', eq_ca'⟩, ⟨cb', eq_cb'⟩, ⟨cc', eq_cc'⟩⟩
      rw [eq_comm] at eq_ca' eq_cb' eq_cc'
      rw [eq_a', eq_b', eq_c']
      rw [natDegree_mul hd ha', natDegree_mul hd hb', natDegree_mul hd hc']
      rw [← Nat.max₃_add_distrib_left _ _ _ _]
      simp_rw [eq_ca', eq_cb', eq_cc', C_ne_zero] at ha' hb' hc' ⊢
      simp only [Nat.max₃, natDegree_C, max_self, add_zero]
      rw [add_comm _ 1, add_le_add_iff_right]
      rw [radical_mul_unit_right (Ne.isUnit_C ha'),
          radical_mul_unit_right (Ne.isUnit_C hb')]
      revert hd'
      rw [not_imp_comm]
      simp only [not_le, Nat.lt_one_iff, add_eq_zero, and_self]
      exact natDegree_radical_eq_zero_iff.mp
  · right
    rw [eq_a', eq_b', eq_c']
    (repeat rw [mul_comm d _, Polynomial.natDegree_mul _ hd]) <;> try assumption
    rw [← Nat.max₃_add_distrib_right _ _ _ _]
    rw [add_right_comm, ← add_assoc, Nat.add_le_add_iff_right]
    have habc := hca.symm.mul_left hbc
    rw [radical_hMul habc, natDegree_mul (radical_ne_zero _) (radical_ne_zero _)] at hineq
    rw [radical_hMul hab, natDegree_mul (radical_ne_zero _) (radical_ne_zero _)] at hineq
    apply le_trans hineq
    apply add_le_add_three <;> apply natDegree_le_of_dvd
    · exact radical_dvd_radical_self_mul hd
    · exact radical_ne_zero _
    · exact radical_dvd_radical_self_mul hd
    · exact radical_ne_zero _
    · exact radical_dvd_self _
    · exact hc'

end Polynomial

end LeanPolyABC
