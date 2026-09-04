/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Reductions for Fermat's Last Theorem

This file develops primitive and coprimality reductions used in the regular-prime argument.
-/

@[expose] public section

open Int Finset

namespace FltRegular

namespace MayAssume

theorem coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    letI d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 := by
  have ha : a ≠ 0 := by grind
  let s : Finset ℤ := {a, b, c}
  set d : ℤ := s.gcd id
  have hadiv : d ∣ a := gcd_dvd (by grind)
  have hbdiv : d ∣ b := gcd_dvd (by grind)
  have hcdiv : d ∣ c := gcd_dvd (by grind)
  have hdzero : d ≠ 0 := fun hd ↦ by grind [Finset.gcd_eq_zero_iff.1 hd a (by grind)]
  have hdp : d ^ n ≠ 0 := pow_ne_zero _ hdzero
  refine ⟨?_, ?_, fun habs ↦ ?_⟩
  · obtain ⟨na, hna⟩ := hadiv
    obtain ⟨nb, hnb⟩ := hbdiv
    obtain ⟨nc, hnc⟩ := hcdiv
    rwa [← mul_left_inj' hdp, add_mul, ← mul_pow, ← mul_pow, ← mul_pow, hna, hnb, hnc,
      Int.mul_ediv_cancel_left _ hdzero, Int.mul_ediv_cancel_left _ hdzero,
      Int.mul_ediv_cancel_left _ hdzero, mul_comm, ← hna, mul_comm, ← hnb, mul_comm, ← hnc]
  · simpa [gcd_eq_gcd_image, d] using
      Finset.gcd_div_id_eq_one (show a ∈ ({a, b, c} : Finset ℤ) by simp) ha
  · simp only [mul_eq_zero] at habs
    rcases habs with ((ha' | hb') | hc') <;>
    grind [Int.eq_zero_of_ediv_eq_zero]

end MayAssume

theorem p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  have : Fact p.Prime := ⟨hpri⟩
  replace h := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_neg] at hbc hab
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_sub,
    ← Int.cast_sub] at h
  ring_nf at h
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, neg_eq_zero, mul_eq_zero] at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine Or.resolve_right h fun h3 ↦ ?_
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_zero_iff,
    Nat.dvd_prime Nat.prime_three] at h3
  exact h3.elim hpri.ne_one hp

theorem a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧
        ¬↑p ∣ x * y * z := by
  by_cases hab : a ≡ b [ZMOD p]
  swap
  · exact ⟨a, b, c, ⟨h, hgcd, hab, hprod, caseI⟩⟩
  refine ⟨a, -c, -b, ⟨?_, ?_, fun habs ↦ ?_, ?_, ?_⟩⟩
  · have hodd : Odd p := hpri.odd_of_ne_two (by omega)
    rw [hodd.neg_pow, hodd.neg_pow]
    linarith
  · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
      ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm]
  · have hp3 : p ≠ 3 := by omega
    rw [← ZMod.intCast_eq_intCast_iff] at habs hab
    rw [hab] at habs
    rw [ZMod.intCast_eq_intCast_iff] at habs hab
    obtain ⟨n, hn⟩ := p_dvd_c_of_ab_of_anegc hpri hp3 h hab habs
    refine caseI ⟨a * b * n, ?_⟩
    rw [hn]
    ring
  · convert hprod using 1
    ring
  · grind

end FltRegular
