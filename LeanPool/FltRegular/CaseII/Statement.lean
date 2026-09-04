/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import LeanPool.FltRegular.NumberTheory.RegularPrimes
import LeanPool.FltRegular.CaseII.InductionStep
import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The second case of Fermat's Last Theorem for regular primes

This file states the second-case contradiction in the cyclotomic-number-field setting.
-/

@[expose] public section

open scoped nonZeroDivisors NumberField
open Polynomial

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

namespace FltRegular

include hp hreg in
lemma not_exists_solution {m : ℕ} (hm : 1 ≤ m) :
  ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬((hζ.toInteger : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
    x' ^ p + y' ^ p = ε₃ * (((hζ.toInteger : 𝓞 K) - 1) ^ m * z') ^ p := by
  induction m, hm using Nat.le_induction with
  | base =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact zero_lt_one.not_ge (one_le_m hp hζ e hy hz)
  | succ m' _ IH =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact IH (exists_solution' hp hζ e hy hz hreg)

include hp hreg in
lemma not_exists_solution' : ¬∃ (x y z : 𝓞 K), ¬(hζ.toInteger : 𝓞 K) - 1 ∣ y ∧
    (hζ.toInteger : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z, hm, hz'', rfl⟩ :
      ∃ m z', 1 ≤ m ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
        z = ((hζ.toInteger : 𝓞 K) - 1) ^ m * z' := by
    obtain ⟨m, z', hz'', rfl⟩ :=
      WfDvdMonoid.max_power_factor hz' hζ.zeta_sub_one_prime'.irreducible
    refine ⟨m, z', ?_, hz'', rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [pow_zero, one_mul] at hz
      exact absurd hz hz''
    · exact h
  refine not_exists_solution hp hreg hζ hm ⟨x, y, z, 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]

lemma not_exists_Int_solution {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ¬↑p ∣ y ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField p ℚ)) (Set.mem_singleton p) hpri.1.ne_zero
  have := fun n ↦ IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
    (K := CyclotomicField p ℚ) p hζ (n := n)
  simp_rw [← this]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  refine not_exists_solution' (K := CyclotomicField p ℚ) hodd ?_
    hζ ⟨x, y, z, hy, hz, ?_, ?_⟩
  · simpa [IsRegularPrime, IsRegularNumber] using hreg
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]

lemma not_exists_Int_solution' {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ↑p ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_Int_solution hreg hodd ⟨x, y, z, ?_, hz, hz', e⟩
  intro hy
  have := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
  rw [← e, add_sub_cancel_right] at this
  replace this := (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow this
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_isUnit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, this]

/-- Case II of Fermat's Last Theorem for regular primes. -/
theorem caseII {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseII : ↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain hab | hc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd caseII
  · obtain ha | hb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_Int_solution' hreg hodd ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine not_exists_Int_solution' hreg hodd ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact not_exists_Int_solution' hreg hodd ⟨a, b, c, hgcd, hc, c0, e⟩

end FltRegular
