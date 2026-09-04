/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Auxiliary lemmas for the second case

Supporting ideal-theoretic and arithmetic lemmas used in the second case of Fermat's Last Theorem.
-/

@[expose] public section

variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}

open scoped nonZeroDivisors
open Polynomial

open FractionalIdeal in
lemma exists_not_dvd_spanSingleton_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : Prime x) (I J : Ideal R)
    (hI : ¬ (Ideal.span <| singleton x) ∣ I) (hJ : ¬ (Ideal.span <| singleton x) ∣ J)
    (h : Submodule.IsPrincipal ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) : ∃ a b : R,
    ¬(x ∣ a) ∧ ¬(x ∣ b) ∧
      spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
  by_contra hcontra
  have hI' : (I : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [← coeIdeal_bot, Ne, coeIdeal_inj]
    rintro rfl
    exact hI (dvd_zero _)
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [← coeIdeal_bot, Ne, coeIdeal_inj]
    rintro rfl
    exact hJ (dvd_zero _)
  have hpow : ∀ n : ℕ, 1 ≤ n → ¬∃ a b : R, ¬(x ^ n ∣ a) ∧ ¬(x ^ n ∣ b) ∧
    spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        simp_rw [pow_one]
        exact hcontra
    | succ n' hn' IH =>
        rintro ⟨a, b, ha, hb, e⟩
        have e₀ := e
        rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton,
          ← one_div_spanSingleton, ← mul_div_assoc, mul_one, div_eq_iff,
          ← mul_div_right_comm, eq_div_iff hJ', ← coeIdeal_span_singleton,
          ← coeIdeal_span_singleton, ← coeIdeal_mul, ← coeIdeal_mul, coeIdeal_inj] at e
        on_goal 2 =>
          rw [Ne, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
            (IsFractionRing.injective R K).eq_iff]
          rintro rfl
          exact hb (dvd_zero _)
        by_cases h : x ^ n' ∣ a
        · have ha' : x ∣ a := (dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hn')).trans h
          have hb' : x ∣ b := by
            have : gcd (Ideal.span <| singleton x) I = 1 := by
              rwa [Irreducible.gcd_eq_one_iff]
              · rwa [irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
                · exact hx.ne_zero
                · rw [Ne, Ideal.span_singleton_eq_bot]
                  exact hx.ne_zero
            rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at ha' ⊢
            replace h := ha'.trans (dvd_mul_right _ J)
            rwa [e, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at h
          obtain ⟨a', rfl⟩ := ha'
          obtain ⟨b', rfl⟩ := hb'
          rw [pow_succ', mul_dvd_mul_iff_left hx.ne_zero] at ha hb
          rw [_root_.map_mul, _root_.map_mul, mul_div_mul_left] at e₀
          · exact IH ⟨a', b', ha, hb, e₀⟩
          · rw [Ne, ← (algebraMap R K).map_zero, (IsFractionRing.injective R K).eq_iff]
            exact hx.ne_zero
        · refine IH ⟨a, b, h, ?_, e₀⟩
          intro hb
          apply h
          rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at hb ⊢
          replace hb := hb.trans (dvd_mul_left _ I)
          have : gcd (Ideal.span <| singleton <| x ^ n') J = 1 := by
            rwa [← Ideal.isCoprime_iff_gcd, ← Ideal.span_singleton_pow,
              IsCoprime.pow_left_iff, Ideal.isCoprime_iff_gcd, Irreducible.gcd_eq_one_iff]
            · rwa [irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
              · exact hx.ne_zero
              · rw [Ne, Ideal.span_singleton_eq_bot]
                exact hx.ne_zero
            · rwa [Nat.pos_iff_ne_zero, ← Nat.one_le_iff_ne_zero]
          rwa [← e, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at hb
  rw [isPrincipal_iff] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ a
  by_cases h : s = 0
  · rw [div_eq_iff hJ', h, IsLocalization.mk'_zero, spanSingleton_zero, zero_mul] at ha
    exact hI' ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hx.not_isUnit h
  obtain ⟨m, hm⟩ :=
    FiniteMultiplicity.of_not_isUnit hx.not_isUnit (nonZeroDivisors.ne_zero t.prop)
  rw [IsFractionRing.mk'_eq_div] at ha
  refine hpow (n + m + 1) (Nat.le_add_left 1 (n + m))
    ⟨s, t, (fun hs ↦ ?_), (fun ht ↦ ?_), ha.symm⟩
  · exact hn (dvd_trans (pow_dvd_pow _ (by lia)) hs)
  · exact hm (dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ _)) ht)
