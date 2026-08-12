/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Layer 3: Root Counting for Quadratic Congruences

This file counts solutions to `x² ≡ c (mod p^n)` for prime powers `p^n`.
These are the "analytic inputs" for the ideal-counting theorems (Layer 4).
-/

namespace QuadraticOrder

open Finset

/-! ## Definition -/

/-- The number of elements `x` in `ZMod n` satisfying `x ^ 2 = c`. -/
def cardSqrts (n : ℕ) [NeZero n] (c : ZMod n) : ℕ :=
  (univ.filter (fun x : ZMod n => x ^ 2 = c)).card

/-! ## Base case: odd prime `p` -/

section PrimeBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- For an odd prime `p`, the number of solutions to `x² = c` in `ZMod p`
equals `legendreSym p c + 1`. -/
theorem cardSqrts_prime (hp2 : p ≠ 2) (c : ℤ) :
    (cardSqrts p ((c : ℤ) : ZMod p) : ℤ) = legendreSym p c + 1 := by
  unfold cardSqrts
  have : (univ.filter (fun x : ZMod p => x ^ 2 = (c : ZMod p))) =
      {x : ZMod p | x ^ 2 = (c : ZMod p)}.toFinset := by
    ext x; simp [Finset.mem_filter]
  rw [this]
  exact legendreSym.card_sqrts p hp2 c

-- Linear order on `ZMod p` is not available, so we use `legendreSym`.
end PrimeBase

/-! ## Odd prime powers -/

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

private lemma cardSqrtsPrimePowCoprimeTwoMulNeZero (hp2 : p ≠ 2)
    {k : ℕ} {x : ZMod (p ^ (k + 1))}
    (h_x_nz : ((x.val : ℕ) : ZMod p) ≠ 0) :
    (2 : ZMod p) * (x.val : ZMod p) ≠ 0 := by
  intro h_zero
  cases mul_eq_zero.mp h_zero with
  | inl h2 =>
    have h_p_dvd_2 : (p : ℤ) ∣ 2 := by
      have h2' : ((2 : ℤ) : ZMod p) = 0 := by
        simp_all
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2'
      exact h2'
    have hp_le_2 : p ≤ 2 := by
      have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by decide) h_p_dvd_2
      omega
    have hp_ge_2 : 2 ≤ p := Fact.out (p := Nat.Prime p) |>.two_le
    have : p = 2 := by omega
    exact hp2 this
  | inr hx =>
    exact h_x_nz hx

private lemma cardSqrtsPrimePowCoprimeLift (hp2 : p ≠ 2)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) (k : ℕ)
    (h_fiber :
      ∀ (x : ZMod (p ^ (k + 1))) (y : ZMod (p ^ (k + 2))),
        ZMod.cast y = x ↔
          ∃ (t : ZMod p), y = (x.val : ZMod (p ^ (k + 2))) +
            (t.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2)))) :
    ∀ (x : ZMod (p ^ (k + 1))), x^2 = (c : ZMod (p ^ (k + 1))) →
      ∃! (y : ZMod (p ^ (k + 2))), y.cast = x ∧ y^2 = (c : ZMod (p ^ (k + 2))) := by
  intro x hx
  have h_pow_sq : ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) ^ 2 = 0 := by
    rw [pow_two]
    rw [← Nat.cast_mul]
    have h_pow_add : p ^ (k + 1) * p ^ (k + 1) = p ^ (2 * k + 2) := by ring
    rw [h_pow_add]
    have h_dvd : p ^ (k + 2) ∣ p ^ (2 * k + 2) := pow_dvd_pow p (by omega)
    obtain ⟨m, hm⟩ := h_dvd
    simp_all
  have h_dvd_diff : (p : ℤ) ^(k + 1) ∣ (c : ℤ) - (x.val : ℤ)^2 := by
    have h_sub : (((x.val : ℤ)^2 - c : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
      simp_all
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_sub
    have h_neg : (c : ℤ) - (x.val : ℤ)^2 = -((x.val : ℤ)^2 - c) := by ring
    rw [h_neg]
    exact dvd_neg.mpr h_sub
  have h_x_nz : ((x.val : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((x.val : ℤ) : ZMod p) = 0 := by
      simp_all
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0'
    obtain ⟨L, hL⟩ := h_dvd_diff
    have h_c_eq : (c : ℤ) = (x.val : ℤ)^2 + (p : ℤ) ^(k + 1) * L := by linarith
    have h_p_dvd_c : (p : ℤ) ∣ c := by
      rw [h_c_eq]
      apply dvd_add
      · rw [pow_two]
        exact dvd_mul_of_dvd_left h0' (x.val : ℤ)
      · have hp_dvd_pow : (p : ℤ) ∣ (p : ℤ) ^(k + 1) := dvd_pow_self _ (by omega)
        exact dvd_mul_of_dvd_left hp_dvd_pow L
    exact hc h_p_dvd_c
  obtain ⟨L, hL⟩ := h_dvd_diff
  let t : ZMod p := (L : ZMod p) * (2 * (x.val : ZMod p))⁻¹
  have h_c_eq' :
      (c : ZMod (p ^ (k + 2))) =
        (x.val : ZMod (p ^ (k + 2)))^2 +
          (p ^ (k + 1) : ZMod (p ^ (k + 2))) * (L : ZMod (p ^ (k + 2))) := by
    have hL' : (c : ℤ) = (x.val : ℤ)^2 + (p : ℤ) ^(k + 1) * L := by linarith
    simp_all
  have h_t_prop : (2 : ZMod p) * ((x.val : ℕ) : ZMod p) * t = (L : ZMod p) := by
    dsimp [t]
    have h_assoc :
        (2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
            ((L : ZMod p) * ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹) =
          ((2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
              ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹) * (L : ZMod p) := by
      ring
    rw [h_assoc]
    have h_inv :
        (2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
            ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹ = 1 := by
      exact mul_inv_cancel₀ (cardSqrtsPrimePowCoprimeTwoMulNeZero (p := p) hp2 h_x_nz)
    rw [h_inv, one_mul]
  let y : ZMod (p ^ (k + 2)) :=
    (x.val : ZMod (p ^ (k + 2))) +
      (t.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2)))
  have hy_cast : y.cast = x := by
    have h_fib := h_fiber x y
    rw [h_fib]
    use t
  have hy_sq : y^2 = c := by
    have h_expand :
        y^2 =
          (x.val : ZMod (p ^ (k + 2)))^2 +
            2 * (x.val : ZMod (p ^ (k + 2))) *
              (t.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2))) +
            (t.val : ZMod (p ^ (k + 2)))^2 *
              ((p ^ (k + 1) : ZMod (p ^ (k + 2))))^2 := by
      dsimp [y]
      ring
    rw [h_expand]
    have h_pow_sq' : ((p : ZMod (p ^ (k + 2)))^(k + 1))^2 = 0 := by
      simp_all
    rw [h_pow_sq']
    simp only [mul_zero, add_zero]
    rw [h_c_eq']
    have h_t_prop' : (p : ℤ) ∣ 2 * (x.val : ℤ) * (t.val : ℤ) - L := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp_all
    obtain ⟨m', hm'⟩ := h_t_prop'
    have h_linear : 2 * (x.val : ℤ) * (t.val : ℤ) = L + p * m' := by
      linarith
    have h_eq' :
        2 * (x.val : ℤ) * (t.val : ℤ) * (p : ℤ) ^(k + 1) =
          (L : ℤ) * (p : ℤ) ^(k + 1) + m' * (p : ℤ) ^(k + 2) := by
      calc 2 * (x.val : ℤ) * (t.val : ℤ) * (p : ℤ) ^(k + 1)
        _ = (L + p * m') * (p : ℤ) ^(k + 1) := by rw [h_linear]
        _ = (L : ℤ) * (p : ℤ) ^(k + 1) + m' * (p : ℤ) ^(k + 2) := by ring
    have h_cast := congr_arg (fun (a : ℤ) => (a : ZMod (p ^ (k + 2)))) h_eq'
    push_cast at h_cast
    have hp_pow_zero : (p : ZMod (p ^ (k + 2)))^(k + 2) = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self (p ^ (k + 2))
    rw [hp_pow_zero, mul_zero, add_zero] at h_cast
    rw [h_cast, mul_comm (L : ZMod (p ^ (k + 2)))]
  refine ⟨y, ⟨hy_cast, hy_sq⟩, ?_⟩
  intro y' ⟨hy'_cast, hy'_sq⟩
  have h_fib' := h_fiber x y' |>.mp hy'_cast
  obtain ⟨t', ht'⟩ := h_fib'
  have hy'_expand :
      y'^2 =
        (x.val : ZMod (p ^ (k + 2)))^2 +
          2 * (x.val : ZMod (p ^ (k + 2))) *
            (t'.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2))) := by
    rw [ht']
    have :
        (↑x.val + ↑t'.val * ↑p ^ (k + 1) : ZMod (p ^ (k + 2)))^2 =
          ↑x.val ^ 2 + 2 * ↑x.val * ↑t'.val * ↑p ^ (k + 1) +
            ↑t'.val ^ 2 * (↑p ^ (k + 1)) ^ 2 := by
      ring
    simp_all
  have h_eq'_mod :
      2 * (x.val : ZMod (p ^ (k + 2))) *
          (t'.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2))) =
        (p ^ (k + 1) : ZMod (p ^ (k + 2))) * (L : ZMod (p ^ (k + 2))) := by
    simp_all
  have h_dvd :
      (p : ℤ) ^(k + 2) ∣
        (2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ) ^(k + 1) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ) ^(k + 1))
      (p ^ (k + 2))).mp ?_
    have h_ring :
        (((2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ) ^(k + 1) : ℤ) :
            ZMod (p ^ (k + 2))) =
          2 * (x.val : ZMod (p ^ (k + 2))) *
              (t'.val : ZMod (p ^ (k + 2))) *
              (p : ZMod (p ^ (k + 2)))^(k + 1) -
            (p : ZMod (p ^ (k + 2)))^(k + 1) * (L : ZMod (p ^ (k + 2))) := by
      push_cast
      ring
    simp_all
  have hp_pow_nz : (p : ℤ) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.prime_iff_prime_int.mp hp.out).ne_zero
  have h_div : (p : ℤ) ∣ 2 * (x.val : ℤ) * (t'.val : ℤ) - L := by
    have h_dvd' :
        (p : ℤ) * (p : ℤ) ^(k + 1) ∣
          (2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ) ^(k + 1) := by
      rw [mul_comm, ← pow_succ]
      exact h_dvd
    exact Int.dvd_of_mul_dvd_mul_right hp_pow_nz h_dvd'
  have h_t'_prop : (2 : ZMod p) * (x.val : ZMod p) * t' = (L : ZMod p) := by
    have h_zero : ((2 * (x.val : ℤ) * (t'.val : ℤ) - L : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h_div
    push_cast at h_zero
    have :
        (2 : ZMod p) * (x.val : ZMod p) * (t'.val : ZMod p) =
          (L : ZMod p) := sub_eq_zero.mp h_zero
    simp_all
  have h_x_nz' : (2 : ZMod p) * (x.val : ZMod p) ≠ 0 :=
    cardSqrtsPrimePowCoprimeTwoMulNeZero (p := p) hp2 h_x_nz
  have ht_eq : t' = t := by
    have :
        (2 : ZMod p) * (x.val : ZMod p) * t' =
          (2 : ZMod p) * (x.val : ZMod p) * t := by
      rw [h_t'_prop, h_t_prop]
    exact mul_left_cancel₀ h_x_nz' this
  have ht_val_eq : t'.val = t.val := by rw [ht_eq]
  rw [ht']
  rw [ht_val_eq]

private lemma cardSqrtsPrimePowCoprimeSucc (hp2 : p ≠ 2)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) (k : ℕ)
    (ih :
      cardSqrts (p ^ (k + 1)) ((c : ℤ) : ZMod (p ^ (k + 1))) =
        if legendreSym p c = 1 then 2 else 0) :
    cardSqrts (p ^ (k + 2)) ((c : ℤ) : ZMod (p ^ (k + 2))) =
      if legendreSym p c = 1 then 2 else 0 := by
  have h_fiber :
      ∀ (x : ZMod (p ^ (k + 1))) (y : ZMod (p ^ (k + 2))),
        ZMod.cast y = x ↔
          ∃ (t : ZMod p), y = (x.val : ZMod (p ^ (k + 2))) +
            (t.val : ZMod (p ^ (k + 2))) * (p ^ (k + 1) : ZMod (p ^ (k + 2))) := by
    intro x y
    constructor
    · intro h
      have h_val : (ZMod.cast y : ZMod (p ^ (k + 1))).val = x.val := by rw [h]
      have h_mod : y.val % p ^ (k + 1) = x.val := by
        have h_val : (ZMod.cast y : ZMod (p ^ (k + 1))).val = x.val := by rw [h]
        rw [ZMod.cast_eq_val] at h_val
        rw [ZMod.val_natCast] at h_val
        exact h_val
      let t := y.val / p ^ (k + 1)
      have h_y_val : y.val = x.val + t * p ^ (k + 1) := by
        dsimp [t]
        have h_div_add_mod := Nat.div_add_mod y.val (p ^ (k + 1))
        rw [h_mod] at h_div_add_mod
        rw [mul_comm (p ^ (k + 1))] at h_div_add_mod
        rw [add_comm] at h_div_add_mod
        exact h_div_add_mod.symm
      have h_t_lt : t < p := by
        dsimp [t]
        apply Nat.div_lt_of_lt_mul
        have h_y_lt : y.val < p ^ (k + 2) := y.val_lt
        have h_pow : p ^ (k + 2) = p * p ^ (k + 1) := by ring
        linarith
      have h_t_val : ((t : ZMod p).val : ZMod (p ^ (k + 2))) = (t : ZMod (p ^ (k + 2))) := by
        rw [ZMod.val_cast_of_lt h_t_lt]
      use (t : ZMod p)
      rw [h_t_val]
      apply ZMod.val_injective
      rw [ZMod.val_add]
      rw [ZMod.val_mul]
      have h_x_lt : x.val < p ^ (k + 2) := by
        have h1 := x.val_lt
        have hp_two_le := Nat.Prime.two_le hp.out
        have h_pow : p ^ (k + 2) = p ^ (k + 1) * p := by ring
        have : 1 ≤ p := by omega
        nlinarith
      have h_t_lt' : t < p ^ (k + 2) := by
        have hp_two_le := Nat.Prime.two_le hp.out
        have h_pow : p ^ (k + 2) = p ^ (k + 1) * p := by ring
        have : 0 < p ^ (k + 1) := by positivity
        nlinarith
      have h_p_pow_lt : p ^ (k + 1) < p ^ (k + 2) := by
        have hp_two_le := Nat.Prime.two_le hp.out
        have h_pow : p ^ (k + 2) = p ^ (k + 1) * p := by ring
        have : 0 < p ^ (k + 1) := by positivity
        nlinarith
      rw [ZMod.val_cast_of_lt h_x_lt]
      rw [ZMod.val_cast_of_lt h_t_lt']
      have h_pow_eq :
          (p : ZMod (p ^ (k + 2))) ^ (k + 1) = ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) := by
        norm_cast
      rw [h_pow_eq]
      rw [ZMod.val_cast_of_lt h_p_pow_lt]
      have h_t_mul_lt : t * p ^ (k + 1) < p ^ (k + 2) := by
        have hp_two_le := Nat.Prime.two_le hp.out
        have h_pow : p ^ (k + 2) = p ^ (k + 1) * p := by ring
        have : 0 < p ^ (k + 1) := by positivity
        nlinarith
      rw [Nat.mod_eq_of_lt h_t_mul_lt]
      rw [← h_y_val]
      rw [Nat.mod_eq_of_lt y.val_lt]
    · rintro ⟨t, rfl⟩
      have h_dvd : p ^ (k + 1) ∣ p ^ (k + 2) := pow_dvd_pow p (by omega)
      rw [ZMod.cast_add h_dvd]
      rw [ZMod.cast_mul h_dvd]
      have h_pow :
          ((p : ZMod (p ^ (k + 2))) ^ (k + 1)) =
            ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) := by
        simp
      rw [h_pow]
      have h_cast :
          (ZMod.cast ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) :
            ZMod (p ^ (k + 1))) = 0 := by
        rw [ZMod.cast_natCast h_dvd]
        rw [ZMod.natCast_self]
      have h_id :
          (ZMod.cast ((x.val : ℕ) : ZMod (p ^ (k + 2))) :
            ZMod (p ^ (k + 1))) = x := by
        rw [ZMod.cast_natCast h_dvd]
        simp_all
      simp_all
  have h_map :
      ∀ (y : ZMod (p ^ (k + 2))), y^2 = (c : ZMod (p ^ (k + 2))) →
        (ZMod.cast y : ZMod (p ^ (k + 1)))^2 = (c : ZMod (p ^ (k + 1))) := by
    intro y hy
    have h_dvd : p ^ (k + 1) ∣ p ^ (k + 2) := pow_dvd_pow p (by omega)
    rw [pow_two] at hy ⊢
    rw [← ZMod.cast_mul h_dvd]
    simp_all
  have h_lift := cardSqrtsPrimePowCoprimeLift (p := p) hp2 c hc k h_fiber
  have h_fiber_card :
      ∀ x ∈ univ.filter (fun x : ZMod (p ^ (k + 1)) =>
          x ^ 2 = (c : ZMod (p ^ (k + 1)))),
        ((univ.filter (fun y : ZMod (p ^ (k + 2)) =>
            y ^ 2 = (c : ZMod (p ^ (k + 2))))).filter
          (fun y => ZMod.cast y = x)).card = 1 := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨y, ⟨hy_cast, hy_sq⟩, hy_uniq⟩ := h_lift x hx
    rw [Finset.card_eq_one]
    refine ⟨y, ?_⟩
    ext y'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hy'_sq, hy'_cast⟩
      exact hy_uniq y' ⟨hy'_cast, hy'_sq⟩
    · rintro rfl
      exact ⟨hy_sq, hy_cast⟩
  unfold cardSqrts
  have h_sum :
      ((univ.filter (fun y : ZMod (p ^ (k + 2)) =>
        y ^ 2 = (c : ZMod (p ^ (k + 2))))).card) =
        ∑ x ∈ univ.filter (fun x : ZMod (p ^ (k + 1)) =>
            x ^ 2 = (c : ZMod (p ^ (k + 1)))),
          ((univ.filter (fun y : ZMod (p ^ (k + 2)) =>
              y ^ 2 = (c : ZMod (p ^ (k + 2))))).filter
            (fun y => ZMod.cast y = x)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro y hy
    simp_all
  rw [h_sum]
  have h_sum_one :
      (∑ x ∈ univ.filter (fun x : ZMod (p ^ (k + 1)) =>
          x ^ 2 = (c : ZMod (p ^ (k + 1)))),
        ((univ.filter (fun y : ZMod (p ^ (k + 2)) =>
            y ^ 2 = (c : ZMod (p ^ (k + 2))))).filter
          (fun y => ZMod.cast y = x)).card) =
        ∑ x ∈ univ.filter (fun x : ZMod (p ^ (k + 1)) =>
          x ^ 2 = (c : ZMod (p ^ (k + 1)))), 1 := by
    apply Finset.sum_congr rfl
    simp_all
  rw [h_sum_one]
  rw [Finset.sum_const]
  have h_smul :
      ((univ.filter (fun x : ZMod (p ^ (k + 1)) =>
        x ^ 2 = (c : ZMod (p ^ (k + 1))))).card • (1 : ℕ)) =
        ((univ.filter (fun x : ZMod (p ^ (k + 1)) =>
          x ^ 2 = (c : ZMod (p ^ (k + 1))))).card) := by
    simp
  rw [h_smul]
  exact ih

/-- For odd prime `p` and `p ∤ c`, each of the 0 or 2 roots mod `p` lifts
uniquely through all `ZMod (p^n)` by Hensel's lemma. -/
theorem cardSqrts_prime_pow_coprime (hp2 : p ≠ 2) (n : ℕ) (hn : 0 < n)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    cardSqrts (p ^ n) ((c : ℤ) : ZMod (p ^ n)) =
      if legendreSym p c = 1 then 2 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  clear hn
  induction k with
  | zero =>
    have h_equiv :
        ∀ (m : ℕ) [NeZero m] (hm : m = p),
          cardSqrts m ((c : ℤ) : ZMod m) = cardSqrts p ((c : ℤ) : ZMod p) := by
      intro m _ hm
      subst hm
      rfl
    have hp_eq : p ^ Nat.succ 0 = p := by rw [pow_succ, pow_zero, one_mul]
    rw [h_equiv (p ^ Nat.succ 0) hp_eq]
    have h_prime := cardSqrts_prime p hp2 c
    by_cases h : legendreSym p c = 1
    · rw [h] at h_prime
      rw [ite_eq_left h]
      omega
    · rw [ite_eq_right h]
      have h_c_nz : (c : ZMod p) ≠ 0 := by
        intro h0
        apply hc
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0
      rcases legendreSym.eq_one_or_neg_one p h_c_nz with h_pos | h_neg
      · exact False.elim (h h_pos)
      · simp_all
  | succ k ih =>
    exact cardSqrtsPrimePowCoprimeSucc (p := p) hp2 c hc k ih

omit hp in
/-- If `p` is prime and `p ^ (2r+1) ∣ a²`, then `p ^ (r+1) ∣ a`. -/
private lemma prime_pow_dvd_sq_imp (r : ℕ) {a : ℤ} (hpp : Prime (p : ℤ))
    (h : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2) : (p : ℤ) ^ (r + 1) ∣ a := by
  induction r generalizing a with
  | zero =>
    simp only [mul_zero, zero_add, pow_one] at h ⊢
    exact hpp.dvd_of_dvd_pow h
  | succ r ih =>
    have h_weaker : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2 :=
      dvd_trans (pow_dvd_pow _ (by omega)) h
    have h_r1 : (p : ℤ) ^ (r + 1) ∣ a := ih h_weaker
    obtain ⟨b, rfl⟩ := h_r1
    have h_pb : (p : ℤ) ∣ b ^ 2 := by
      have key : (p : ℤ) ^ (2 * r + 2) * (p : ℤ) ∣ (p : ℤ) ^ (2 * r + 2) * b ^ 2 := by
        have : (p : ℤ) ^ (2 * (r + 1) + 1) = (p : ℤ) ^ (2 * r + 2) * p := by
          rw [show 2 * (r + 1) + 1 = 2 * r + 2 + 1 from by omega, pow_succ]
        rw [this] at h
        convert h using 1; ring
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hpp.ne_zero)).mp key
    obtain ⟨c, rfl⟩ := hpp.dvd_of_dvd_pow h_pb
    rw [show (r + 1) + 1 = r + 2 from by omega, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)

omit hp2 in
/-- If the `p`-adic valuation of `c` is odd and less than `n`, then `x² ≡ c (mod p^n)`
has no solutions. -/
theorem cardSqrts_odd_val_eq_zero (n r : ℕ)
    (u : ℤ) (hr : 2 * r + 1 < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r + 1) * u : ℤ) : ZMod (p ^ n)) = 0 := by
  unfold cardSqrts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  push_cast
  intro h
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hdvd : (p : ℤ) ^ n ∣ a ^ 2 - (p : ℤ) ^ (2 * r + 1) * u := by
    have h0 : ((a ^ 2 - (p : ℤ) ^ (2 * r + 1) * u : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast; exact sub_eq_zero.mpr h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
  have h1 : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2 := by
    have hpow : (p : ℤ) ^ (2 * r + 1) ∣ (p : ℤ) ^ n := pow_dvd_pow _ (by omega)
    have hdiff := dvd_trans hpow hdvd
    have hpu : (p : ℤ) ^ (2 * r + 1) ∣ (p : ℤ) ^ (2 * r + 1) * u := dvd_mul_right _ _
    have := dvd_add hdiff hpu
    rwa [sub_add_cancel] at this
  obtain ⟨b, rfl⟩ := prime_pow_dvd_sq_imp p r hpp h1
  have key : ((p : ℤ) ^ (r + 1) * b) ^ 2 - (p : ℤ) ^ (2 * r + 1) * u =
      (p : ℤ) ^ (2 * r + 1) * ((p : ℤ) * b ^ 2 - u) := by ring
  rw [key] at hdvd
  have hpne : (p : ℤ) ^ (2 * r + 1) ≠ 0 := pow_ne_zero _ hpp.ne_zero
  have hnsplit : (p : ℤ) ^ n = (p : ℤ) ^ (2 * r + 1) * (p : ℤ) ^ (n - (2 * r + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [hnsplit, mul_dvd_mul_iff_left hpne] at hdvd
  apply hu
  have h3 : (p : ℤ) ∣ (p : ℤ) * b ^ 2 - u := by
    calc (p : ℤ) = (p : ℤ) ^ 1 := (pow_one _).symm
    _ ∣ (p : ℤ) ^ (n - (2 * r + 1)) := pow_dvd_pow _ (by omega)
    _ ∣ (p : ℤ) * b ^ 2 - u := hdvd
  have h4 := dvd_sub (dvd_mul_right (p : ℤ) (b ^ 2)) h3
  rwa [show (p : ℤ) * b ^ 2 - ((p : ℤ) * b ^ 2 - u) = u from by ring] at h4

omit hp hp2 in
/-- If `p` is prime and `p^n ∣ a²`, then `p^⌈n/2⌉ ∣ a`.
Case-split on parity of `n`: the odd case is `prime_pow_dvd_sq_imp`; the even case
`n = 2m` weakens to the odd `p ^ (2m-1) ∣ a²` case (for `m ≥ 1`). -/
private lemma prime_pow_dvd_sq_ceil {a : ℤ} (hpp : Prime (p : ℤ)) (n : ℕ)
    (h : (p : ℤ) ^ n ∣ a ^ 2) : (p : ℤ) ^ ((n + 1) / 2) ∣ a := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = m + m; ⌈n/2⌉ = m; want p^m ∣ a
    subst hm
    simp only [show (m + m + 1) / 2 = m from by omega]
    rcases m with _ | m
    · simp
    · -- n = (m+1)+(m+1); weaken to p ^ (2m+1) ∣ a² then apply imp
      exact prime_pow_dvd_sq_imp p m hpp
        (dvd_trans (pow_dvd_pow _ (by omega)) h)
  · -- n = 2*m+1; ⌈n/2⌉ = m+1; this is exactly prime_pow_dvd_sq_imp
    subst hm
    simp only [show (2 * m + 1 + 1) / 2 = m + 1 from by omega]
    exact prime_pow_dvd_sq_imp p m hpp h


omit hp2 in
private lemma cardSqrtsPrimePowEvenValDvd (n r : ℕ) (u : ℤ) (hr : 2 * r < n) :
    ∀ x : ZMod (p ^ n),
      x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) →
        (p : ZMod (p ^ n)) ^ r ∣ x := by
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  push_cast at hx
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hdvd_int : (p : ℤ) ^ n ∣ a ^ 2 - (p : ℤ) ^ (2 * r) * u := by
    have h0 : ((a ^ 2 - (p : ℤ) ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast; exact sub_eq_zero.mpr hx
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
  have h_div : (p : ℤ) ^ (2 * r) ∣ a ^ 2 := by
    have hpow : (p : ℤ) ^ (2 * r) ∣ (p : ℤ) ^ n := pow_dvd_pow _ (by omega)
    have hdiff := dvd_trans hpow hdvd_int
    have hpu : (p : ℤ) ^ (2 * r) ∣ (p : ℤ) ^ (2 * r) * u := dvd_mul_right _ _
    have := dvd_add hdiff hpu
    rwa [sub_add_cancel] at this
  obtain ⟨b, hb⟩ := prime_pow_dvd_sq_ceil p hpp (2 * r) h_div
  rw [show (2 * r + 1) / 2 = r from by omega] at hb
  simp_all

omit hp2 in
private lemma cardSqrtsPrimePowEvenValImage (n r : ℕ) (u : ℤ) (hr : 2 * r < n) :
    let S_y := univ.filter (fun y : ZMod (p ^ (n - 2 * r)) =>
      y ^ 2 = (u : ZMod (p ^ (n - 2 * r))))
    let f : ZMod (p ^ (n - 2 * r)) × ℕ → ZMod (p ^ n) :=
      fun ⟨y, k⟩ =>
        (p : ZMod (p ^ n)) ^ r * ↑(y.val) +
          ↑k * (p : ZMod (p ^ n)) ^ (n - r)
    univ.filter (fun x : ZMod (p ^ n) =>
        x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n))) =
      (S_y ×ˢ Finset.range (p ^ r)).image f := by
  classical
  dsimp only
  have hdvd := cardSqrtsPrimePowEvenValDvd (p := p) n r u hr
  set S_y := univ.filter (fun y : ZMod (p ^ (n - 2 * r)) =>
    y ^ 2 = (u : ZMod (p ^ (n - 2 * r))))
  set f : ZMod (p ^ (n - 2 * r)) × ℕ → ZMod (p ^ n) :=
    fun ⟨y, k⟩ =>
      (p : ZMod (p ^ n)) ^ r * ↑(y.val) +
        ↑k * (p : ZMod (p ^ n)) ^ (n - r)
    with hf_def
  change univ.filter (fun x : ZMod (p ^ n) =>
      x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n))) =
    (S_y ×ˢ Finset.range (p ^ r)).image f
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_product, mem_range]
  constructor
  · -- x is a solution → x is in image
    intro hx
    have hdvd_val : p ^ r ∣ x.val := by
      obtain ⟨z, hx_div⟩ := hdvd x hx
      have h_eq : x.val = (p ^ r * z.val) % p ^ n := by
        rw [hx_div]
        have : (p : ZMod (p ^ n)) ^ r = ↑(p ^ r) := by push_cast; rfl
        rw [this, ZMod.val_mul, ZMod.val_natCast]
        have h_mod : z.val = z.val % (p ^ n) := (Nat.mod_eq_of_lt z.val_lt).symm
        nth_rw 1 [h_mod]
        exact (Nat.mul_mod (p ^ r) z.val (p ^ n)).symm
      rw [h_eq]
      have h_dvd : p ^ r ∣ p ^ n := pow_dvd_pow _ (by omega)
      rw [Nat.dvd_mod_iff h_dvd]
      exact dvd_mul_right _ _
    obtain ⟨y', hy'⟩ := hdvd_val
    have hdvd_int : (p : ℤ) ^ n ∣ (x.val : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u := by
      have h0 : (((x.val : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        rw [hx]
        push_cast
        ring
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
    have h_subst : (x.val : ℤ) ^ 2 = (p : ℤ) ^ (2 * r) * (y' : ℤ) ^ 2 := by
      rw [hy']
      push_cast
      ring
    rw [h_subst] at hdvd_int
    have key : (p : ℤ) ^ (2 * r) * (y' : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u =
        (p : ℤ) ^ (2 * r) * ((y' : ℤ) ^ 2 - u) := by ring
    rw [key] at hdvd_int
    have hpne : (p : ℤ) ^ (2 * r) ≠ 0 :=
      pow_ne_zero _ (Nat.prime_iff_prime_int.mp hp.out).ne_zero
    have hnsplit : (p : ℤ) ^ n = (p : ℤ) ^ (2 * r) * (p : ℤ) ^ (n - 2 * r) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hnsplit, mul_dvd_mul_iff_left hpne] at hdvd_int
    have hy_sq : (↑y' : ZMod (p ^ (n - 2 * r))) ^ 2 = ↑u := by
      have h_eq : (((y' : ℤ) ^ 2 - u : ℤ) : ZMod (p ^ (n - 2 * r))) = 0 := by
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
      have h_eq' : (↑y' : ZMod (p ^ (n - 2 * r))) ^ 2 - ↑u = 0 := by
        push_cast at h_eq
        exact h_eq
      exact sub_eq_zero.mp h_eq'
    let y0 : ZMod (p ^ (n - 2 * r)) := ↑y'
    let k : ℕ := (y' / p ^ (n - 2 * r)) % p^r
    refine ⟨⟨y0, k⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · -- y0 in S_y
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hy_sq⟩
    · -- k in range
      exact Nat.mod_lt _ (pow_pos (Nat.Prime.pos hp.out) _)
    · -- f(y0, k) = x
      rw [hf_def]
      dsimp
      set A := p ^ (n - 2 * r)
      set B := p ^ r
      set C := p ^ (n - r)
      set D := p ^ n
      have hAB : A * B = C := by
        dsimp [A, B, C]
        rw [← pow_add]
        congr 1
        omega
      have hBC : B * C = D := by
        dsimp [B, C, D]
        rw [← pow_add]
        congr 1
        omega
      have h1 := Nat.div_add_mod y' A
      have h2 := Nat.div_add_mod (y' / A) B
      have h_subst : y' = A * (B * ((y' / A) / B) + (y' / A) % B) + y' % A := by
        nth_rw 1 [← h1]
        rw [h2]
      have h_mul :
          B * y' =
            B * A * B * ((y' / A) / B) + B * A * ((y' / A) % B) +
              B * (y' % A) := by
        have h_eq : B * y' = B * (A * (B * ((y' / A) / B) + (y' / A) % B) + y' % A) := by
          conv_rhs => rw [← h_subst]
        rw [h_eq]
        ring
      rw [mul_comm B A, hAB] at h_mul
      rw [mul_comm C B, hBC] at h_mul
      have h_zmod :
          ((B * y' : ℕ) : ZMod (p^n)) =
            ((D * ((y' / A) / B) + C * k + B * (y' % A) : ℕ) :
              ZMod (p^n)) := by
        rw [h_mul]
      have h_D : ((D * ((y' / A) / B) : ℕ) : ZMod (p^n)) = 0 := by
        dsimp [D]
        rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
      rw [Nat.cast_add, Nat.cast_add] at h_zmod
      rw [h_D, zero_add] at h_zmod
      rw [← hy'] at h_zmod
      simp only [ZMod.natCast_val] at h_zmod
      rw [ZMod.cast_id] at h_zmod
      rw [h_zmod]
      conv_lhs =>
        arg 1
        arg 2
        arg 1
        arg 1
        change (y' : ZMod A)
      rw [ZMod.val_natCast]
      dsimp [A, B, C]
      push_cast
      ring
  · -- x is in image → x is a solution
    rintro ⟨⟨y, k⟩, ⟨⟨hy_y, hy_k⟩, rfl⟩⟩
    have hy_sq' : y ^ 2 = (u : ZMod (p ^ (n - 2 * r))) := (Finset.mem_filter.mp hy_y).2
    have hdvd : (p : ℤ) ^ (n - 2 * r) ∣ (y.val : ℤ) ^ 2 - u := by
      have h0 : (((y.val : ℤ) ^ 2 - u : ℤ) : ZMod (p ^ (n - 2 * r))) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact sub_eq_zero.mpr hy_sq'
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
    obtain ⟨m, hm⟩ := hdvd
    have h_eq_int' : (y.val : ℤ) ^ 2 = u + (p : ℤ) ^ (n - 2 * r) * m := by linarith
    have :
        ((p : ZMod (p ^ n)) ^ r * ↑(y.val) +
            ↑k * (p : ZMod (p ^ n)) ^ (n - r)) ^ 2 =
        (p : ZMod (p ^ n)) ^ (2 * r) * (↑(y.val) : ZMod (p ^ n)) ^ 2 +
        2 * (p : ZMod (p ^ n)) ^ n * ↑(y.val) * ↑k +
        ↑k ^ 2 * (p : ZMod (p ^ n)) ^ (2 * n - 2 * r) := by
      have h_pow_add :
          (p : ZMod (p ^ n)) ^ r * (p : ZMod (p ^ n)) ^ (n - r) =
            (p : ZMod (p ^ n)) ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      have h_expand :
          ((p : ZMod (p ^ n)) ^ r * ↑(y.val) +
              ↑k * (p : ZMod (p ^ n)) ^ (n - r)) ^ 2 =
            (p : ZMod (p ^ n)) ^ (2 * r) * (↑(y.val) : ZMod (p ^ n)) ^ 2 +
            2 * ((p : ZMod (p ^ n)) ^ r * (p : ZMod (p ^ n)) ^ (n - r)) *
              ↑(y.val) * ↑k +
            ↑k ^ 2 * (p : ZMod (p ^ n)) ^ (2 * (n - r)) := by
        ring
      rw [h_expand, h_pow_add]
      have : 2 * (n - r) = 2 * n - 2 * r := by omega
      rw [this]
    rw [this]
    have hpn : (p : ZMod (p ^ n)) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    simp only [hpn, zero_mul, mul_zero, add_zero]
    have hp2n : (p : ZMod (p ^ n)) ^ (2 * n - 2 * r) = 0 := by
      have : 2 * n - 2 * r = n + (n - 2 * r) := by omega
      rw [this, pow_add, hpn, zero_mul]
    rw [hp2n, mul_zero, add_zero]
    have h_val_sq :
        ((y.val : ℤ) : ZMod (p^n)) ^ 2 =
          ((u + (p : ℤ) ^ (n - 2 * r) * m : ℤ) : ZMod (p^n)) := by
      rw [← h_eq_int']
      push_cast; rfl
    push_cast at h_val_sq
    rw [h_val_sq]
    have h_expand :
        (p : ZMod (p ^ n)) ^ (2 * r) *
            ((u : ZMod (p ^ n)) +
              (p : ZMod (p ^ n)) ^ (n - 2 * r) * (m : ZMod (p ^ n))) =
          (p : ZMod (p ^ n)) ^ (2 * r) * (u : ZMod (p ^ n)) +
            (p : ZMod (p ^ n)) ^ (2 * r) *
              (p : ZMod (p ^ n)) ^ (n - 2 * r) * (m : ZMod (p ^ n)) := by
      ring
    rw [h_expand]
    have h_combine :
        (p : ZMod (p ^ n)) ^ (2 * r) *
            (p : ZMod (p ^ n)) ^ (n - 2 * r) =
          (p : ZMod (p ^ n)) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [h_combine, hpn, zero_mul, add_zero]
    push_cast; rfl


/-- When `c = p^{2r} · u` with `p ∤ u` and `2r < n`, the substitution `x = p^r · y`
reduces the problem to solving `y² ≡ u (mod p^{n-2r})`. -/
theorem cardSqrts_prime_pow_even_val (hp2 : p ≠ 2) (n r : ℕ)
    (u : ℤ) (hr : 2 * r < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) =
      if legendreSym p u = 1 then 2 * p ^ r else 0 := by
  classical
  set S_y := univ.filter (fun y : ZMod (p ^ (n - 2 * r)) =>
    y ^ 2 = (u : ZMod (p ^ (n - 2 * r))))
  set f : ZMod (p ^ (n - 2 * r)) × ℕ → ZMod (p ^ n) :=
    fun ⟨y, k⟩ =>
      (p : ZMod (p ^ n)) ^ r * ↑(y.val) +
        ↑k * (p : ZMod (p ^ n)) ^ (n - r)
  have h_eq : univ.filter (fun x : ZMod (p ^ n) =>
        x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n))) =
      (S_y ×ˢ Finset.range (p ^ r)).image f := by
    simpa [S_y, f] using (cardSqrtsPrimePowEvenValImage (p := p) n r u hr)
  unfold cardSqrts
  rw [h_eq]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_range]
    have h_card_Sy :
        S_y.card = cardSqrts (p ^ (n - 2 * r))
          ((u : ℤ) : ZMod (p ^ (n - 2 * r))) := rfl
    rw [h_card_Sy]
    rw [cardSqrts_prime_pow_coprime p hp2 (n - 2 * r) (by omega) u hu]
    simp_all
  · -- f is injective on domain
    rintro ⟨y1, k1⟩ hy1 ⟨y2, k2⟩ hy2 hf_eq
    obtain ⟨hy1_y, hy1_k⟩ := Finset.mem_product.mp hy1
    obtain ⟨hy2_y, hy2_k⟩ := Finset.mem_product.mp hy2
    obtain ⟨_, hy1_sq⟩ := Finset.mem_filter.mp hy1_y
    obtain ⟨_, hy2_sq⟩ := Finset.mem_filter.mp hy2_y
    have hk1 : k1 < p ^ r := Finset.mem_range.mp hy1_k
    have hk2 : k2 < p ^ r := Finset.mem_range.mp hy2_k
    dsimp [f] at hf_eq
    have h_add1 : r + (n - 2 * r) = n - r := by omega
    have h_sub : (p ^ r - 1) * p ^ (n - r) = p ^ n - p ^ (n - r) := by
      rw [Nat.sub_mul, one_mul, ← pow_add]
      have h_add2 : r + (n - r) = n := by omega
      rw [h_add2]
    have h_le : p ^ (n - r) ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2_lt1 : p ^ r * y1.val < p ^ (n - r) := by
      have hy1_lt : y1.val < p ^ (n - 2 * r) := y1.val_lt
      have h2 := Nat.mul_lt_mul_of_pos_left hy1_lt (pow_pos (Nat.Prime.pos hp.out) r)
      rw [← pow_add, h_add1] at h2
      exact h2
    have h2_lt2 : p ^ r * y2.val < p ^ (n - r) := by
      have hy2_lt : y2.val < p ^ (n - 2 * r) := y2.val_lt
      have h2 := Nat.mul_lt_mul_of_pos_left hy2_lt (pow_pos (Nat.Prime.pos hp.out) r)
      rw [← pow_add, h_add1] at h2
      exact h2
    have h_lt1 : p ^ r * y1.val + k1 * p ^ (n - r) < p ^ n := by
      have hk1_le : k1 ≤ p ^ r - 1 := Nat.le_sub_one_of_lt hk1
      have h1 : k1 * p ^ (n - r) ≤ (p ^ r - 1) * p ^ (n - r) := Nat.mul_le_mul_right _ hk1_le
      rw [h_sub] at h1
      calc p ^ r * y1.val + k1 * p ^ (n - r)
        _ < p ^ (n - r) + k1 * p ^ (n - r) := Nat.add_lt_add_right h2_lt1 _
        _ ≤ p ^ (n - r) + (p ^ n - p ^ (n - r)) := Nat.add_le_add_left h1 _
        _ = p ^ n := Nat.add_sub_cancel' h_le
    have h_lt2 : p ^ r * y2.val + k2 * p ^ (n - r) < p ^ n := by
      have hk2_le : k2 ≤ p ^ r - 1 := Nat.le_sub_one_of_lt hk2
      have h1 : k2 * p ^ (n - r) ≤ (p ^ r - 1) * p ^ (n - r) := Nat.mul_le_mul_right _ hk2_le
      rw [h_sub] at h1
      calc p ^ r * y2.val + k2 * p ^ (n - r)
        _ < p ^ (n - r) + k2 * p ^ (n - r) := Nat.add_lt_add_right h2_lt2 _
        _ ≤ p ^ (n - r) + (p ^ n - p ^ (n - r)) := Nat.add_le_add_left h1 _
        _ = p ^ n := Nat.add_sub_cancel' h_le
    have h_eq1 :
        (↑(p ^ r * y1.val + k1 * p ^ (n - r)) : ZMod (p ^ n)) =
          ↑p ^ r * ↑y1.val + ↑k1 * ↑p ^ (n - r) := by
      simp_all
    have h_eq2 :
        (↑(p ^ r * y2.val + k2 * p ^ (n - r)) : ZMod (p ^ n)) =
          ↑p ^ r * ↑y2.val + ↑k2 * ↑p ^ (n - r) := by
      simp_all
    have h_val1 :
        (↑(p ^ r * y1.val + k1 * p ^ (n - r)) : ZMod (p ^ n)).val =
          p ^ r * y1.val + k1 * p ^ (n - r) :=
      ZMod.val_natCast_of_lt h_lt1
    have h_val2 :
        (↑(p ^ r * y2.val + k2 * p ^ (n - r)) : ZMod (p ^ n)).val =
          p ^ r * y2.val + k2 * p ^ (n - r) :=
      ZMod.val_natCast_of_lt h_lt2
    rw [← h_eq1, ← h_eq2] at hf_eq
    have hf_eq_val := congr_arg ZMod.val hf_eq
    rw [h_val1, h_val2] at hf_eq_val
    have h_mod1 : (p ^ r * y1.val + k1 * p ^ (n - r)) % p ^ (n - r) = p ^ r * y1.val := by
      rw [mul_comm k1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2_lt1]
    have h_mod2 : (p ^ r * y2.val + k2 * p ^ (n - r)) % p ^ (n - r) = p ^ r * y2.val := by
      rw [mul_comm k2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2_lt2]
    have h_mod_eq : p ^ r * y1.val = p ^ r * y2.val := by
      rw [← h_mod1, ← h_mod2, hf_eq_val]
    have hy_eq : y1.val = y2.val := by
      have hp_pos : 0 < p ^ r := pow_pos hp.out.pos r
      exact Nat.eq_of_mul_eq_mul_left hp_pos h_mod_eq
    have hy_eq' : y1 = y2 := by
      have hp_pow_pos : 0 < p ^ (n - 2 * r) := pow_pos hp.out.pos (n - 2 * r)
      have : NeZero (p ^ (n - 2 * r)) := ⟨hp_pow_pos.ne'⟩
      exact ZMod.val_injective _ hy_eq
    have hk_eq : k1 = k2 := by
      have h_subst : p ^ r * y1.val + k1 * p ^ (n - r) = p ^ r * y1.val + k2 * p ^ (n - r) := by
        simp_all
      have h_cancel := Nat.add_left_cancel h_subst
      have hp_pow_pos : 0 < p ^ (n - r) := pow_pos hp.out.pos (n - r)
      exact Nat.eq_of_mul_eq_mul_right hp_pow_pos h_cancel
    exact Prod.ext hy_eq' hk_eq


omit hp2 in
/-- When `c ≡ 0 (mod p^n)`, every multiple of `p^⌈n/2⌉` is a solution,
giving `p^⌊n/2⌋` solutions total. -/
theorem cardSqrts_zero (n : ℕ) (hn : 0 < n) :
    cardSqrts (p ^ n) (0 : ZMod (p ^ n)) = p ^ (n / 2) := by
  unfold cardSqrts
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hp_pos : 0 < p := hp.out.pos
  set k := (n + 1) / 2 with hk_def
  have hnk_add : n / 2 + k = n := by omega
  have hpk_pos : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  -- Step 1: x² = 0 in ZMod(p^n) ↔ p^k | x
  have h_iff : ∀ x : ZMod (p ^ n), x ^ 2 = 0 ↔ (p : ZMod (p ^ n)) ^ k ∣ x := by
    intro x; constructor
    · -- Forward: x² = 0 → p^k | x (via prime_pow_dvd_sq_ceil)
      intro hx
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
      have ha2 : (p : ℤ) ^ n ∣ a ^ 2 := by
        have : ((a ^ 2 : ℤ) : ZMod (p ^ n)) = 0 := by push_cast; simpa using hx
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at this
      obtain ⟨b, hb⟩ := prime_pow_dvd_sq_ceil p hpp n ha2
      rw [hb]; push_cast; exact dvd_mul_right _ _
    · -- Backward: p^k | x → x² = 0 (since (↑p)^n = 0 and 2k ≥ n)
      intro ⟨c, hc⟩
      have hp0 : (p : ZMod (p ^ n)) ^ n = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      rw [hc, mul_pow, ← pow_mul,
        show k * 2 = n + (k * 2 - n) from by omega, pow_add, hp0, zero_mul, zero_mul]
  -- Step 2: show filter = image of range(p ^ (n/2)) under i ↦ ↑(i * p^k)
  classical
  rw [show (univ.filter (fun x : ZMod (p ^ n) => x ^ 2 = 0)) =
           (univ.filter (fun x : ZMod (p ^ n) => (p : ZMod (p ^ n)) ^ k ∣ x)) from
      Finset.filter_congr fun x _ => h_iff x]
  set f : ℕ → ZMod (p ^ n) := fun i => ↑(i * p ^ k) with hf_def
  -- Injectivity of f on range(p ^ (n/2))
  have hf_inj : Set.InjOn f (Finset.range (p ^ (n / 2))) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only [hf_def] at hab
    rw [ZMod.natCast_eq_natCast_iff] at hab
    have ha' : a * p ^ k < p ^ n := by
      calc a * p ^ k < p ^ (n / 2) * p ^ k := Nat.mul_lt_mul_of_pos_right ha hpk_pos
        _ = p ^ n := by rw [← pow_add, hnk_add]
    have hb' : b * p ^ k < p ^ n := by
      calc b * p ^ k < p ^ (n / 2) * p ^ k := Nat.mul_lt_mul_of_pos_right hb hpk_pos
        _ = p ^ n := by rw [← pow_add, hnk_add]
    have := hab.eq_of_lt_of_lt ha' hb'
    exact mul_right_cancel₀ (by positivity) this
  -- The filter equals the image
  have h_eq : univ.filter (fun x : ZMod (p ^ n) => (p : ZMod (p ^ n)) ^ k ∣ x) =
      (Finset.range (p ^ (n / 2))).image f := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · -- x divisible by p^k → x in image
      intro ⟨c, hc⟩
      have hval_dvd : p ^ k ∣ x.val := by
        have hv : x.val = (p ^ k * c.val) % (p ^ n) := by
          rw [hc, ← Nat.cast_pow, ZMod.val_mul, ZMod.val_natCast]
          simp_all
        rw [hv]
        have hdvd : p ^ k ∣ p ^ n := pow_dvd_pow p (show k ≤ n by omega)
        rw [Nat.dvd_mod_iff hdvd]
        exact dvd_mul_right _ _
      obtain ⟨i, hi_eq⟩ := hval_dvd
      use i
      have hi_lt : i < p ^ (n / 2) := by
        have : p ^ k * i < p ^ k * p ^ (n / 2) := by
          calc p ^ k * i = x.val := hi_eq.symm
            _ < p ^ n := ZMod.val_lt _
            _ = p ^ (k + n / 2) := by rw [show k + n / 2 = n by omega]
            _ = p ^ k * p ^ (n / 2) := pow_add _ _ _
        exact Nat.lt_of_mul_lt_mul_left this
      refine ⟨by simpa using hi_lt, ?_⟩
      rw [hf_def]
      change (↑(i * p ^ k) : ZMod (p ^ n)) = x
      rw [mul_comm, ← hi_eq, ZMod.natCast_zmod_val]
    · -- x in image → x divisible by p^k
      intro ⟨i, hi, hix⟩
      rw [← hix]
      change (p : ZMod (p ^ n)) ^ k ∣ ↑(i * p ^ k)
      rw [show (↑(i * p ^ k) : ZMod (p ^ n)) =
        (↑i : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ k from by push_cast; ring]
      exact dvd_mul_left _ _
  rw [h_eq, Finset.card_image_of_injOn hf_inj, Finset.card_range]


end OddPrimePower

/-! ## Powers of 2 -/

section TwoPower

/-- In `ZMod 2`, squaring is the identity. -/
theorem cardSqrts_two (u : ZMod 2) : cardSqrts 2 u = 1 := by
  fin_cases u <;> decide

/-- In `ZMod 4`, for odd `u`, there are 2 roots or none. -/
theorem cardSqrts_four_odd (u : ZMod 4) (hu : u = 1 ∨ u = 3) :
    cardSqrts 4 u = if u = 1 then 2 else 0 := by
  rcases hu with rfl | rfl <;> decide

/-- In `ZMod 8`, for odd `u`, there are 4 roots or none. -/
theorem cardSqrts_eight (u : ZMod 8) (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    cardSqrts 8 u = if u = 1 then 4 else 0 := by
  rcases hu with rfl | rfl | rfl | rfl <;> decide

end TwoPower

end QuadraticOrder
