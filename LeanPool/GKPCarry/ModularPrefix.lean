/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.Definitions
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modular evaluation of ternary prefixes

A ternary prefix depends only on a residue modulo a power of three. The
binary-digit modular exponentiation function below lets the finite certificate
evaluate those residues without first constructing the enormous value `4 ^ m`.
-/

namespace GKPCarry

lemma count_append_replicate_zero
    {value : ℕ} (hvalue : value ≠ 0) (digits : List ℕ) (count : ℕ) :
    (digits ++ List.replicate count 0).count value = digits.count value := by
  rw [List.count_append, List.count_replicate]
  simp
  omega

/-- Taking `depth` ternary digits preserves exactly the nonzero digits of the
residue modulo `3 ^ depth`. -/
lemma count_two_take_eq_count_two_mod_pow (depth n : ℕ) :
    ((Nat.digits 3 n).take depth).count 2 =
      (Nat.digits 3 (n % 3 ^ depth)).count 2 := by
  classical
  set residue := n % 3 ^ depth with hresidue
  set quotient := n / 3 ^ depth with hquotient
  have hpow : 0 < (3 : ℕ) ^ depth := by positivity
  have hresidue_lt : residue < 3 ^ depth := Nat.mod_lt _ hpow
  have hlength : (Nat.digits 3 residue).length ≤ depth :=
    (Nat.digits_length_le_iff (b := 3) (by decide) residue).mpr hresidue_lt
  have hsplit : n = residue + 3 ^ depth * quotient := by
    rw [hresidue, hquotient]
    exact (Nat.mod_add_div n (3 ^ depth)).symm
  by_cases hquotient_zero : quotient = 0
  · have hn : n = residue := by
      rw [hsplit, hquotient_zero]
      ring_nf
    rw [hn, List.take_of_length_le hlength]
  · have hquotient_pos : 0 < quotient := Nat.pos_of_ne_zero hquotient_zero
    have hdecomp :
        Nat.digits 3 n =
          Nat.digits 3 residue ++
            List.replicate (depth - (Nat.digits 3 residue).length) 0 ++
              Nat.digits 3 quotient := by
      have hfill :
          (Nat.digits 3 residue).length +
              (depth - (Nat.digits 3 residue).length) = depth := by
        omega
      have hdigits := Nat.digits_append_zeroes_append_digits
        (b := 3) (k := depth - (Nat.digits 3 residue).length)
        (m := quotient) (n := residue) (by decide) hquotient_pos
      rw [hfill] at hdigits
      rw [hdigits, hsplit]
    have hpadded_length :
        (Nat.digits 3 residue ++
          List.replicate (depth - (Nat.digits 3 residue).length) 0).length =
            depth := by
      rw [List.length_append, List.length_replicate]
      omega
    rw [hdecomp,
      List.take_append_of_le_length hpadded_length.ge,
      List.take_of_length_le hpadded_length.le]
    exact count_append_replicate_zero (by decide) _ _

/-- The two-`2` prefix predicate can be checked on a modular residue. -/
theorem hasTwoTernaryTwosBelow_iff_mod (depth n : ℕ) :
    hasTwoTernaryTwosBelow depth n ↔
      2 ≤ (Nat.digits 3 (n % 3 ^ depth)).count 2 := by
  unfold hasTwoTernaryTwosBelow
  rw [count_two_take_eq_count_two_mod_pow depth n]

/-- Modular exponentiation over a little-endian list of binary digits. -/
def powModDigits (base modulus : ℕ) : List ℕ → ℕ
  | [] => 1 % modulus
  | digit :: digits =>
      let rest := powModDigits (base * base % modulus) modulus digits
      if digit = 0 then rest else base * rest % modulus

/-- Modular exponentiation by repeated squaring over binary exponent digits. -/
def powMod (base exponent modulus : ℕ) : ℕ :=
  powModDigits base modulus (Nat.digits 2 exponent)

theorem powModDigits_eq_pow_mod
    (base modulus : ℕ) (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < 2) :
    powModDigits base modulus digits =
      base ^ (Nat.ofDigits 2 digits) % modulus := by
  induction digits generalizing base with
  | nil => simp [powModDigits]
  | cons digit digits ih =>
      have hdigit : digit < 2 := hdigits digit (by simp)
      have htail : ∀ d ∈ digits, d < 2 := by
        intro d hd
        exact hdigits d (by simp [hd])
      have hrec := ih (base := base * base % modulus) htail
      have hsquare :
          (base * base % modulus) ^ (Nat.ofDigits 2 digits) % modulus =
            base ^ (2 * Nat.ofDigits 2 digits) % modulus := by
        rw [← Nat.pow_mod]
        congr 1
        rw [show base * base = base ^ 2 by ring, ← pow_mul]
      rcases (show digit = 0 ∨ digit = 1 by omega) with rfl | rfl
      · simp only [powModDigits, if_pos, Nat.ofDigits_cons, zero_add]
        rw [hrec, hsquare]
      · simp only [powModDigits,
          if_neg (show (1 : ℕ) ≠ 0 by decide), Nat.ofDigits_cons]
        rw [hrec, hsquare, pow_add]
        norm_num [Nat.mul_mod]

/-- `powMod` computes the ordinary power modulo `modulus`. -/
theorem powMod_eq_pow_mod (base exponent modulus : ℕ) :
    powMod base exponent modulus = base ^ exponent % modulus := by
  rw [powMod, powModDigits_eq_pow_mod]
  · rw [Nat.ofDigits_digits]
  · exact fun digit hdigit => Nat.digits_lt_base (by decide) hdigit

end GKPCarry
