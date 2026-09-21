/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Fixed-width binary encodings of natural numbers

Big-endian, fixed-width binary encoding `Nat.toBits` with its exact decoder
`Nat.fromBits`, plus the little-endian views `Nat.toBitsLE` and
`Nat.fromBitsLE` used by local Turing-machine arithmetic. Both conventions
have exact length, truncation, round-trip, and fixed-width injectivity lemmas.
Values wider than the target width are truncated modulo `2 ^ w`.

This file lives in `Complexitylib/Mathlib/` because it extends a Mathlib
type in its home (root) namespace — the sanctioned exception to the
`Complexity` root-namespace rule. Its contents are candidates for
upstreaming to Mathlib.
-/


@[expose] public section

/-- Encode a natural number as a big-endian binary list of exactly `w` bits.
    Numbers larger than `2^w - 1` are truncated (mod 2^w). -/
def Nat.toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, val => (val / 2 ^ w % 2 == 1) :: Nat.toBits w val

theorem Nat.length_toBits : ∀ (w val : ℕ), (Nat.toBits w val).length = w
  | 0, _ => rfl
  | w + 1, val => by simp [Nat.toBits, Nat.length_toBits w]

/-- Decode a big-endian binary list to a natural number. -/
def Nat.fromBits : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 2 ^ rest.length + Nat.fromBits rest

/-- Decoded values are bounded by `2 ^ length`. -/
theorem Nat.fromBits_lt_pow_length : ∀ (l : List Bool), Nat.fromBits l < 2 ^ l.length
  | [] => by simp [Nat.fromBits]
  | b :: rest => by
    have ih := Nat.fromBits_lt_pow_length rest
    simp only [Nat.fromBits, List.length_cons, pow_succ]
    rcases b with _ | _ <;> simp <;> omega

/-- `fromBits ∘ toBits w` reduces any input modulo `2 ^ w`. -/
theorem Nat.fromBits_toBits_mod : ∀ (w val : ℕ),
    Nat.fromBits (Nat.toBits w val) = val % 2 ^ w
  | 0, val => by simp [Nat.toBits, Nat.fromBits, Nat.mod_one]
  | w + 1, val => by
    have ih := Nat.fromBits_toBits_mod w val
    simp only [Nat.toBits, Nat.fromBits, Nat.length_toBits, ih]
    have hbit : (val / 2 ^ w) % 2 = if (val / 2 ^ w % 2 == 1) then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one (val / 2 ^ w) with h | h <;> simp [h]
    have hpow : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
    have hkey : val % 2 ^ (w + 1) = (val / 2 ^ w) % 2 * 2 ^ w + val % 2 ^ w := by
      rw [hpow, Nat.mod_mul, Nat.mul_comm (2^w) _, Nat.add_comm]
    rw [hkey, ← hbit]

/-- `Nat.fromBits` is a left inverse of `Nat.toBits` on values below `2 ^ w`. -/
theorem Nat.fromBits_toBits {w val : ℕ} (hv : val < 2 ^ w) :
    Nat.fromBits (Nat.toBits w val) = val := by
  rw [Nat.fromBits_toBits_mod, Nat.mod_eq_of_lt hv]

/-- Adding a multiple of `2^w` does not change the low `w` encoded bits. -/
theorem Nat.toBits_add_pow_mul : ∀ (w val c : ℕ),
    Nat.toBits w (val + c * 2 ^ w) = Nat.toBits w val
  | 0, _, _ => rfl
  | w + 1, val, c => by
    have hrw : val + c * 2 ^ (w + 1) = val + c * 2 * 2 ^ w := by
      rw [pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc]
    have hdiv : (val + c * 2 * 2 ^ w) / 2 ^ w = val / 2 ^ w + c * 2 :=
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos w)
    simp only [hrw, Nat.toBits, hdiv, List.cons.injEq]
    constructor
    · rw [Nat.add_mul_mod_self_right]
    · exact Nat.toBits_add_pow_mul w val (c * 2)

/-- Fixed-width encoding recovers every bit list from its decoded value. -/
theorem Nat.toBits_fromBits : ∀ bits : List Bool,
    Nat.toBits bits.length (Nat.fromBits bits) = bits
  | [] => rfl
  | bit :: rest => by
    have hlt := Nat.fromBits_lt_pow_length rest
    have hval : Nat.fromBits (bit :: rest) =
        Nat.fromBits rest + (if bit then 1 else 0) * 2 ^ rest.length := by
      simp only [Nat.fromBits]
      exact Nat.add_comm _ _
    simp only [Nat.toBits, List.cons.injEq]
    constructor
    · rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
      cases bit <;> simp
    · rw [hval, Nat.toBits_add_pow_mul, Nat.toBits_fromBits rest]

/-- Decoding is injective among bit lists of the same width. -/
theorem Nat.fromBits_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Nat.fromBits first = Nat.fromBits second) : first = second := by
  have hfirst := Nat.toBits_fromBits first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Nat.toBits_fromBits second]

/-- Little-endian fixed-width bits, with the least significant bit first. -/
def Nat.toBitsLE (width value : ℕ) : List Bool :=
  (Nat.toBits width value).reverse

/-- Decode a little-endian bit list. -/
def Nat.fromBitsLE (bits : List Bool) : ℕ :=
  Nat.fromBits bits.reverse

/-- Little-endian encoding has exactly the requested width. -/
@[simp] theorem Nat.length_toBitsLE (width value : ℕ) :
    (Nat.toBitsLE width value).length = width := by
  simp [Nat.toBitsLE, Nat.length_toBits]

/-- Little-endian decoding of a fixed-width encoding truncates modulo `2^width`. -/
theorem Nat.fromBitsLE_toBitsLE_mod (width value : ℕ) :
    Nat.fromBitsLE (Nat.toBitsLE width value) = value % 2 ^ width := by
  simp [Nat.fromBitsLE, Nat.toBitsLE, Nat.fromBits_toBits_mod]

/-- Little-endian encoding exactly round-trips values that fit the width. -/
theorem Nat.fromBitsLE_toBitsLE {width value : ℕ} (hvalue : value < 2 ^ width) :
    Nat.fromBitsLE (Nat.toBitsLE width value) = value := by
  rw [Nat.fromBitsLE_toBitsLE_mod, Nat.mod_eq_of_lt hvalue]

/-- Every little-endian list is recovered at its own fixed width. -/
theorem Nat.toBitsLE_fromBitsLE (bits : List Bool) :
    Nat.toBitsLE bits.length (Nat.fromBitsLE bits) = bits := by
  unfold Nat.toBitsLE Nat.fromBitsLE
  rw [show bits.length = bits.reverse.length by simp,
    Nat.toBits_fromBits, List.reverse_reverse]

/-- A little-endian list decodes below `2` raised to its width. -/
theorem Nat.fromBitsLE_lt_pow_length (bits : List Bool) :
    Nat.fromBitsLE bits < 2 ^ bits.length := by
  unfold Nat.fromBitsLE
  simpa using Nat.fromBits_lt_pow_length bits.reverse

/-- Little-endian decoding is injective at a fixed width. -/
theorem Nat.fromBitsLE_inj_of_length_eq {first second : List Bool}
    (hlen : first.length = second.length)
    (hvalue : Nat.fromBitsLE first = Nat.fromBitsLE second) : first = second := by
  have hfirst := Nat.toBitsLE_fromBitsLE first
  rw [hvalue, hlen] at hfirst
  rw [← hfirst, Nat.toBitsLE_fromBitsLE second]

private theorem Nat.fromBits_append_singleton :
    ∀ (bits : List Bool) (bit : Bool),
      Nat.fromBits (bits ++ [bit]) =
        2 * Nat.fromBits bits + (if bit then 1 else 0)
  | [], bit => by cases bit <;> simp [Nat.fromBits]
  | first :: rest, bit => by
      rw [List.cons_append, Nat.fromBits,
        Nat.fromBits_append_singleton rest bit]
      simp only [List.length_append, List.length_singleton, pow_succ]
      cases first <;> simp [Nat.fromBits]
      omega

/-- Little-endian decoding exposes its least-significant head bit. -/
theorem Nat.fromBitsLE_cons (bit : Bool) (bits : List Bool) :
    Nat.fromBitsLE (bit :: bits) =
      (if bit then 1 else 0) + 2 * Nat.fromBitsLE bits := by
  simp only [Nat.fromBitsLE, List.reverse_cons]
  rw [Nat.fromBits_append_singleton]
  omega

/-- Decoding the canonical variable-width little-endian bits recovers the
original natural number. -/
theorem Nat.fromBitsLE_bits : ∀ value : ℕ,
    Nat.fromBitsLE value.bits = value := by
  intro value
  induction value using Nat.binaryRec' with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue,
        Nat.fromBitsLE_cons, ih]
      cases bit <;> simp [Nat.bit]
      omega

/-- The minimal fixed-width little-endian encoding is exactly the canonical
variable-width bit list. -/
theorem Nat.toBitsLE_size (value : ℕ) :
    Nat.toBitsLE value.size value = value.bits := by
  calc
    Nat.toBitsLE value.size value =
        Nat.toBitsLE value.bits.length (Nat.fromBitsLE value.bits) := by
      congr 1
      · exact (Nat.size_eq_bits_len value).symm
      · exact (Nat.fromBitsLE_bits value).symm
    _ = value.bits := Nat.toBitsLE_fromBitsLE value.bits

/-- Binary digit width is at most floor-log base two plus one. -/
theorem Nat.size_le_log_two_add_one (value : ℕ) :
    value.size ≤ Nat.log 2 value + 1 := by
  rw [Nat.size_le]
  simpa only [Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (b := 2) (by omega) value

/-- Every positive natural has binary digit width exactly floor-log base two
plus one. -/
theorem Nat.size_eq_log_two_add_one {value : ℕ} (hvalue : value ≠ 0) :
    value.size = Nat.log 2 value + 1 := by
  apply le_antisymm (Nat.size_le_log_two_add_one value)
  have hlower : Nat.log 2 value < value.size := by
    rw [Nat.lt_size]
    exact Nat.pow_log_le_self 2 hvalue
  omega
