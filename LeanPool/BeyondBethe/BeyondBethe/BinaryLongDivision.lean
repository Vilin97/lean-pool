/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
import Mathlib.Tactic

/-! # Binary Long Division -/

namespace BeyondBethe

/-!
# Binary long division

This file starts the machine-level arithmetic layer with a structural
long-division recurrence on little-endian binary words.  The recurrence uses
only doubling, comparison, and subtraction.  Its proof does not appeal to
`Nat.div` or `Nat.mod` while the recurrence is running; those operations occur
only in the extensional correctness statement.
-/

/-- The numeric value of one bit. -/
def bitValue (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitValue_false : bitValue false = 0 := rfl

@[simp] theorem bitValue_true : bitValue true = 1 := rfl

theorem bitValue_le_one (b : Bool) : bitValue b ≤ 1 := by
  cases b <;> simp [bitValue]

/-- One most-significant-to-least-significant long-division step.  The pair is
`(quotient, remainder)` for the already processed high bits. -/
def binaryLongDivStep (divisor : ℕ) (b : Bool) (qr : ℕ × ℕ) : ℕ × ℕ :=
  let trial := 2 * qr.2 + bitValue b
  if divisor = 0 then
    (0, trial)
  else if divisor ≤ trial then
    (2 * qr.1 + 1, trial - divisor)
  else
    (2 * qr.1, trial)

/-- Divide a little-endian binary word by processing its high-order tail
first. -/
def binaryLongDivBits (divisor : ℕ) : List Bool → ℕ × ℕ
  | [] => (0, 0)
  | b :: bits => binaryLongDivStep divisor b (binaryLongDivBits divisor bits)

@[simp] theorem binaryLongDivBits_nil (divisor : ℕ) :
    binaryLongDivBits divisor [] = (0, 0) := rfl

@[simp] theorem binaryLongDivBits_cons (divisor : ℕ) (b : Bool)
    (bits : List Bool) :
    binaryLongDivBits divisor (b :: bits) =
      binaryLongDivStep divisor b (binaryLongDivBits divisor bits) := rfl

/-- The zero-divisor branch follows Lean's convention: quotient zero and the
entire input as remainder. -/
theorem binaryLongDivBits_zero (bits : List Bool) :
    binaryLongDivBits 0 bits = (0, Nat.fromBitsLE bits) := by
  induction bits with
  | nil =>
      change (0, 0) = (0, 0)
      rfl
  | cons b bits ih =>
      simp [binaryLongDivBits, binaryLongDivStep, ih,
        Nat.fromBitsLE_cons, bitValue, Nat.add_comm]

/-- Algebraic preservation performed by one positive-divisor step. -/
theorem binaryLongDivStep_invariant {divisor : ℕ} (hdivisor : 0 < divisor)
    (b : Bool) (q r : ℕ) (hr : r < divisor) :
    let out := binaryLongDivStep divisor b (q, r)
    2 * (q * divisor + r) + bitValue b =
        out.1 * divisor + out.2 ∧
      out.2 < divisor := by
  have htrial : 2 * r + bitValue b < 2 * divisor := by
    have hb := bitValue_le_one b
    omega
  rw [binaryLongDivStep]
  simp only [Prod.fst, Prod.snd]
  split
  · rename_i hzero
    omega
  · split
    · rename_i hle
      constructor
      · have hcancel : divisor + (2 * r + bitValue b - divisor) =
            2 * r + bitValue b := Nat.add_sub_of_le hle
        calc
          2 * (q * divisor + r) + bitValue b =
              2 * (q * divisor) + (2 * r + bitValue b) := by ring
          _ = 2 * (q * divisor) +
              (divisor + (2 * r + bitValue b - divisor)) := by rw [hcancel]
          _ = (2 * q + 1) * divisor +
              (2 * r + bitValue b - divisor) := by ring
      · omega
    · rename_i hnle
      constructor
      · ring
      · omega

/-- Fundamental invariant of the recurrence for a positive divisor. -/
theorem binaryLongDivBits_invariant {divisor : ℕ} (hdivisor : 0 < divisor) :
    ∀ bits : List Bool,
      let qr := binaryLongDivBits divisor bits
      Nat.fromBitsLE bits = qr.1 * divisor + qr.2 ∧ qr.2 < divisor := by
  intro bits
  induction bits with
  | nil =>
      simp [binaryLongDivBits, Nat.fromBitsLE, Nat.fromBits, hdivisor]
  | cons b bits ih =>
      let q := (binaryLongDivBits divisor bits).1
      let r := (binaryLongDivBits divisor bits).2
      have ihEq : Nat.fromBitsLE bits = q * divisor + r := by
        simpa only [q, r] using ih.1
      have ihRem : r < divisor := by
        simpa only [r] using ih.2
      have hstep := binaryLongDivStep_invariant hdivisor b q r ihRem
      rw [Nat.fromBitsLE_cons, binaryLongDivBits_cons]
      simpa only [bitValue, q, r, ihEq, add_comm] using hstep

/-- Extensional correctness of binary long division. -/
theorem binaryLongDivBits_eq_div_mod (divisor : ℕ) (bits : List Bool) :
    binaryLongDivBits divisor bits =
      (Nat.fromBitsLE bits / divisor, Nat.fromBitsLE bits % divisor) := by
  by_cases hzero : divisor = 0
  · subst divisor
    simpa using binaryLongDivBits_zero bits
  · have hpos : 0 < divisor := Nat.pos_of_ne_zero hzero
    let q := (binaryLongDivBits divisor bits).1
    let r := (binaryLongDivBits divisor bits).2
    have hinv := binaryLongDivBits_invariant hpos bits
    have hinvEq : Nat.fromBitsLE bits = q * divisor + r := by
      simpa only [q, r] using hinv.1
    have hinvRem : r < divisor := by
      simpa only [r] using hinv.2
    have hquot : Nat.fromBitsLE bits / divisor = q := by
      apply Nat.div_eq_of_lt_le
      · rw [hinvEq]
        omega
      · rw [hinvEq]
        calc
          q * divisor + r < q * divisor + divisor :=
            Nat.add_lt_add_left hinvRem _
          _ = (q + 1) * divisor := by ring
    have hrem : Nat.fromBitsLE bits % divisor = r := by
      rw [hinvEq, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hinvRem]
    apply Prod.ext
    · simpa only [q] using hquot.symm
    · simpa only [r] using hrem.symm

/-- Natural-number wrapper using Lean's canonical little-endian bits. -/
def binaryLongDiv (dividend divisor : ℕ) : ℕ × ℕ :=
  binaryLongDivBits divisor dividend.bits

theorem binaryLongDiv_eq_div_mod (dividend divisor : ℕ) :
    binaryLongDiv dividend divisor =
      (dividend / divisor, dividend % divisor) := by
  rw [binaryLongDiv, binaryLongDivBits_eq_div_mod,
    Nat.fromBitsLE_bits]

theorem binaryLongDiv_remainder_lt {dividend divisor : ℕ}
    (hdivisor : 0 < divisor) :
    (binaryLongDiv dividend divisor).2 < divisor := by
  rw [binaryLongDiv_eq_div_mod]
  exact Nat.mod_lt _ hdivisor

theorem binaryLongDivBits_quotient_le_value (divisor : ℕ)
    (bits : List Bool) :
    (binaryLongDivBits divisor bits).1 ≤ Nat.fromBitsLE bits := by
  rw [binaryLongDivBits_eq_div_mod]
  exact Nat.div_le_self _ _

theorem binaryLongDivBits_remainder_le_value (divisor : ℕ)
    (bits : List Bool) :
    (binaryLongDivBits divisor bits).2 ≤ Nat.fromBitsLE bits := by
  rw [binaryLongDivBits_eq_div_mod]
  exact Nat.mod_le _ _

/-- Both result registers fit in the input word width. -/
theorem binaryLongDivBits_components_lt_width (divisor : ℕ)
    (bits : List Bool) :
    (binaryLongDivBits divisor bits).1 < 2 ^ bits.length ∧
      (binaryLongDivBits divisor bits).2 < 2 ^ bits.length := by
  have hvalue := Nat.fromBitsLE_lt_pow_length bits
  exact ⟨(binaryLongDivBits_quotient_le_value divisor bits).trans_lt hvalue,
    (binaryLongDivBits_remainder_le_value divisor bits).trans_lt hvalue⟩

/-- Euclid's algorithm with its remainder supplied by the verified binary
division recurrence. -/
def binaryEuclid (a : ℕ) : ℕ → ℕ
  | 0 => a
  | b + 1 =>
      binaryEuclid (b + 1) (binaryLongDiv a (b + 1)).2
termination_by b => b
decreasing_by
  exact binaryLongDiv_remainder_lt (by omega)

theorem binaryEuclid_eq_gcd : ∀ a b : ℕ,
    binaryEuclid a b = Nat.gcd a b := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero => simp [binaryEuclid]
      | succ b =>
          have hrem : a % (b + 1) < b + 1 := Nat.mod_lt _ (by omega)
          rw [binaryEuclid, binaryLongDiv_eq_div_mod]
          simp only [Prod.snd]
          rw [ih (a % (b + 1)) hrem]
          calc
            Nat.gcd (b + 1) (a % (b + 1)) =
                Nat.gcd (a % (b + 1)) (b + 1) := Nat.gcd_comm _ _
            _ = Nat.gcd (b + 1) a := (Nat.gcd_rec (b + 1) a).symm
            _ = Nat.gcd a (b + 1) := Nat.gcd_comm _ _

/-- One total Euclid step.  Once the second register is zero it is a no-op. -/
def binaryEuclidStep (state : ℕ × ℕ) : ℕ × ℕ :=
  if state.2 = 0 then state
  else (state.2, (binaryLongDiv state.1 state.2).2)

theorem binaryEuclidStep_eq (a b : ℕ) :
    binaryEuclidStep (a, b) =
      if b = 0 then (a, b) else (b, a % b) := by
  simp [binaryEuclidStep, binaryLongDiv_eq_div_mod]

theorem binaryEuclidStep_zero (a : ℕ) :
    binaryEuclidStep (a, 0) = (a, 0) := by
  simp [binaryEuclidStep]

/-- For `0 < r < b`, the next Euclidean remainder is at most half of
`b`. -/
theorem mod_le_half_of_pos_of_lt {b r : ℕ} (hr0 : 0 < r) (hrb : r < b) :
    b % r ≤ b / 2 := by
  by_cases hrhalf : r ≤ b / 2
  · exact (Nat.mod_lt b hr0).le.trans hrhalf
  · have hbr : r ≤ b := hrb.le
    rw [Nat.mod_eq_sub_mod hbr, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Irrespective of the first register, two Euclid steps halve the second
register. -/
theorem binaryEuclidStep_two_snd_le_half (a b : ℕ) :
    ((binaryEuclidStep^[2]) (a, b)).2 ≤ b / 2 := by
  by_cases hb : b = 0
  · subst b
    simp [Function.iterate_succ_apply, binaryEuclidStep_zero]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    let r := a % b
    have hrb : r < b := by
      dsimp only [r]
      exact Nat.mod_lt _ hbpos
    have hfirst : binaryEuclidStep (a, b) = (b, r) := by
      rw [binaryEuclidStep_eq, if_neg hb]
    rw [show (binaryEuclidStep^[2]) (a, b) =
        binaryEuclidStep (binaryEuclidStep (a, b)) by rfl, hfirst]
    by_cases hr : r = 0
    · rw [hr, binaryEuclidStep_zero]
      simp
    · rw [binaryEuclidStep_eq, if_neg hr]
      simp only [Prod.snd]
      exact mod_le_half_of_pos_of_lt (Nat.pos_of_ne_zero hr) hrb

/-- Fixed-budget Euclid loop. -/
def binaryEuclidIterate (steps : ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  (binaryEuclidStep^[steps]) state

theorem binaryEuclidIterate_zero (steps a : ℕ) :
    binaryEuclidIterate steps (a, 0) = (a, 0) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [binaryEuclidIterate, Function.iterate_succ_apply,
        binaryEuclidStep_zero]
      simpa only [binaryEuclidIterate] using ih

/-- Two steps per available input bit suffice to reach remainder zero. -/
theorem binaryEuclidIterate_snd_eq_zero_of_lt_pow :
    ∀ k a b : ℕ, b < 2 ^ k →
      (binaryEuclidIterate (2 * k) (a, b)).2 = 0 := by
  intro k
  induction k with
  | zero =>
      intro a b hb
      have : b = 0 := by simpa using hb
      subst b
      simp [binaryEuclidIterate]
  | succ k ih =>
      intro a b hb
      by_cases hb0 : b = 0
      · subst b
        simp [binaryEuclidIterate_zero]
      · let afterTwo := (binaryEuclidStep^[2]) (a, b)
        have hhalf := binaryEuclidStep_two_snd_le_half a b
        have hbhalf : b / 2 < 2 ^ k := by
          rw [pow_succ] at hb
          omega
        have hafter : afterTwo.2 < 2 ^ k := by
          exact hhalf.trans_lt hbhalf
        have htail := ih afterTwo.1 afterTwo.2 hafter
        rw [binaryEuclidIterate] at htail ⊢
        rw [show 2 * (k + 1) = 2 * k + 2 by omega,
          Function.iterate_add_apply]
        exact htail

theorem binaryEuclidStep_gcd (state : ℕ × ℕ) :
    Nat.gcd (binaryEuclidStep state).1 (binaryEuclidStep state).2 =
      Nat.gcd state.1 state.2 := by
  rcases state with ⟨a, b⟩
  rw [binaryEuclidStep_eq]
  split
  · rfl
  · simp only [Prod.fst, Prod.snd]
    calc
      Nat.gcd b (a % b) = Nat.gcd (a % b) b := Nat.gcd_comm _ _
      _ = Nat.gcd b a := (Nat.gcd_rec b a).symm
      _ = Nat.gcd a b := Nat.gcd_comm _ _

theorem binaryEuclidIterate_gcd (steps : ℕ) (state : ℕ × ℕ) :
    Nat.gcd (binaryEuclidIterate steps state).1
        (binaryEuclidIterate steps state).2 =
      Nat.gcd state.1 state.2 := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      rw [binaryEuclidIterate, Function.iterate_succ_apply]
      change Nat.gcd
          (binaryEuclidIterate steps (binaryEuclidStep state)).1
          (binaryEuclidIterate steps (binaryEuclidStep state)).2 = _
      rw [ih, binaryEuclidStep_gcd]

/-- Machine-facing gcd: a fixed `2 * bitlength` loop rather than an
unbounded semantic recursion. -/
def binaryEuclidBounded (a b : ℕ) : ℕ :=
  (binaryEuclidIterate (2 * b.size) (a, b)).1

theorem binaryEuclidBounded_eq_gcd (a b : ℕ) :
    binaryEuclidBounded a b = Nat.gcd a b := by
  have hb : b < 2 ^ b.size := Nat.lt_size_self b
  have hzero := binaryEuclidIterate_snd_eq_zero_of_lt_pow b.size a b hb
  have hgcd := binaryEuclidIterate_gcd (2 * b.size) (a, b)
  rw [hzero, Nat.gcd_zero_right] at hgcd
  exact hgcd

end BeyondBethe
