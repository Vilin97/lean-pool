/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.UInt.U64

/-!
# `U128`

Type-owned construction, narrowing, widening multiplication, and proof API for 128-bit values.
-/

namespace Lean4EVM
namespace U128

/-- Constructs a `U128` by retaining the low 128 bits. -/
abbrev ofNat (n : ℕ) : U128 := FixedUInt.ofNat n
/-- Constructs a `U128` only when `n` fits in 128 bits. -/
abbrev ofNat? (n : ℕ) : Option U128 := FixedUInt.ofNat? n
/-- Constructs a `U128` with two's-complement wrapping. -/
abbrev ofInt (n : ℤ) : U128 := FixedUInt.ofInt n
/-- Constructs a `U128` only from a representable nonnegative integer. -/
abbrev ofInt? (n : ℤ) : Option U128 := FixedUInt.ofInt? n
/-- Returns the unsigned value. -/
abbrev toNat (value : U128) : ℕ := FixedUInt.toNat value
/-- Reinterprets the bits as a signed two's-complement integer. -/
abbrev toSignedInt (value : U128) : ℤ := FixedUInt.toSignedInt value
/-- Returns the maximum `U128`. -/
abbrev max : U128 := FixedUInt.max
/-- Returns the modulus `2 ^ 128`. -/
abbrev modulus : ℕ := FixedUInt.modulus 128

/-! ### Overflow policies

Ordinary `U128` arithmetic wraps. These re-exports give the checked, overflowing and saturating
policies the same `value.operation` spelling, so a caller states its policy without reaching into
the generic `FixedUInt` namespace.
-/

/-- Adds two values, or reports `none` when the exact sum does not fit in 128 bits. -/
abbrev checkedAdd (a b : U128) : Option U128 := FixedUInt.checkedAdd a b
/-- Subtracts two values, or reports `none` when the exact difference is negative. -/
abbrev checkedSub (a b : U128) : Option U128 := FixedUInt.checkedSub a b
/-- Multiplies two values, or reports `none` when the exact product does not fit in 128 bits. -/
abbrev checkedMul (a b : U128) : Option U128 := FixedUInt.checkedMul a b
/-- Divides two values, or reports `none` for a zero divisor. -/
abbrev checkedDiv (a b : U128) : Option U128 := FixedUInt.checkedDiv a b
/-- Computes a remainder, or reports `none` for a zero divisor. -/
abbrev checkedMod (a b : U128) : Option U128 := FixedUInt.checkedMod a b
/-- Returns quotient and remainder together, or `none` for a zero divisor. -/
abbrev checkedDivMod (a b : U128) : Option (U128 × U128) := FixedUInt.checkedDivMod a b

/-- Returns the wrapped sum together with the flag that reports the lost carry. -/
abbrev overflowingAdd (a b : U128) : U128 × Bool := FixedUInt.overflowingAdd a b
/-- Returns the wrapped difference together with the flag that reports the borrow. -/
abbrev overflowingSub (a b : U128) : U128 × Bool := FixedUInt.overflowingSub a b
/-- Returns the wrapped product together with the flag that reports the lost high bits. -/
abbrev overflowingMul (a b : U128) : U128 × Bool := FixedUInt.overflowingMul a b

/-- Adds two values, clamping an overflowing sum to the greatest U128. -/
abbrev saturatingAdd (a b : U128) : U128 := FixedUInt.saturatingAdd a b
/-- Subtracts two values, clamping an underflowing difference to zero. -/
abbrev saturatingSub (a b : U128) : U128 := FixedUInt.saturatingSub a b
/-- Multiplies two values, clamping an overflowing product to the greatest U128. -/
abbrev saturatingMul (a b : U128) : U128 := FixedUInt.saturatingMul a b

/-- Reports whether the exact sum leaves the 128-bit range. -/
abbrev addOverflow (a b : U128) : Bool := FixedUInt.addOverflow a b
/-- Reports whether the exact difference is negative. -/
abbrev subOverflow (a b : U128) : Bool := FixedUInt.subOverflow a b
/-- Reports whether the exact product leaves the 128-bit range. -/
abbrev mulOverflow (a b : U128) : Bool := FixedUInt.mulOverflow a b

/-! ### Bit inspection, rotation and rendering -/

/-- Returns bit `index` counting from the least-significant bit; bits at 128 and above are false. -/
abbrev testBit (value : U128) (index : ℕ) : Bool := FixedUInt.testBit value index
/-- Counts the zero bits above the most-significant set bit. -/
abbrev leadingZeros (value : U128) : ℕ := FixedUInt.leadingZeros value
/-- Counts the zero bits below the least-significant set bit. -/
abbrev trailingZeros (value : U128) : ℕ := FixedUInt.trailingZeros value
/-- Counts the set bits. -/
abbrev countOnes (value : U128) : ℕ := FixedUInt.countOnes value
/-- Rotates the bit pattern left, carrying the bits that leave the top back into the bottom; the
amount is taken modulo 128. -/
abbrev rotateLeft (value : U128) (amount : ℕ) : U128 := FixedUInt.rotateLeft value amount
/-- Rotates the bit pattern right, carrying the bits that leave the bottom back into the top; the
amount is taken modulo 128. -/
abbrev rotateRight (value : U128) (amount : ℕ) : U128 := FixedUInt.rotateRight value amount
/-- Renders the value as `0x` followed by exactly 32 hexadecimal digits. -/
abbrev toHex (value : U128) : String := FixedUInt.toHex value

/-- The `U128` modulus has the canonical power-of-two form. -/
@[simp]
theorem modulus_eq : U128.modulus = 2 ^ 128 :=
  rfl

/-- Natural casts into `U128` reduce modulo `2 ^ 128`. -/
@[simp]
theorem toNat_natCast (n : ℕ) : (n : U128).toNat = n % 2 ^ 128 := by
  exact FixedUInt.toNat_natCast (α := U128) (width := 128) n

/-- Numeric `U128` literals reduce modulo `2 ^ 128`. -/
@[simp]
theorem toNat_ofNat_lit (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : U128).toNat = n % 2 ^ 128 := by
  exact FixedUInt.toNat_ofNat_lit (α := U128) (width := 128) n

/-- Narrows a `U128` when its value fits in 64 bits. -/
def toU64? (value : U128) : Option U64 :=
  U64.ofNat? value.toNat

/-- Returns the low 64 bits of a `U128`. -/
def lowU64 (value : U128) : U64 :=
  U64.ofNat value.toNat

/-- Widens a `U128` to `U256` without changing its value. -/
def toU256 (value : U128) : U256 :=
  FixedUInt.ofNat value.toNat

/-- Multiplies two `U128` values exactly into a `U256`. -/
def wideningMul (a b : U128) : U256 :=
  FixedUInt.ofNat (a.toNat * b.toNat)

/-- Widening to `U256` preserves the unsigned value. -/
@[simp]
theorem toNat_toU256 (value : U128) : FixedUInt.toNat value.toU256 = value.toNat := by
  rw [toU256, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (FixedUInt.toNat_lt_modulus value) (by decide)

/-- Widening from `U128` to `U256` is injective. -/
theorem toU256_injective : Function.Injective toU256 := by
  intro a b h
  apply FixedUInt.toNat_injective
  have h' := congrArg FixedUInt.toNat h
  simpa using h'

/-- Low-64-bit narrowing agrees with reduction modulo `2 ^ 64`. -/
@[simp]
theorem toNat_lowU64 (value : U128) : value.lowU64.toNat = value.toNat % U64.modulus := by
  exact FixedUInt.toNat_ofNat _

/-- Checked narrowing to `U64` fails exactly for out-of-range values. -/
@[simp]
theorem toU64?_eq_none_iff (value : U128) :
    value.toU64? = none ↔ U64.modulus ≤ value.toNat := by
  exact FixedUInt.ofNat?_eq_none_iff _

/-- Checked narrowing to `U64` returns the low word when the value fits. -/
theorem toU64?_eq_some_of_lt (value : U128) (h : value.toNat < U64.modulus) :
    value.toU64? = some value.lowU64 := by
  simp only [toU64?, lowU64, U64.ofNat?, FixedUInt.ofNat?]
  rw [ite_eq_left h]

/-- Widening a `U64` and narrowing it again is lossless. -/
@[simp]
theorem toU64?_toU128 (value : U64) : value.toU128.toU64? = some value := by
  have h : value.toU128.toNat < U64.modulus := by
    simp only [U64.toNat_toU128]
    exact FixedUInt.toNat_lt_modulus value
  rw [toU64?_eq_some_of_lt _ h]
  apply congrArg some
  apply FixedUInt.toNat_injective
  simp only [toNat_lowU64, U64.toNat_toU128]
  exact Nat.mod_eq_of_lt (FixedUInt.toNat_lt_modulus value)

/-- A `U64` recovered by checked narrowing widens back to the value it came from. With
`toU64?_toU128` this makes widening and checked narrowing mutually inverse. -/
theorem toU128_toU64?_eq_some {value : U128} {narrowed : U64}
    (h : value.toU64? = some narrowed) : narrowed.toU128 = value := by
  rw [toU64?, U64.ofNat?] at h
  rcases FixedUInt.ofNat?_eq_some_iff.mp h with ⟨hlt, hval⟩
  apply FixedUInt.toNat_injective
  simp only [U64.toNat_toU128, ← hval, FixedUInt.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Exact widening multiplication has the natural-number product as its value. -/
@[simp]
theorem toNat_wideningMul (a b : U128) :
    FixedUInt.toNat (wideningMul a b) = a.toNat * b.toNat := by
  rw [wideningMul, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  have h := Nat.mul_lt_mul_of_lt_of_lt
    (FixedUInt.toNat_lt_modulus a) (FixedUInt.toNat_lt_modulus b)
  simpa [U128.modulus, FixedUInt.modulus, pow_add] using h

end U128

end Lean4EVM
