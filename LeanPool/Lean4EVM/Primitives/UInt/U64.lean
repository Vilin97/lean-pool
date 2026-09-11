/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.UInt.Core

/-!
# `U64`

Type-owned construction, widening, and proof API for bounded 64-bit Ethereum quantities.
-/

namespace Lean4EVM
namespace U64

/-- Constructs a `U64` by retaining the low 64 bits. -/
abbrev ofNat (n : ℕ) : U64 := FixedUInt.ofNat n
/-- Constructs a `U64` only when `n` fits in 64 bits. -/
abbrev ofNat? (n : ℕ) : Option U64 := FixedUInt.ofNat? n
/-- Constructs a `U64` with two's-complement wrapping. -/
abbrev ofInt (n : ℤ) : U64 := FixedUInt.ofInt n
/-- Constructs a `U64` only from a representable nonnegative integer. -/
abbrev ofInt? (n : ℤ) : Option U64 := FixedUInt.ofInt? n
/-- Returns the unsigned value. -/
abbrev toNat (value : U64) : ℕ := FixedUInt.toNat value
/-- Reinterprets the bits as a signed two's-complement integer. -/
abbrev toSignedInt (value : U64) : ℤ := FixedUInt.toSignedInt value
/-- Returns the maximum `U64`. -/
abbrev max : U64 := FixedUInt.max
/-- Returns the modulus `2 ^ 64`. -/
abbrev modulus : ℕ := FixedUInt.modulus 64

/-! ### Overflow policies

Ordinary `U64` arithmetic wraps. These re-exports give the checked, overflowing and saturating
policies the same `value.operation` spelling, so a caller states its policy without reaching into
the generic `FixedUInt` namespace.
-/

/-- Adds two values, or reports `none` when the exact sum does not fit in 64 bits. -/
abbrev checkedAdd (a b : U64) : Option U64 := FixedUInt.checkedAdd a b
/-- Subtracts two values, or reports `none` when the exact difference is negative. -/
abbrev checkedSub (a b : U64) : Option U64 := FixedUInt.checkedSub a b
/-- Multiplies two values, or reports `none` when the exact product does not fit in 64 bits. -/
abbrev checkedMul (a b : U64) : Option U64 := FixedUInt.checkedMul a b
/-- Divides two values, or reports `none` for a zero divisor. -/
abbrev checkedDiv (a b : U64) : Option U64 := FixedUInt.checkedDiv a b
/-- Computes a remainder, or reports `none` for a zero divisor. -/
abbrev checkedMod (a b : U64) : Option U64 := FixedUInt.checkedMod a b
/-- Returns quotient and remainder together, or `none` for a zero divisor. -/
abbrev checkedDivMod (a b : U64) : Option (U64 × U64) := FixedUInt.checkedDivMod a b

/-- Returns the wrapped sum together with the flag that reports the lost carry. -/
abbrev overflowingAdd (a b : U64) : U64 × Bool := FixedUInt.overflowingAdd a b
/-- Returns the wrapped difference together with the flag that reports the borrow. -/
abbrev overflowingSub (a b : U64) : U64 × Bool := FixedUInt.overflowingSub a b
/-- Returns the wrapped product together with the flag that reports the lost high bits. -/
abbrev overflowingMul (a b : U64) : U64 × Bool := FixedUInt.overflowingMul a b

/-- Adds two values, clamping an overflowing sum to the greatest U64. -/
abbrev saturatingAdd (a b : U64) : U64 := FixedUInt.saturatingAdd a b
/-- Subtracts two values, clamping an underflowing difference to zero. -/
abbrev saturatingSub (a b : U64) : U64 := FixedUInt.saturatingSub a b
/-- Multiplies two values, clamping an overflowing product to the greatest U64. -/
abbrev saturatingMul (a b : U64) : U64 := FixedUInt.saturatingMul a b

/-- Reports whether the exact sum leaves the 64-bit range. -/
abbrev addOverflow (a b : U64) : Bool := FixedUInt.addOverflow a b
/-- Reports whether the exact difference is negative. -/
abbrev subOverflow (a b : U64) : Bool := FixedUInt.subOverflow a b
/-- Reports whether the exact product leaves the 64-bit range. -/
abbrev mulOverflow (a b : U64) : Bool := FixedUInt.mulOverflow a b

/-! ### Bit inspection, rotation and rendering -/

/-- Returns bit `index` counting from the least-significant bit; bits at 64 and above are false. -/
abbrev testBit (value : U64) (index : ℕ) : Bool := FixedUInt.testBit value index
/-- Counts the zero bits above the most-significant set bit. -/
abbrev leadingZeros (value : U64) : ℕ := FixedUInt.leadingZeros value
/-- Counts the zero bits below the least-significant set bit. -/
abbrev trailingZeros (value : U64) : ℕ := FixedUInt.trailingZeros value
/-- Counts the set bits. -/
abbrev countOnes (value : U64) : ℕ := FixedUInt.countOnes value
/-- Rotates the bit pattern left, carrying the bits that leave the top back into the bottom; the
amount is taken modulo 64. -/
abbrev rotateLeft (value : U64) (amount : ℕ) : U64 := FixedUInt.rotateLeft value amount
/-- Rotates the bit pattern right, carrying the bits that leave the bottom back into the top; the
amount is taken modulo 64. -/
abbrev rotateRight (value : U64) (amount : ℕ) : U64 := FixedUInt.rotateRight value amount
/-- Renders the value as `0x` followed by exactly 16 hexadecimal digits. -/
abbrev toHex (value : U64) : String := FixedUInt.toHex value

/-- The `U64` modulus has the canonical power-of-two form. -/
@[simp]
theorem modulus_eq : U64.modulus = 2 ^ 64 :=
  rfl

/-- Natural casts into `U64` reduce modulo `2 ^ 64`. -/
@[simp]
theorem toNat_natCast (n : ℕ) : (n : U64).toNat = n % 2 ^ 64 := by
  exact FixedUInt.toNat_natCast (α := U64) (width := 64) n

/-- Numeric `U64` literals reduce modulo `2 ^ 64`. -/
@[simp]
theorem toNat_ofNat_lit (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : U64).toNat = n % 2 ^ 64 := by
  exact FixedUInt.toNat_ofNat_lit (α := U64) (width := 64) n

/-- Widens a `U64` to `U128` without changing its value. -/
def toU128 (value : U64) : U128 :=
  FixedUInt.ofNat value.toNat

/-- Widens a `U64` to `U256` without changing its value. -/
def toU256 (value : U64) : U256 :=
  FixedUInt.ofNat value.toNat

/-- Widening to `U128` preserves the unsigned value. -/
@[simp]
theorem toNat_toU128 (value : U64) :
    FixedUInt.toNat value.toU128 = value.toNat := by
  rw [toU128, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (FixedUInt.toNat_lt_modulus value) (by decide)

/-- Widening to `U256` preserves the unsigned value. -/
@[simp]
theorem toNat_toU256 (value : U64) :
    FixedUInt.toNat value.toU256 = value.toNat := by
  rw [toU256, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (FixedUInt.toNat_lt_modulus value) (by decide)

/-- Widening from `U64` to `U128` is injective. -/
theorem toU128_injective : Function.Injective toU128 := by
  intro a b h
  apply FixedUInt.toNat_injective
  simpa using congrArg FixedUInt.toNat h

/-- Widening from `U64` to `U256` is injective. -/
theorem toU256_injective : Function.Injective toU256 := by
  intro a b h
  apply FixedUInt.toNat_injective
  simpa using congrArg FixedUInt.toNat h

end U64

end Lean4EVM
