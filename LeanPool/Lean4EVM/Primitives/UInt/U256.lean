/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.UInt.U128

/-!
# `U256`

The EVM word API: width conversions, signed interpretation, opcode arithmetic, and their laws.
-/

namespace Lean4EVM
namespace U256

/-- Constructs a `U256` by retaining the low 256 bits. -/
abbrev ofNat (n : ℕ) : U256 := FixedUInt.ofNat n
/-- Constructs a `U256` only when `n` fits in 256 bits. -/
abbrev ofNat? (n : ℕ) : Option U256 := FixedUInt.ofNat? n
/-- Constructs a `U256` with two's-complement wrapping. -/
abbrev ofInt (n : ℤ) : U256 := FixedUInt.ofInt n
/-- Constructs a `U256` only from a representable nonnegative integer. -/
abbrev ofInt? (n : ℤ) : Option U256 := FixedUInt.ofInt? n
/-- Returns the unsigned value. -/
abbrev toNat (value : U256) : ℕ := FixedUInt.toNat value
/-- Reinterprets the bits as a signed two's-complement integer. -/
abbrev toSignedInt (value : U256) : ℤ := FixedUInt.toSignedInt value
/-- Compatibility name for signed two's-complement reinterpretation. -/
abbrev toInt (value : U256) : ℤ := toSignedInt value
/-- Returns the maximum `U256`. -/
abbrev max : U256 := FixedUInt.max
/-- Returns the modulus `2 ^ 256`. -/
abbrev modulus : ℕ := FixedUInt.modulus 256

/-! ### Overflow policies

Ordinary `U256` arithmetic wraps. These re-exports give the checked, overflowing and saturating
policies the same `value.operation` spelling, so a caller states its policy without reaching into
the generic `FixedUInt` namespace.
-/

/-- Adds two values, or reports `none` when the exact sum does not fit in 256 bits. -/
abbrev checkedAdd (a b : U256) : Option U256 := FixedUInt.checkedAdd a b
/-- Subtracts two values, or reports `none` when the exact difference is negative. -/
abbrev checkedSub (a b : U256) : Option U256 := FixedUInt.checkedSub a b
/-- Multiplies two values, or reports `none` when the exact product does not fit in 256 bits. -/
abbrev checkedMul (a b : U256) : Option U256 := FixedUInt.checkedMul a b
/-- Divides two values, or reports `none` for a zero divisor. -/
abbrev checkedDiv (a b : U256) : Option U256 := FixedUInt.checkedDiv a b
/-- Computes a remainder, or reports `none` for a zero divisor. -/
abbrev checkedMod (a b : U256) : Option U256 := FixedUInt.checkedMod a b
/-- Returns quotient and remainder together, or `none` for a zero divisor. -/
abbrev checkedDivMod (a b : U256) : Option (U256 × U256) := FixedUInt.checkedDivMod a b

/-- Returns the wrapped sum together with the flag that reports the lost carry. -/
abbrev overflowingAdd (a b : U256) : U256 × Bool := FixedUInt.overflowingAdd a b
/-- Returns the wrapped difference together with the flag that reports the borrow. -/
abbrev overflowingSub (a b : U256) : U256 × Bool := FixedUInt.overflowingSub a b
/-- Returns the wrapped product together with the flag that reports the lost high bits. -/
abbrev overflowingMul (a b : U256) : U256 × Bool := FixedUInt.overflowingMul a b

/-- Adds two values, clamping an overflowing sum to the greatest U256. -/
abbrev saturatingAdd (a b : U256) : U256 := FixedUInt.saturatingAdd a b
/-- Subtracts two values, clamping an underflowing difference to zero. -/
abbrev saturatingSub (a b : U256) : U256 := FixedUInt.saturatingSub a b
/-- Multiplies two values, clamping an overflowing product to the greatest U256. -/
abbrev saturatingMul (a b : U256) : U256 := FixedUInt.saturatingMul a b

/-- Reports whether the exact sum leaves the 256-bit range. -/
abbrev addOverflow (a b : U256) : Bool := FixedUInt.addOverflow a b
/-- Reports whether the exact difference is negative. -/
abbrev subOverflow (a b : U256) : Bool := FixedUInt.subOverflow a b
/-- Reports whether the exact product leaves the 256-bit range. -/
abbrev mulOverflow (a b : U256) : Bool := FixedUInt.mulOverflow a b

/-! ### Bit inspection, rotation and rendering -/

/-- Returns bit `index` counting from the least-significant bit; bits at 256 and above are false. -/
abbrev testBit (value : U256) (index : ℕ) : Bool := FixedUInt.testBit value index
/-- Counts the zero bits above the most-significant set bit. -/
abbrev leadingZeros (value : U256) : ℕ := FixedUInt.leadingZeros value
/-- Counts the zero bits below the least-significant set bit. -/
abbrev trailingZeros (value : U256) : ℕ := FixedUInt.trailingZeros value
/-- Counts the set bits. -/
abbrev countOnes (value : U256) : ℕ := FixedUInt.countOnes value
/-- Rotates the bit pattern left, carrying the bits that leave the top back into the bottom; the
amount is taken modulo 256. -/
abbrev rotateLeft (value : U256) (amount : ℕ) : U256 := FixedUInt.rotateLeft value amount
/-- Rotates the bit pattern right, carrying the bits that leave the bottom back into the top; the
amount is taken modulo 256. -/
abbrev rotateRight (value : U256) (amount : ℕ) : U256 := FixedUInt.rotateRight value amount
/-- Renders the value as `0x` followed by exactly 64 hexadecimal digits. -/
abbrev toHex (value : U256) : String := FixedUInt.toHex value

/-- The `U256` modulus has the canonical power-of-two form. -/
@[simp]
theorem modulus_eq : U256.modulus = 2 ^ 256 :=
  rfl

/-- Natural casts into `U256` reduce modulo `2 ^ 256`. -/
@[simp]
theorem toNat_natCast (n : ℕ) : (n : U256).toNat = n % 2 ^ 256 := by
  exact FixedUInt.toNat_natCast (α := U256) (width := 256) n

/-- Numeric `U256` literals reduce modulo `2 ^ 256`. -/
@[simp]
theorem toNat_ofNat_lit (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : U256).toNat = n % 2 ^ 256 := by
  exact FixedUInt.toNat_ofNat_lit (α := U256) (width := 256) n

/-- Narrows a `U256` when its value fits in 64 bits. -/
def toU64? (value : U256) : Option U64 :=
  U64.ofNat? value.toNat

/-- Returns the low 64 bits of a `U256`. -/
def lowU64 (value : U256) : U64 :=
  U64.ofNat value.toNat

/-- Narrows a `U256` when its value fits in 128 bits. -/
def toU128? (value : U256) : Option U128 :=
  U128.ofNat? value.toNat

/-- Returns the low 128 bits of a `U256`. -/
def lowU128 (value : U256) : U128 :=
  U128.ofNat value.toNat

/-- Returns the high 128 bits of a `U256`. -/
def highU128 (value : U256) : U128 :=
  U128.ofNat (value.toNat / U128.modulus)

/-- Constructs a `U256` from its high and low 128-bit halves. -/
def fromU128s (high low : U128) : U256 :=
  ofNat (high.toNat * U128.modulus + low.toNat)

/-- Converts a Boolean to the EVM word zero or one. -/
def ofBool (value : Bool) : U256 :=
  if value then 1 else 0

/-- Tests whether an EVM word is nonzero. -/
def toBool (value : U256) : Bool :=
  decide (value ≠ 0)

/-- Tests whether an EVM word is zero. -/
def isZero (value : U256) : Bool :=
  decide (value = 0)

/-- Compares two EVM words as unsigned integers. -/
def ult (a b : U256) : Bool :=
  decide (a < b)

/-- Compares two EVM words in descending unsigned order. -/
def ugt (a b : U256) : Bool :=
  decide (a > b)

/-- Compares two EVM words as signed two's-complement integers. -/
def slt (a b : U256) : Bool :=
  decide (a.toSignedInt < b.toSignedInt)

/-- Compares two EVM words in descending signed two's-complement order. -/
def sgt (a b : U256) : Bool :=
  decide (a.toSignedInt > b.toSignedInt)

/-- Divides EVM words, returning zero for a zero divisor. -/
def div (a b : U256) : U256 :=
  if b = 0 then 0 else U256.mk (a.val / b.val)

/-- Computes EVM remainder, returning zero for a zero divisor. -/
def mod (a b : U256) : U256 :=
  if b = 0 then 0 else U256.mk (a.val % b.val)

/-- EVM unsigned division, including its zero-divisor rule. -/
instance : Div U256 where
  div := div

/-- EVM unsigned remainder, including its zero-divisor rule. -/
instance : Mod U256 where
  mod := mod

/-- Divides signed two's-complement EVM words, truncating toward zero. -/
def sdiv (a b : U256) : U256 :=
  U256.mk (a.val.sdiv b.val)

/-- Computes EVM signed remainder, whose sign follows the dividend. -/
def smod (a b : U256) : U256 :=
  if b = 0 then 0 else U256.mk (a.val.srem b.val)

/-- Computes `(a + b) % modulus` with an exact intermediate sum. -/
def addmod (a b modulus : U256) : U256 :=
  if modulus = 0 then 0 else ofNat ((a.toNat + b.toNat) % modulus.toNat)

/-- Computes `(a * b) % modulus` with an exact intermediate product. -/
def mulmod (a b modulus : U256) : U256 :=
  if modulus = 0 then 0 else ofNat ((a.toNat * b.toNat) % modulus.toNat)

/-- Raises `base` to the exponent encoded by `exponent`, modulo `2 ^ 256`. -/
def exp (base exponent : U256) : U256 :=
  FixedUInt.pow base exponent.toNat

/-- Returns the indexed byte, counting from the most-significant byte. -/
def byteAt (index value : U256) : U256 :=
  if index.toNat < 32 then
    ofNat ((value.toNat / 2 ^ (8 * (31 - index.toNat))) % 256)
  else
    0

/-- Sign-extends `value` from `byteIndex`; indices at least 32 leave it unchanged. -/
def signExtend (byteIndex value : U256) : U256 :=
  if byteIndex.toNat < 32 then
    U256.mk <| BitVec.signExtend 256 <|
      BitVec.extractLsb' 0 (8 * (byteIndex.toNat + 1)) value.val
  else
    value

/-- Shifts `value` left by the EVM word encoded in `shift`. -/
def shl (shift value : U256) : U256 :=
  value <<< shift.toNat

/-- Logically shifts `value` right by the EVM word encoded in `shift`. -/
def shr (shift value : U256) : U256 :=
  value >>> shift.toNat

/-- Arithmetically shifts `value` right by the EVM word encoded in `shift`. -/
def sar (shift value : U256) : U256 :=
  U256.mk (value.val.sshiftRight shift.toNat)

/-- Counts leading zero bits as an EVM word, as specified by `CLZ`. -/
def clz (value : U256) : U256 :=
  ofNat (FixedUInt.leadingZeros value)

/-- `EXP` agrees with natural exponentiation modulo `2 ^ 256`. -/
@[simp]
theorem toNat_exp (base exponent : U256) :
    (exp base exponent).toNat = base.toNat ^ exponent.toNat % 2 ^ 256 := by
  exact FixedUInt.toNat_pow base exponent.toNat

/-- `SHL` returns zero when the EVM shift amount is at least 256. -/
@[simp]
theorem shl_of_ge_256 (shift value : U256) (h : 256 ≤ shift.toNat) :
    shl shift value = 0 := by
  exact FixedUInt.shiftLeft_eq_zero_of_width_le value shift.toNat h

/-- In-range `SHL` agrees with natural left shift modulo `2 ^ 256`. -/
theorem toNat_shl_of_lt (shift value : U256) (h : shift.toNat < 256) :
    (shl shift value).toNat =
      (value.toNat <<< shift.toNat) % U256.modulus := by
  exact FixedUInt.toNat_shiftLeft_of_lt value shift.toNat h

/-- `SHR` returns zero when the EVM shift amount is at least 256. -/
@[simp]
theorem shr_of_ge_256 (shift value : U256) (h : 256 ≤ shift.toNat) :
    shr shift value = 0 := by
  exact FixedUInt.shiftRight_eq_zero_of_width_le value shift.toNat h

/-- `SHR` agrees with natural logical right shift. -/
@[simp]
theorem toNat_shr (shift value : U256) :
    (shr shift value).toNat = value.toNat >>> shift.toNat := by
  exact FixedUInt.toNat_shiftRight value shift.toNat

/-- `SAR` fills an oversized shift with the sign bit. -/
theorem sar_of_ge_256 (shift value : U256) (h : 256 ≤ shift.toNat) :
    sar shift value = if value.val.msb then U256.max else 0 := by
  cases hsign : value.val.msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply U256.ext
    change value.val.sshiftRight shift.toNat = 0
    rw [BitVec.sshiftRight_eq_of_msb_false hsign,
      BitVec.ushiftRight_eq_zero h]
    exact (FixedUInt.toBitVec_zero (α := U256) (width := 256)).symm
  · simp only [↓reduceIte]
    apply U256.ext
    change value.val.sshiftRight shift.toNat = BitVec.allOnes 256
    rw [BitVec.sshiftRight_eq_of_msb_true hsign,
      BitVec.ushiftRight_eq_zero h]
    simp

/-- Arithmetic right shift exposes the underlying two's-complement operation. -/
@[simp]
theorem val_sar (shift value : U256) :
    (sar shift value).val = value.val.sshiftRight shift.toNat :=
  rfl

/-- In-range `SIGNEXTEND` exposes its exact bit-vector result. -/
theorem val_signExtend_of_lt (byteIndex value : U256) (h : byteIndex.toNat < 32) :
    (signExtend byteIndex value).val =
      BitVec.signExtend 256 (BitVec.extractLsb' 0 (8 * (byteIndex.toNat + 1)) value.val) := by
  simp [signExtend, h]

/-- In-range `BYTE` has the exact EVM big-endian indexing formula. -/
theorem toNat_byteAt_of_lt (index value : U256) (h : index.toNat < 32) :
    (byteAt index value).toNat =
      (value.toNat / 2 ^ (8 * (31 - index.toNat))) % 256 := by
  simp only [byteAt, h, ↓reduceIte]
  change FixedUInt.toNat (FixedUInt.ofNat _ : U256) = _
  rw [FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-- The word returned by `CLZ` is the exact leading-zero count. -/
@[simp]
theorem toNat_clz (value : U256) :
    (clz value).toNat = FixedUInt.leadingZeros value := by
  change FixedUInt.toNat
    (FixedUInt.ofNat (FixedUInt.leadingZeros value) : U256) = _
  rw [FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (FixedUInt.leadingZeros_le_width value) (by decide)

/-- `CLZ` always returns a value at most 256. -/
theorem clz_toNat_le_256 (value : U256) : (clz value).toNat ≤ 256 := by
  rw [toNat_clz]
  exact FixedUInt.leadingZeros_le_width value

/-- Low-128-bit narrowing agrees with reduction modulo `2 ^ 128`. -/
@[simp]
theorem toNat_lowU128 (value : U256) :
    FixedUInt.toNat value.lowU128 = FixedUInt.toNat value % U128.modulus := by
  exact FixedUInt.toNat_ofNat _

/-- Low-64-bit narrowing agrees with reduction modulo `2 ^ 64`. -/
@[simp]
theorem toNat_lowU64 (value : U256) : value.lowU64.toNat = value.toNat % U64.modulus := by
  exact FixedUInt.toNat_ofNat _

/-- The high half is unsigned division by `2 ^ 128`. -/
@[simp]
theorem toNat_highU128 (value : U256) :
    FixedUInt.toNat value.highU128 = FixedUInt.toNat value / U128.modulus := by
  change FixedUInt.toNat (FixedUInt.ofNat (value.toNat / U128.modulus) : U128) = _
  rw [FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < U128.modulus)).2
  simpa [U128.modulus, U256.modulus, FixedUInt.modulus, pow_add] using
    FixedUInt.toNat_lt_modulus value

/-- Combining two 128-bit halves preserves their exact unsigned value. -/
@[simp]
theorem toNat_fromU128s (high low : U128) :
    FixedUInt.toNat (fromU128s high low) =
      FixedUInt.toNat high * U128.modulus + FixedUInt.toNat low := by
  change FixedUInt.toNat
    (FixedUInt.ofNat (high.toNat * U128.modulus + low.toNat) : U256) = _
  rw [FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  have hhigh := FixedUInt.toNat_lt_modulus high
  have hlow := FixedUInt.toNat_lt_modulus low
  have hfit : high.toNat * U128.modulus + low.toNat < U128.modulus * U128.modulus := by
    have h₁ := Nat.add_lt_add_left hlow (high.toNat * U128.modulus)
    rw [show high.toNat * U128.modulus + U128.modulus =
      (high.toNat + 1) * U128.modulus by simp [Nat.add_mul]] at h₁
    exact lt_of_lt_of_le h₁ (Nat.mul_le_mul_right U128.modulus (Nat.succ_le_of_lt hhigh))
  simpa [U128.modulus, U256.modulus, FixedUInt.modulus, pow_add] using hfit

/-- Splitting a combined word recovers its low half. -/
@[simp]
theorem lowU128_fromU128s (high low : U128) :
    lowU128 (fromU128s high low) = low := by
  apply FixedUInt.toNat_injective
  rw [toNat_lowU128, toNat_fromU128s, Nat.mul_comm (FixedUInt.toNat high) U128.modulus,
    Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (FixedUInt.toNat_lt_modulus low)

/-- Splitting a combined word recovers its high half. -/
@[simp]
theorem highU128_fromU128s (high low : U128) :
    highU128 (fromU128s high low) = high := by
  apply FixedUInt.toNat_injective
  rw [toNat_highU128, toNat_fromU128s]
  rw [Nat.mul_comm (FixedUInt.toNat high) U128.modulus]
  rw [Nat.mul_add_div (by decide : 0 < U128.modulus),
    Nat.div_eq_of_lt (FixedUInt.toNat_lt_modulus low), Nat.add_zero]

/-- Splitting and recombining a `U256` is lossless. -/
@[simp]
theorem fromU128s_highU128_lowU128 (value : U256) :
    fromU128s value.highU128 value.lowU128 = value := by
  apply FixedUInt.toNat_injective
  rw [toNat_fromU128s, toNat_highU128, toNat_lowU128]
  exact Nat.div_add_mod' value.toNat U128.modulus

/-- Checked narrowing succeeds exactly when the value fits in 128 bits. -/
@[simp]
theorem toU128?_eq_none_iff (value : U256) :
    value.toU128? = none ↔ U128.modulus ≤ value.toNat := by
  exact FixedUInt.ofNat?_eq_none_iff _

/-- Checked narrowing succeeds with the low half when the value fits. -/
theorem toU128?_eq_some_of_lt (value : U256) (h : value.toNat < U128.modulus) :
    value.toU128? = some value.lowU128 := by
  simp only [toU128?, lowU128, U128.ofNat?, FixedUInt.ofNat?]
  rw [ite_eq_left h]

/-- Checked narrowing to `U64` fails exactly for out-of-range values. -/
@[simp]
theorem toU64?_eq_none_iff (value : U256) :
    value.toU64? = none ↔ U64.modulus ≤ value.toNat := by
  exact FixedUInt.ofNat?_eq_none_iff _

/-- Checked narrowing to `U64` returns the low word when the value fits. -/
theorem toU64?_eq_some_of_lt (value : U256) (h : value.toNat < U64.modulus) :
    value.toU64? = some value.lowU64 := by
  simp only [toU64?, lowU64, U64.ofNat?, FixedUInt.ofNat?]
  rw [ite_eq_left h]

/-- Widening a `U64` to `U256` and narrowing it again is lossless. -/
@[simp]
theorem toU64?_toU256 (value : U64) : value.toU256.toU64? = some value := by
  have h : FixedUInt.toNat value.toU256 < U64.modulus := by
    rw [U64.toNat_toU256]
    exact FixedUInt.toNat_lt_modulus value
  rw [toU64?_eq_some_of_lt _ h]
  apply congrArg some
  apply FixedUInt.toNat_injective
  simp only [toNat_lowU64, U64.toNat_toU256]
  exact Nat.mod_eq_of_lt (FixedUInt.toNat_lt_modulus value)

/-- Widening a `U128` to `U256` and narrowing it again is lossless. -/
@[simp]
theorem toU128?_toU256 (value : U128) : value.toU256.toU128? = some value := by
  have h : FixedUInt.toNat value.toU256 < U128.modulus := by
    rw [U128.toNat_toU256]
    exact FixedUInt.toNat_lt_modulus value
  rw [toU128?_eq_some_of_lt _ h]
  apply congrArg some
  apply FixedUInt.toNat_injective
  simp only [U256.toNat_lowU128, U128.toNat_toU256]
  exact Nat.mod_eq_of_lt (FixedUInt.toNat_lt_modulus value)

/-- A `U64` recovered by checked narrowing widens back to the word it came from. With
`toU64?_toU256` this makes widening and checked narrowing mutually inverse. -/
theorem toU256_toU64?_eq_some {value : U256} {narrowed : U64}
    (h : value.toU64? = some narrowed) : narrowed.toU256 = value := by
  rw [toU64?, U64.ofNat?] at h
  rcases FixedUInt.ofNat?_eq_some_iff.mp h with ⟨hlt, hval⟩
  apply FixedUInt.toNat_injective
  simp only [U64.toNat_toU256, ← hval, FixedUInt.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- A `U128` recovered by checked narrowing widens back to the word it came from. With
`toU128?_toU256` this makes widening and checked narrowing mutually inverse. -/
theorem toU256_toU128?_eq_some {value : U256} {narrowed : U128}
    (h : value.toU128? = some narrowed) : narrowed.toU256 = value := by
  rw [toU128?, U128.ofNat?] at h
  rcases FixedUInt.ofNat?_eq_some_iff.mp h with ⟨hlt, hval⟩
  apply FixedUInt.toNat_injective
  simp only [U128.toNat_toU256, ← hval, FixedUInt.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- `ISZERO` is true exactly for the zero word. -/
@[simp]
theorem isZero_eq_true_iff (value : U256) : isZero value = true ↔ value = 0 := by
  simp [isZero]

/-- Boolean interpretation is false exactly for the zero word. -/
@[simp]
theorem toBool_eq_false_iff (value : U256) : toBool value = false ↔ value = 0 := by
  simp [toBool]

/-- Unsigned less-than agrees with comparison of unsigned natural values. -/
@[simp]
theorem ult_eq_true_iff (a b : U256) : ult a b = true ↔ a.toNat < b.toNat := by
  simp [ult]

/-- Unsigned greater-than agrees with comparison of unsigned natural values. -/
@[simp]
theorem ugt_eq_true_iff (a b : U256) : ugt a b = true ↔ b.toNat < a.toNat := by
  simp [ugt]

/-- Signed less-than agrees with two's-complement integer comparison. -/
@[simp]
theorem slt_eq_true_iff (a b : U256) :
    slt a b = true ↔ a.toSignedInt < b.toSignedInt := by
  simp [slt]

/-- Signed greater-than agrees with two's-complement integer comparison. -/
@[simp]
theorem sgt_eq_true_iff (a b : U256) :
    sgt a b = true ↔ b.toSignedInt < a.toSignedInt := by
  simp [sgt]

/-- EVM unsigned division agrees with natural-number division. -/
@[simp]
theorem toNat_div (a b : U256) : (a / b).toNat = a.toNat / b.toNat := by
  by_cases h : b = 0
  · subst b
    change (div a 0).toNat = a.toNat / (0 : U256).toNat
    simp [div]
  · simp only [HDiv.hDiv, Div.div, div, h, ↓reduceIte, toNat, FixedUInt.toNat]
    exact BitVec.toNat_udiv

/-- EVM unsigned division by zero returns zero. -/
@[simp]
theorem div_zero (a : U256) : a / 0 = 0 := by
  simp [HDiv.hDiv, Div.div, div]

/-- EVM unsigned remainder agrees with natural remainder away from zero. -/
theorem toNat_mod (a b : U256) :
    (a % b).toNat = if b = 0 then 0 else a.toNat % b.toNat := by
  by_cases h : b = 0
  · simp [HMod.hMod, Mod.mod, mod, h]
  · simp only [HMod.hMod, Mod.mod, mod, h, ↓reduceIte, toNat, FixedUInt.toNat]
    exact BitVec.toNat_umod

/-- EVM remainder by zero returns zero. -/
@[simp]
theorem mod_zero (a : U256) : a % 0 = 0 := by
  simp [HMod.hMod, Mod.mod, mod]

/-- Signed EVM division by zero returns zero. -/
@[simp]
theorem sdiv_zero (a : U256) : sdiv a 0 = 0 := by
  cases a with
  | mk value =>
    change U256.mk (value.sdiv 0) = U256.mk 0
    congr
    exact BitVec.sdiv_zero

/-- Signed EVM division agrees with truncating integer division, wrapped to 256 bits. -/
@[simp]
theorem toSignedInt_sdiv (a b : U256) :
    (sdiv a b).toSignedInt =
      (a.toSignedInt.tdiv b.toSignedInt).bmod U256.modulus := by
  change (a.val.sdiv b.val).toInt = (a.val.toInt.tdiv b.val.toInt).bmod (2 ^ 256)
  exact BitVec.toInt_sdiv _ _

/-- Signed EVM remainder by zero returns zero. -/
@[simp]
theorem smod_zero (a : U256) : smod a 0 = 0 := by
  simp [smod]

/-- Signed EVM remainder agrees with truncating integer remainder away from zero. -/
theorem toSignedInt_smod (a b : U256) :
    (smod a b).toSignedInt =
      if b = 0 then 0 else a.toSignedInt.tmod b.toSignedInt := by
  by_cases h : b = 0
  · simp [smod, h]
  · change (if b = 0 then 0 else U256.mk (a.val.srem b.val)).toSignedInt = _
    simp only [h, ↓reduceIte]
    exact BitVec.toInt_srem _ _

/-- Modular addition with modulus zero returns zero. -/
@[simp]
theorem addmod_zero (a b : U256) : addmod a b 0 = 0 := by
  simp [addmod]

/-- `ADDMOD` uses an exact, non-wrapping intermediate sum. -/
theorem toNat_addmod (a b modulus : U256) :
    (addmod a b modulus).toNat =
      if modulus = 0 then 0 else (a.toNat + b.toNat) % modulus.toNat := by
  by_cases h : modulus = 0
  · simp [addmod, h]
  · simp only [addmod, h, ↓reduceIte, FixedUInt.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    have hnonzero : modulus.toNat ≠ 0 := by
      intro hzero
      apply h
      apply FixedUInt.toNat_injective
      simpa using hzero
    exact lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hnonzero))
      (FixedUInt.toNat_lt_modulus modulus)

/-- Modular multiplication with modulus zero returns zero. -/
@[simp]
theorem mulmod_zero (a b : U256) : mulmod a b 0 = 0 := by
  simp [mulmod]

/-- `MULMOD` uses an exact, non-wrapping intermediate product. -/
theorem toNat_mulmod (a b modulus : U256) :
    (mulmod a b modulus).toNat =
      if modulus = 0 then 0 else (a.toNat * b.toNat) % modulus.toNat := by
  by_cases h : modulus = 0
  · simp [mulmod, h]
  · simp only [mulmod, h, ↓reduceIte, FixedUInt.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    have hnonzero : modulus.toNat ≠ 0 := by
      intro hzero
      apply h
      apply FixedUInt.toNat_injective
      simpa using hzero
    exact lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hnonzero))
      (FixedUInt.toNat_lt_modulus modulus)

/-- `BYTE` returns zero for an index outside the 32-byte EVM word. -/
@[simp]
theorem byteAt_of_index_ge (index value : U256) (h : 32 ≤ index.toNat) :
    byteAt index value = 0 := by
  simp [byteAt, Nat.not_lt.mpr h]

/-- `BYTE` always returns a single-byte value. -/
theorem byteAt_toNat_lt (index value : U256) : (byteAt index value).toNat < 256 := by
  by_cases h : index.toNat < 32
  · simp only [byteAt, h, ↓reduceIte, FixedUInt.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · exact Nat.mod_lt _ (by decide)
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide))
        (by decide)
  · simp [byteAt, h]

/-- `SIGNEXTEND` leaves a word unchanged for an out-of-range byte index. -/
@[simp]
theorem signExtend_of_index_ge (byteIndex value : U256) (h : 32 ≤ byteIndex.toNat) :
    signExtend byteIndex value = value := by
  simp [signExtend, Nat.not_lt.mpr h]

/-- `CLZ` returns 256 for the zero word. -/
@[simp]
theorem clz_zero : clz 0 = (256 : U256) := by
  apply FixedUInt.toNat_injective
  change (clz 0).toNat = (256 : U256).toNat
  rw [toNat_clz]
  simp only [FixedUInt.leadingZeros]
  have hzero : FixedUInt.toBitVec (0 : U256) = 0 := by simp
  rw [hzero]
  change ((0#256).clz).toNat = FixedUInt.toNat (256 : U256)
  have hclz : (0#256).clz = (256 : BitVec 256) :=
    BitVec.clz_eq_iff_eq_zero.mpr rfl
  rw [hclz]
  decide

end U256

end Lean4EVM
