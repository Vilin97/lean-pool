/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.FixedBytes.Core

/-!
# `H160`

Nominal 160-bit hash values with exact-size serialization and type-owned laws.
-/

namespace Lean4EVM

/-! ## `H160` -/

/-- A nominal 160-bit hash value. It is not definitionally an address. -/
@[ext]
structure H160 where
  /-- The exact 20-byte representation. -/
  bytes : FixedBytes 20
  deriving Repr, Hashable

namespace H160

/-- Constructs `H160` from its exact generic representation. -/
def ofFixedBytes (value : FixedBytes 20) : H160 :=
  ⟨value⟩

/-- Returns the exact generic representation. -/
def toFixedBytes (value : H160) : FixedBytes 20 :=
  value.bytes

/-- Constructs `H160` by retaining the low 160 bits. -/
def ofNat (n : ℕ) : H160 :=
  ofFixedBytes (FixedBytes.ofNat 20 n)

/-- Constructs `H160` only when `n` fits in 160 bits. -/
def ofNat? (n : ℕ) : Option H160 :=
  (FixedBytes.ofNat? 20 n).map ofFixedBytes

/-- Returns the unsigned natural-number value. -/
def toNat (value : H160) : ℕ :=
  value.toFixedBytes.toNat

/-- Returns the exact 20-byte hexadecimal representation. -/
def toHex (value : H160) : String :=
  value.toFixedBytes.toHex

/-- Returns the byte at `index` in big-endian order, or zero out of bounds. -/
def getByte (value : H160) (index : ℕ) : UInt8 :=
  value.toFixedBytes.getByte index

/-- Returns bit `index`, counting from the least-significant bit. -/
def testBit (value : H160) (index : ℕ) : Bool :=
  value.toFixedBytes.testBit index

/-- Parses an exact 20-byte big-endian array. -/
def ofByteArray? (bytes : ByteArray) : Option H160 :=
  (FixedBytes.ofByteArray? 20 bytes).map ofFixedBytes

/-- Serializes `value` as exactly 20 big-endian bytes. -/
def toByteArray (value : H160) : ByteArray :=
  value.toFixedBytes.toByteArray

/-- Returns the greatest 160-bit hash value. -/
def max : H160 :=
  ofFixedBytes (FixedBytes.max 20)

/-- Equality of generic representations identifies equal `H160` values. -/
theorem toFixedBytes_injective : Function.Injective toFixedBytes := by
  intro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

/-- `H160` uses unsigned big-endian numeric order. -/
instance : LinearOrder H160 :=
  LinearOrder.lift' toFixedBytes toFixedBytes_injective

/-- Zero is the all-zero 160-bit hash. -/
instance : Zero H160 where
  zero := ofNat 0

/-- One has only the least-significant bit set. -/
instance : One H160 where
  one := ofNat 1

/-- Natural casts retain the low 160 bits. -/
instance : NatCast H160 where
  natCast := ofNat

/-- The default `H160` is zero. -/
instance : Inhabited H160 :=
  ⟨0⟩

/-- String conversion emits exact-width hexadecimal notation. -/
instance : ToString H160 where
  toString := toHex

/-- Complement flips every bit of a 160-bit hash. -/
instance : Complement H160 where
  complement value := ofFixedBytes (~~~value.toFixedBytes)

/-- Conjunction combines equal-position hash bits. -/
instance : AndOp H160 where
  and a b := ofFixedBytes (a.toFixedBytes &&& b.toFixedBytes)

/-- Disjunction combines equal-position hash bits. -/
instance : OrOp H160 where
  or a b := ofFixedBytes (a.toFixedBytes ||| b.toFixedBytes)

/-- Exclusive-or compares equal-position hash bits. -/
instance : XorOp H160 where
  xor a b := ofFixedBytes (a.toFixedBytes ^^^ b.toFixedBytes)

/-- Converting from generic bytes and back is lossless. -/
@[simp]
theorem toFixedBytes_ofFixedBytes (value : FixedBytes 20) :
    (ofFixedBytes value).toFixedBytes = value :=
  rfl

/-- Converting to generic bytes and back is lossless. -/
@[simp]
theorem ofFixedBytes_toFixedBytes (value : H160) :
    ofFixedBytes value.toFixedBytes = value := by
  cases value
  rfl

/-- Equal unsigned values identify equal `H160` values. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  apply toFixedBytes_injective
  exact FixedBytes.toNat_injective h

/-- Equality agrees with equality of unsigned values. -/
@[simp]
theorem toNat_inj {a b : H160} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

/-- Complement is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_complement (value : H160) :
    (~~~value).toFixedBytes = ~~~value.toFixedBytes :=
  rfl

/-- Conjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_and (a b : H160) :
    (a &&& b).toFixedBytes = a.toFixedBytes &&& b.toFixedBytes :=
  rfl

/-- Disjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_or (a b : H160) :
    (a ||| b).toFixedBytes = a.toFixedBytes ||| b.toFixedBytes :=
  rfl

/-- Exclusive-or is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_xor (a b : H160) :
    (a ^^^ b).toFixedBytes = a.toFixedBytes ^^^ b.toFixedBytes :=
  rfl

/-- Bit testing agrees with the unsigned value. -/
@[simp]
theorem testBit_eq (value : H160) (index : ℕ) :
    value.testBit index = value.toNat.testBit index :=
  FixedBytes.testBit_eq value.toFixedBytes index

/-- Bits at indices 160 and above are false. -/
theorem testBit_of_ge (value : H160) (index : ℕ) (h : 160 ≤ index) :
    value.testBit index = false := by
  exact FixedBytes.testBit_of_bitWidth_le value.toFixedBytes index (by simpa [FixedBytes.bitWidth])

/-- Natural construction retains the low 160 bits. -/
@[simp]
theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 160 := by
  simp [toNat, ofNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Converting through a natural number is lossless. -/
@[simp]
theorem ofNat_toNat (value : H160) : ofNat value.toNat = value := by
  apply toFixedBytes_injective
  simp [ofNat, toNat]

/-- Every `H160` value is smaller than `2 ^ 160`. -/
theorem toNat_lt (value : H160) : value.toNat < 2 ^ 160 := by
  simpa [toNat, FixedBytes.modulus, FixedBytes.bitWidth] using
    FixedBytes.toNat_lt_modulus value.toFixedBytes

/-- The greatest `H160` value is `2 ^ 160 - 1`. -/
@[simp]
theorem toNat_max : max.toNat = 2 ^ 160 - 1 := by
  simp [max, toNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Unsigned order agrees with order on natural-number values. -/
@[simp]
theorem le_iff_toNat_le (a b : H160) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

/-- Strict order agrees with order on natural-number values. -/
@[simp]
theorem lt_iff_toNat_lt (a b : H160) : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

/-- Checked construction fails exactly outside the 160-bit range. -/
@[simp]
theorem ofNat?_eq_none_iff (n : ℕ) : ofNat? n = none ↔ 2 ^ 160 ≤ n := by
  simp [ofNat?, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Checked construction succeeds exactly for representable 160-bit values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : H160} :
    ofNat? n = some value ↔ n < 2 ^ 160 ∧ ofNat n = value := by
  simp [ofNat?, ofNat, FixedBytes.ofNat?_eq_some_iff, FixedBytes.modulus,
    FixedBytes.bitWidth]

/-- Serialization always emits 20 bytes. -/
@[simp]
theorem toByteArray_size (value : H160) : value.toByteArray.size = 20 := by
  simp [toByteArray]

/-- Parsing succeeds exactly for 20-byte arrays. -/
@[simp]
theorem ofByteArray?_isSome (bytes : ByteArray) :
    (ofByteArray? bytes).isSome = decide (bytes.size = 20) := by
  simp [ofByteArray?]

/-- Parsing a serialized `H160` value is lossless. -/
@[simp]
theorem ofByteArray?_toByteArray (value : H160) :
    ofByteArray? value.toByteArray = some value := by
  simp [ofByteArray?, toByteArray]

/-- Serializing any successfully parsed `H160` input reproduces that input. -/
theorem toByteArray_ofByteArray?_eq_some {bytes : ByteArray} {value : H160}
    (h : ofByteArray? bytes = some value) : value.toByteArray = bytes := by
  simp only [ofByteArray?, Option.map_eq_some_iff] at h
  rcases h with ⟨raw, hraw, rfl⟩
  exact FixedBytes.toByteArray_ofByteArray?_eq_some hraw

end H160

end Lean4EVM
