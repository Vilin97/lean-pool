/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.FixedBytes.H256

/-!
# `Bytes32`

Nominal raw 32-byte values and explicit reinterpretations of hashes and EVM words.
-/

namespace Lean4EVM

/-! ## `Bytes32` -/

/-- A nominal raw 32-byte value used by Ethereum encodings and ABI data. -/
@[ext]
structure Bytes32 where
  /-- The exact 32-byte representation. -/
  bytes : FixedBytes 32
  deriving Repr, Hashable

namespace Bytes32

/-- Constructs `Bytes32` from its exact generic representation. -/
def ofFixedBytes (value : FixedBytes 32) : Bytes32 :=
  ⟨value⟩

/-- Returns the exact generic representation. -/
def toFixedBytes (value : Bytes32) : FixedBytes 32 :=
  value.bytes

/-- Constructs `Bytes32` by retaining the low 256 bits. -/
def ofNat (n : ℕ) : Bytes32 :=
  ofFixedBytes (FixedBytes.ofNat 32 n)

/-- Constructs `Bytes32` only when `n` fits in 256 bits. -/
def ofNat? (n : ℕ) : Option Bytes32 :=
  (FixedBytes.ofNat? 32 n).map ofFixedBytes

/-- Returns the unsigned natural-number value. -/
def toNat (value : Bytes32) : ℕ :=
  value.toFixedBytes.toNat

/-- Returns the exact 32-byte hexadecimal representation. -/
def toHex (value : Bytes32) : String :=
  value.toFixedBytes.toHex

/-- Returns the byte at `index` in big-endian order, or zero out of bounds. -/
def getByte (value : Bytes32) (index : ℕ) : UInt8 :=
  value.toFixedBytes.getByte index

/-- Returns bit `index`, counting from the least-significant bit. -/
def testBit (value : Bytes32) (index : ℕ) : Bool :=
  value.toFixedBytes.testBit index

/-- Parses an exact 32-byte big-endian array. -/
def ofByteArray? (bytes : ByteArray) : Option Bytes32 :=
  (FixedBytes.ofByteArray? 32 bytes).map ofFixedBytes

/-- Serializes `value` as exactly 32 big-endian bytes. -/
def toByteArray (value : Bytes32) : ByteArray :=
  value.toFixedBytes.toByteArray

/-- Returns the greatest raw 32-byte value. -/
def max : Bytes32 :=
  ofFixedBytes (FixedBytes.max 32)

/-- Reinterprets an EVM word as raw 32-byte data. -/
def ofU256 (value : U256) : Bytes32 :=
  ofFixedBytes ⟨value.val⟩

/-- Reinterprets raw 32-byte data as an EVM word. -/
def toU256 (value : Bytes32) : U256 :=
  ⟨value.toFixedBytes.val⟩

/-- Reinterprets a 256-bit hash as raw 32-byte data. -/
def ofH256 (value : H256) : Bytes32 :=
  ofFixedBytes value.toFixedBytes

/-- Reinterprets raw 32-byte data as a 256-bit hash. -/
def toH256 (value : Bytes32) : H256 :=
  H256.ofFixedBytes value.toFixedBytes

/-- Equality of generic representations identifies equal `Bytes32` values. -/
theorem toFixedBytes_injective : Function.Injective toFixedBytes := by
  intro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

/-- `Bytes32` uses unsigned big-endian numeric order. -/
instance : LinearOrder Bytes32 :=
  LinearOrder.lift' toFixedBytes toFixedBytes_injective

/-- Zero is the all-zero 32-byte value. -/
instance : Zero Bytes32 where
  zero := ofNat 0

/-- One has only the least-significant bit set. -/
instance : One Bytes32 where
  one := ofNat 1

/-- Natural casts retain the low 256 bits. -/
instance : NatCast Bytes32 where
  natCast := ofNat

/-- The default `Bytes32` is zero. -/
instance : Inhabited Bytes32 :=
  ⟨0⟩

/-- String conversion emits exact-width hexadecimal notation. -/
instance : ToString Bytes32 where
  toString := toHex

/-- Complement flips every bit of raw 32-byte data. -/
instance : Complement Bytes32 where
  complement value := ofFixedBytes (~~~value.toFixedBytes)

/-- Conjunction combines equal-position data bits. -/
instance : AndOp Bytes32 where
  and a b := ofFixedBytes (a.toFixedBytes &&& b.toFixedBytes)

/-- Disjunction combines equal-position data bits. -/
instance : OrOp Bytes32 where
  or a b := ofFixedBytes (a.toFixedBytes ||| b.toFixedBytes)

/-- Exclusive-or compares equal-position data bits. -/
instance : XorOp Bytes32 where
  xor a b := ofFixedBytes (a.toFixedBytes ^^^ b.toFixedBytes)

/-- Converting from generic bytes and back is lossless. -/
@[simp]
theorem toFixedBytes_ofFixedBytes (value : FixedBytes 32) :
    (ofFixedBytes value).toFixedBytes = value :=
  rfl

/-- Converting to generic bytes and back is lossless. -/
@[simp]
theorem ofFixedBytes_toFixedBytes (value : Bytes32) :
    ofFixedBytes value.toFixedBytes = value := by
  cases value
  rfl

/-- Equal unsigned values identify equal `Bytes32` values. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  apply toFixedBytes_injective
  exact FixedBytes.toNat_injective h

/-- Equality agrees with equality of unsigned values. -/
@[simp]
theorem toNat_inj {a b : Bytes32} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

/-- Complement is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_complement (value : Bytes32) :
    (~~~value).toFixedBytes = ~~~value.toFixedBytes :=
  rfl

/-- Conjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_and (a b : Bytes32) :
    (a &&& b).toFixedBytes = a.toFixedBytes &&& b.toFixedBytes :=
  rfl

/-- Disjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_or (a b : Bytes32) :
    (a ||| b).toFixedBytes = a.toFixedBytes ||| b.toFixedBytes :=
  rfl

/-- Exclusive-or is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_xor (a b : Bytes32) :
    (a ^^^ b).toFixedBytes = a.toFixedBytes ^^^ b.toFixedBytes :=
  rfl

/-- Bit testing agrees with the unsigned value. -/
@[simp]
theorem testBit_eq (value : Bytes32) (index : ℕ) :
    value.testBit index = value.toNat.testBit index :=
  FixedBytes.testBit_eq value.toFixedBytes index

/-- Bits at indices 256 and above are false. -/
theorem testBit_of_ge (value : Bytes32) (index : ℕ) (h : 256 ≤ index) :
    value.testBit index = false := by
  exact FixedBytes.testBit_of_bitWidth_le value.toFixedBytes index (by simpa [FixedBytes.bitWidth])

/-- Natural construction retains the low 256 bits. -/
@[simp]
theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 256 := by
  simp [toNat, ofNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Converting through a natural number is lossless. -/
@[simp]
theorem ofNat_toNat (value : Bytes32) : ofNat value.toNat = value := by
  apply toFixedBytes_injective
  simp [ofNat, toNat]

/-- Every `Bytes32` value is smaller than `2 ^ 256`. -/
theorem toNat_lt (value : Bytes32) : value.toNat < 2 ^ 256 := by
  simpa [toNat, FixedBytes.modulus, FixedBytes.bitWidth] using
    FixedBytes.toNat_lt_modulus value.toFixedBytes

/-- The greatest `Bytes32` value is `2 ^ 256 - 1`. -/
@[simp]
theorem toNat_max : max.toNat = 2 ^ 256 - 1 := by
  simp [max, toNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Unsigned order agrees with order on natural-number values. -/
@[simp]
theorem le_iff_toNat_le (a b : Bytes32) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

/-- Strict order agrees with order on natural-number values. -/
@[simp]
theorem lt_iff_toNat_lt (a b : Bytes32) : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

/-- Checked construction fails exactly outside the 256-bit range. -/
@[simp]
theorem ofNat?_eq_none_iff (n : ℕ) : ofNat? n = none ↔ 2 ^ 256 ≤ n := by
  simp [ofNat?, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Checked construction succeeds exactly for representable 256-bit values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : Bytes32} :
    ofNat? n = some value ↔ n < 2 ^ 256 ∧ ofNat n = value := by
  simp [ofNat?, ofNat, FixedBytes.ofNat?_eq_some_iff, FixedBytes.modulus,
    FixedBytes.bitWidth]

/-- Serialization always emits 32 bytes. -/
@[simp]
theorem toByteArray_size (value : Bytes32) : value.toByteArray.size = 32 := by
  simp [toByteArray]

/-- Parsing succeeds exactly for 32-byte arrays. -/
@[simp]
theorem ofByteArray?_isSome (bytes : ByteArray) :
    (ofByteArray? bytes).isSome = decide (bytes.size = 32) := by
  simp [ofByteArray?]

/-- Parsing a serialized `Bytes32` value is lossless. -/
@[simp]
theorem ofByteArray?_toByteArray (value : Bytes32) :
    ofByteArray? value.toByteArray = some value := by
  simp [ofByteArray?, toByteArray]

/-- Serializing any successfully parsed `Bytes32` input reproduces that input. -/
theorem toByteArray_ofByteArray?_eq_some {bytes : ByteArray} {value : Bytes32}
    (h : ofByteArray? bytes = some value) : value.toByteArray = bytes := by
  simp only [ofByteArray?, Option.map_eq_some_iff] at h
  rcases h with ⟨raw, hraw, rfl⟩
  exact FixedBytes.toByteArray_ofByteArray?_eq_some hraw

/-- Reinterpreting bytes as a word and back is lossless. -/
@[simp]
theorem ofU256_toU256 (value : Bytes32) : ofU256 value.toU256 = value := by
  cases value
  rfl

/-- Reinterpreting a word as bytes and back is lossless. -/
@[simp]
theorem toU256_ofU256 (value : U256) : (ofU256 value).toU256 = value :=
  rfl

/-- Word conversion preserves the unsigned value. -/
@[simp]
theorem toNat_toU256 (value : Bytes32) : value.toU256.toNat = value.toNat :=
  rfl

/-- Byte construction from a word preserves the unsigned value. -/
@[simp]
theorem toNat_ofU256 (value : U256) : (ofU256 value).toNat = value.toNat :=
  rfl

/-- Reinterpreting bytes as a hash and back is lossless. -/
@[simp]
theorem ofH256_toH256 (value : Bytes32) : ofH256 value.toH256 = value := by
  cases value
  rfl

/-- Reinterpreting a hash as bytes and back is lossless. -/
@[simp]
theorem toH256_ofH256 (value : H256) : (ofH256 value).toH256 = value := by
  cases value
  rfl

/-- Hash conversion preserves the unsigned value. -/
@[simp]
theorem toNat_toH256 (value : Bytes32) : value.toH256.toNat = value.toNat :=
  rfl

/-- Byte conversion from a hash preserves the unsigned value. -/
@[simp]
theorem toNat_ofH256 (value : H256) : (ofH256 value).toNat = value.toNat :=
  rfl

end Bytes32

end Lean4EVM
