/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.FixedBytes.H160
import LeanPool.Lean4EVM.Primitives.UInt.U256

/-!
# `Address`

Nominal 20-byte Ethereum addresses, exact serialization, and explicit EVM-word conversions.
-/

namespace Lean4EVM

/-! ## `Address` -/

/-- A nominal 20-byte Ethereum account or contract address. -/
@[ext]
structure Address where
  /-- The exact 20-byte address payload. -/
  bytes : FixedBytes 20
  deriving Repr, Hashable

namespace Address

/-- Constructs an address from its exact generic representation. -/
def ofFixedBytes (value : FixedBytes 20) : Address :=
  ⟨value⟩

/-- Returns the exact generic representation. -/
def toFixedBytes (value : Address) : FixedBytes 20 :=
  value.bytes

/-- Constructs an address by retaining the low 160 bits. -/
def ofNat (n : ℕ) : Address :=
  ofFixedBytes (FixedBytes.ofNat 20 n)

/-- Constructs an address only when `n` fits in 160 bits. -/
def ofNat? (n : ℕ) : Option Address :=
  (FixedBytes.ofNat? 20 n).map ofFixedBytes

/-- Returns the unsigned 160-bit address value. -/
def toNat (value : Address) : ℕ :=
  value.toFixedBytes.toNat

/-- Returns the exact lowercase 20-byte hexadecimal payload. -/
def toHex (value : Address) : String :=
  value.toFixedBytes.toHex

/-- Returns the address byte at `index` in big-endian order, or zero out of bounds. -/
def getByte (value : Address) (index : ℕ) : UInt8 :=
  value.toFixedBytes.getByte index

/-- Returns address bit `index`, counting from the least-significant bit. -/
def testBit (value : Address) (index : ℕ) : Bool :=
  value.toFixedBytes.testBit index

/-- Parses an exact 20-byte big-endian address payload. -/
def ofByteArray? (bytes : ByteArray) : Option Address :=
  (FixedBytes.ofByteArray? 20 bytes).map ofFixedBytes

/-- Serializes the address as exactly 20 big-endian bytes. -/
def toByteArray (value : Address) : ByteArray :=
  value.toFixedBytes.toByteArray

/-- Returns the greatest 160-bit address payload. -/
def max : Address :=
  ofFixedBytes (FixedBytes.max 20)

/-- Converts a 160-bit hash payload to a nominal address. -/
def ofH160 (value : H160) : Address :=
  ofFixedBytes value.toFixedBytes

/-- Converts an address payload to a nominal 160-bit hash. -/
def toH160 (value : Address) : H160 :=
  H160.ofFixedBytes value.toFixedBytes

/-- Extracts the low 160 bits of an EVM word as an address. -/
def ofU256 (value : U256) : Address :=
  ofNat value.toNat

/-- Converts an EVM word to an address only when its high 96 bits are zero. -/
def ofU256? (value : U256) : Option Address :=
  ofNat? value.toNat

/-- Zero-extends an address to an EVM word. -/
def toU256 (value : Address) : U256 :=
  U256.ofNat value.toNat

/-- Equality of generic representations identifies equal addresses. -/
theorem toFixedBytes_injective : Function.Injective toFixedBytes := by
  intro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

/-- Addresses use unsigned big-endian numeric order. -/
instance : LinearOrder Address :=
  LinearOrder.lift' toFixedBytes toFixedBytes_injective

/-- Zero is the all-zero address. -/
instance : Zero Address where
  zero := ofNat 0

/-- One has only the least-significant address bit set. -/
instance : One Address where
  one := ofNat 1

/-- Natural casts retain the low 160 bits. -/
instance : NatCast Address where
  natCast := ofNat

/-- The default address is zero. -/
instance : Inhabited Address :=
  ⟨0⟩

/-- String conversion emits the raw exact-width hexadecimal payload. -/
instance : ToString Address where
  toString := toHex

/-- Converting from generic bytes and back is lossless. -/
@[simp]
theorem toFixedBytes_ofFixedBytes (value : FixedBytes 20) :
    (ofFixedBytes value).toFixedBytes = value :=
  rfl

/-- Converting to generic bytes and back is lossless. -/
@[simp]
theorem ofFixedBytes_toFixedBytes (value : Address) :
    ofFixedBytes value.toFixedBytes = value := by
  cases value
  rfl

/-- Equal unsigned values identify equal addresses. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  apply toFixedBytes_injective
  exact FixedBytes.toNat_injective h

/-- Equality agrees with equality of unsigned address values. -/
@[simp]
theorem toNat_inj {a b : Address} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

/-- Bit testing agrees with the unsigned address value. -/
@[simp]
theorem testBit_eq (value : Address) (index : ℕ) :
    value.testBit index = value.toNat.testBit index :=
  FixedBytes.testBit_eq value.toFixedBytes index

/-- Address bits at indices 160 and above are false. -/
theorem testBit_of_ge (value : Address) (index : ℕ) (h : 160 ≤ index) :
    value.testBit index = false := by
  exact FixedBytes.testBit_of_bitWidth_le value.toFixedBytes index (by simpa [FixedBytes.bitWidth])

/-- Natural construction retains the low 160 bits. -/
@[simp]
theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 160 := by
  simp [toNat, ofNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Converting through a natural number is lossless. -/
@[simp]
theorem ofNat_toNat (value : Address) : ofNat value.toNat = value := by
  apply toFixedBytes_injective
  simp [ofNat, toNat]

/-- Every address lies below the 160-bit modulus. -/
theorem toNat_lt (value : Address) : value.toNat < 2 ^ 160 := by
  simpa [toNat, FixedBytes.modulus, FixedBytes.bitWidth] using
    FixedBytes.toNat_lt_modulus value.toFixedBytes

/-- The greatest address payload is `2 ^ 160 - 1`. -/
@[simp]
theorem toNat_max : max.toNat = 2 ^ 160 - 1 := by
  simp [max, toNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Checked construction fails exactly outside the 160-bit range. -/
@[simp]
theorem ofNat?_eq_none_iff (n : ℕ) : ofNat? n = none ↔ 2 ^ 160 ≤ n := by
  simp [ofNat?, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Checked construction succeeds exactly for representable address values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : Address} :
    ofNat? n = some value ↔ n < 2 ^ 160 ∧ ofNat n = value := by
  simp [ofNat?, ofNat, FixedBytes.ofNat?_eq_some_iff, FixedBytes.modulus,
    FixedBytes.bitWidth]

/-- Unsigned order agrees with order on natural-number values. -/
@[simp]
theorem le_iff_toNat_le (a b : Address) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

/-- Strict order agrees with order on natural-number values. -/
@[simp]
theorem lt_iff_toNat_lt (a b : Address) : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

/-- Serialization always emits 20 bytes. -/
@[simp]
theorem toByteArray_size (value : Address) : value.toByteArray.size = 20 := by
  simp [toByteArray]

/-- Parsing succeeds exactly for 20-byte arrays. -/
@[simp]
theorem ofByteArray?_isSome (bytes : ByteArray) :
    (ofByteArray? bytes).isSome = decide (bytes.size = 20) := by
  simp [ofByteArray?]

/-- Parsing a serialized address is lossless. -/
@[simp]
theorem ofByteArray?_toByteArray (value : Address) :
    ofByteArray? value.toByteArray = some value := by
  simp [ofByteArray?, toByteArray]

/-- Serializing any successfully parsed address reproduces that input. -/
theorem toByteArray_ofByteArray?_eq_some {bytes : ByteArray} {value : Address}
    (h : ofByteArray? bytes = some value) : value.toByteArray = bytes := by
  simp only [ofByteArray?, Option.map_eq_some_iff] at h
  rcases h with ⟨raw, hraw, rfl⟩
  exact FixedBytes.toByteArray_ofByteArray?_eq_some hraw

/-- Converting an address to `H160` and back is lossless. -/
@[simp]
theorem ofH160_toH160 (value : Address) : ofH160 value.toH160 = value := by
  cases value
  rfl

/-- Converting `H160` to an address and back is lossless. -/
@[simp]
theorem toH160_ofH160 (value : H160) : (ofH160 value).toH160 = value := by
  cases value
  rfl

/-- Extracting an address from a word retains exactly its low 160 bits. -/
@[simp]
theorem toNat_ofU256 (value : U256) : (ofU256 value).toNat = value.toNat % 2 ^ 160 := by
  simp [ofU256]

/-- Checked word conversion succeeds exactly when the word fits in 160 bits. -/
theorem ofU256?_eq_some_iff {word : U256} {value : Address} :
    ofU256? word = some value ↔ word.toNat < 2 ^ 160 ∧ ofU256 word = value := by
  exact ofNat?_eq_some_iff

/-- Zero-extension preserves the unsigned address value. -/
@[simp]
theorem toNat_toU256 (value : Address) : value.toU256.toNat = value.toNat := by
  change FixedUInt.toNat (FixedUInt.ofNat value.toNat : U256) = value.toNat
  rw [FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans value.toNat_lt (by decide)

/-- Zero-extending an address and taking its low 160 bits is lossless. -/
@[simp]
theorem ofU256_toU256 (value : Address) : ofU256 value.toU256 = value := by
  apply toFixedBytes_injective
  apply FixedBytes.toNat_injective
  change (ofU256 value.toU256).toNat = value.toNat
  rw [toNat_ofU256, toNat_toU256, Nat.mod_eq_of_lt value.toNat_lt]

/-- Checked conversion accepts every zero-extended address word. -/
@[simp]
theorem ofU256?_toU256 (value : Address) : ofU256? value.toU256 = some value := by
  apply ofU256?_eq_some_iff.mpr
  rw [toNat_toU256]
  exact ⟨value.toNat_lt, ofU256_toU256 value⟩

end Address

end Lean4EVM
