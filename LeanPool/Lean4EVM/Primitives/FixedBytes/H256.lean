/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.FixedBytes.Core
import LeanPool.Lean4EVM.Primitives.FixedBytes.H160
import LeanPool.Lean4EVM.Primitives.UInt.U256

/-!
# `H256`

Nominal 256-bit hash values and explicit, lossless reinterpretation of EVM words.
-/

namespace Lean4EVM

/-! ## `H256` -/

/-- A nominal 256-bit hash value. It is distinct from an EVM word and raw `Bytes32`. -/
@[ext]
structure H256 where
  /-- The exact 32-byte representation. -/
  bytes : FixedBytes 32
  deriving Repr, Hashable

namespace H256

/-- Constructs `H256` from its exact generic representation. -/
def ofFixedBytes (value : FixedBytes 32) : H256 :=
  ⟨value⟩

/-- Returns the exact generic representation. -/
def toFixedBytes (value : H256) : FixedBytes 32 :=
  value.bytes

/-- Constructs `H256` by retaining the low 256 bits. -/
def ofNat (n : ℕ) : H256 :=
  ofFixedBytes (FixedBytes.ofNat 32 n)

/-- Constructs `H256` only when `n` fits in 256 bits. -/
def ofNat? (n : ℕ) : Option H256 :=
  (FixedBytes.ofNat? 32 n).map ofFixedBytes

/-- Returns the unsigned natural-number value. -/
def toNat (value : H256) : ℕ :=
  value.toFixedBytes.toNat

/-- Returns the exact 32-byte hexadecimal representation. -/
def toHex (value : H256) : String :=
  value.toFixedBytes.toHex

/-- Returns the byte at `index` in big-endian order, or zero out of bounds. -/
def getByte (value : H256) (index : ℕ) : UInt8 :=
  value.toFixedBytes.getByte index

/-- Returns bit `index`, counting from the least-significant bit. -/
def testBit (value : H256) (index : ℕ) : Bool :=
  value.toFixedBytes.testBit index

/-- Parses an exact 32-byte big-endian array. -/
def ofByteArray? (bytes : ByteArray) : Option H256 :=
  (FixedBytes.ofByteArray? 32 bytes).map ofFixedBytes

/-- Serializes `value` as exactly 32 big-endian bytes. -/
def toByteArray (value : H256) : ByteArray :=
  value.toFixedBytes.toByteArray

/-- Returns the greatest 256-bit hash value. -/
def max : H256 :=
  ofFixedBytes (FixedBytes.max 32)

/-- Reinterprets an EVM word as a 256-bit hash. -/
def ofU256 (value : U256) : H256 :=
  ofFixedBytes ⟨value.val⟩

/-- Reinterprets a 256-bit hash as an EVM word. -/
def toU256 (value : H256) : U256 :=
  ⟨value.toFixedBytes.val⟩

/-- Reinterprets the last twenty bytes of a hash as `H160`, which is how Ethereum derives an
account identifier from a digest. The leading twelve bytes are discarded. -/
def toH160 (value : H256) : H160 :=
  H160.ofNat value.toNat

/-- Places a 160-bit hash in the last twenty bytes of an `H256`, leaving the leading twelve zero. -/
def ofH160 (value : H160) : H256 :=
  ofNat value.toNat

/-- Equality of generic representations identifies equal `H256` values. -/
theorem toFixedBytes_injective : Function.Injective toFixedBytes := by
  intro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

/-- `H256` uses unsigned big-endian numeric order. -/
instance : LinearOrder H256 :=
  LinearOrder.lift' toFixedBytes toFixedBytes_injective

/-- Zero is the all-zero 256-bit hash. -/
instance : Zero H256 where
  zero := ofNat 0

/-- One has only the least-significant bit set. -/
instance : One H256 where
  one := ofNat 1

/-- Natural casts retain the low 256 bits. -/
instance : NatCast H256 where
  natCast := ofNat

/-- The default `H256` is zero. -/
instance : Inhabited H256 :=
  ⟨0⟩

/-- String conversion emits exact-width hexadecimal notation. -/
instance : ToString H256 where
  toString := toHex

/-- Complement flips every bit of a 256-bit hash. -/
instance : Complement H256 where
  complement value := ofFixedBytes (~~~value.toFixedBytes)

/-- Conjunction combines equal-position hash bits. -/
instance : AndOp H256 where
  and a b := ofFixedBytes (a.toFixedBytes &&& b.toFixedBytes)

/-- Disjunction combines equal-position hash bits. -/
instance : OrOp H256 where
  or a b := ofFixedBytes (a.toFixedBytes ||| b.toFixedBytes)

/-- Exclusive-or compares equal-position hash bits. -/
instance : XorOp H256 where
  xor a b := ofFixedBytes (a.toFixedBytes ^^^ b.toFixedBytes)

/-- Converting from generic bytes and back is lossless. -/
@[simp]
theorem toFixedBytes_ofFixedBytes (value : FixedBytes 32) :
    (ofFixedBytes value).toFixedBytes = value :=
  rfl

/-- Converting to generic bytes and back is lossless. -/
@[simp]
theorem ofFixedBytes_toFixedBytes (value : H256) :
    ofFixedBytes value.toFixedBytes = value := by
  cases value
  rfl

/-- Equal unsigned values identify equal `H256` values. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  apply toFixedBytes_injective
  exact FixedBytes.toNat_injective h

/-- Equality agrees with equality of unsigned values. -/
@[simp]
theorem toNat_inj {a b : H256} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

/-- Complement is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_complement (value : H256) :
    (~~~value).toFixedBytes = ~~~value.toFixedBytes :=
  rfl

/-- Conjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_and (a b : H256) :
    (a &&& b).toFixedBytes = a.toFixedBytes &&& b.toFixedBytes :=
  rfl

/-- Disjunction is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_or (a b : H256) :
    (a ||| b).toFixedBytes = a.toFixedBytes ||| b.toFixedBytes :=
  rfl

/-- Exclusive-or is preserved by the generic representation. -/
@[simp]
theorem toFixedBytes_xor (a b : H256) :
    (a ^^^ b).toFixedBytes = a.toFixedBytes ^^^ b.toFixedBytes :=
  rfl

/-- Bit testing agrees with the unsigned value. -/
@[simp]
theorem testBit_eq (value : H256) (index : ℕ) :
    value.testBit index = value.toNat.testBit index :=
  FixedBytes.testBit_eq value.toFixedBytes index

/-- Bits at indices 256 and above are false. -/
theorem testBit_of_ge (value : H256) (index : ℕ) (h : 256 ≤ index) :
    value.testBit index = false := by
  exact FixedBytes.testBit_of_bitWidth_le value.toFixedBytes index (by simpa [FixedBytes.bitWidth])

/-- Natural construction retains the low 256 bits. -/
@[simp]
theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 256 := by
  simp [toNat, ofNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Converting through a natural number is lossless. -/
@[simp]
theorem ofNat_toNat (value : H256) : ofNat value.toNat = value := by
  apply toFixedBytes_injective
  simp [ofNat, toNat]

/-- Every `H256` value is smaller than `2 ^ 256`. -/
theorem toNat_lt (value : H256) : value.toNat < 2 ^ 256 := by
  simpa [toNat, FixedBytes.modulus, FixedBytes.bitWidth] using
    FixedBytes.toNat_lt_modulus value.toFixedBytes

/-- The greatest `H256` value is `2 ^ 256 - 1`. -/
@[simp]
theorem toNat_max : max.toNat = 2 ^ 256 - 1 := by
  simp [max, toNat, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Unsigned order agrees with order on natural-number values. -/
@[simp]
theorem le_iff_toNat_le (a b : H256) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

/-- Strict order agrees with order on natural-number values. -/
@[simp]
theorem lt_iff_toNat_lt (a b : H256) : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

/-- Checked construction fails exactly outside the 256-bit range. -/
@[simp]
theorem ofNat?_eq_none_iff (n : ℕ) : ofNat? n = none ↔ 2 ^ 256 ≤ n := by
  simp [ofNat?, FixedBytes.modulus, FixedBytes.bitWidth]

/-- Checked construction succeeds exactly for representable 256-bit values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : H256} :
    ofNat? n = some value ↔ n < 2 ^ 256 ∧ ofNat n = value := by
  simp [ofNat?, ofNat, FixedBytes.ofNat?_eq_some_iff, FixedBytes.modulus,
    FixedBytes.bitWidth]

/-- Serialization always emits 32 bytes. -/
@[simp]
theorem toByteArray_size (value : H256) : value.toByteArray.size = 32 := by
  simp [toByteArray]

/-- Parsing succeeds exactly for 32-byte arrays. -/
@[simp]
theorem ofByteArray?_isSome (bytes : ByteArray) :
    (ofByteArray? bytes).isSome = decide (bytes.size = 32) := by
  simp [ofByteArray?]

/-- Parsing a serialized `H256` value is lossless. -/
@[simp]
theorem ofByteArray?_toByteArray (value : H256) :
    ofByteArray? value.toByteArray = some value := by
  simp [ofByteArray?, toByteArray]

/-- Serializing any successfully parsed `H256` input reproduces that input. -/
theorem toByteArray_ofByteArray?_eq_some {bytes : ByteArray} {value : H256}
    (h : ofByteArray? bytes = some value) : value.toByteArray = bytes := by
  simp only [ofByteArray?, Option.map_eq_some_iff] at h
  rcases h with ⟨raw, hraw, rfl⟩
  exact FixedBytes.toByteArray_ofByteArray?_eq_some hraw

/-- Reinterpreting a hash as a word and back is lossless. -/
@[simp]
theorem ofU256_toU256 (value : H256) : ofU256 value.toU256 = value := by
  cases value
  rfl

/-- Reinterpreting a word as a hash and back is lossless. -/
@[simp]
theorem toU256_ofU256 (value : U256) : (ofU256 value).toU256 = value :=
  rfl

/-- Word conversion preserves the unsigned value. -/
@[simp]
theorem toNat_toU256 (value : H256) : value.toU256.toNat = value.toNat :=
  rfl

/-- Hash construction from a word preserves the unsigned value. -/
@[simp]
theorem toNat_ofU256 (value : U256) : (ofU256 value).toNat = value.toNat :=
  rfl

/-- Narrowing to `H160` keeps exactly the low 160 bits. -/
@[simp]
theorem toNat_toH160 (value : H256) : value.toH160.toNat = value.toNat % 2 ^ 160 := by
  simp [toH160]

/-- Widening a 160-bit hash preserves its unsigned value. -/
@[simp]
theorem toNat_ofH160 (value : H160) : (ofH160 value).toNat = value.toNat := by
  rw [ofH160, toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans value.toNat_lt (by decide)

/-- Widening a 160-bit hash and narrowing it back is lossless. -/
@[simp]
theorem toH160_ofH160 (value : H160) : (ofH160 value).toH160 = value := by
  apply H160.toNat_injective
  rw [toNat_toH160, toNat_ofH160, Nat.mod_eq_of_lt value.toNat_lt]

/-- Narrowing is a left inverse of widening, which is the source of the two facts below. -/
theorem leftInverse_toH160_ofH160 : Function.LeftInverse toH160 ofH160 :=
  toH160_ofH160

/-- Distinct 160-bit hashes widen to distinct 256-bit hashes. -/
theorem ofH160_injective : Function.Injective ofH160 :=
  leftInverse_toH160_ofH160.injective

/-- Every 160-bit hash is the narrowing of some 256-bit hash. -/
theorem toH160_surjective : Function.Surjective toH160 :=
  leftInverse_toH160_ofH160.surjective

/-- Narrowing then widening recovers the hash exactly when its leading twelve bytes are zero. -/
theorem ofH160_toH160_iff {value : H256} :
    ofH160 value.toH160 = value ↔ value.toNat < 2 ^ 160 := by
  constructor
  · intro h
    have hvalue := congrArg H256.toNat h
    rw [toNat_ofH160, toNat_toH160] at hvalue
    exact hvalue ▸ Nat.mod_lt _ (by decide)
  · intro h
    apply toNat_injective
    rw [toNat_ofH160, toNat_toH160, Nat.mod_eq_of_lt h]

/-- Widening changes no bit: every bit at 160 and above was already false. The simp set already
proves this from the value lemmas, so it is stated for readability rather than marked `@[simp]`. -/
theorem testBit_ofH160 (value : H160) (index : ℕ) :
    (ofH160 value).testBit index = value.testBit index := by
  rw [testBit_eq, H160.testBit_eq, toNat_ofH160]

/-- Narrowing preserves every bit below 160 and drops exactly the rest. -/
theorem testBit_toH160 (value : H256) (index : ℕ) (h : index < 160) :
    value.toH160.testBit index = value.testBit index := by
  rw [H160.testBit_eq, testBit_eq, toNat_toH160, Nat.testBit_mod_two_pow]
  simp [h]

/-- Reducing modulo `2 ^ 160` leaves every byte that lies below that boundary unchanged. -/
private theorem mod_pow_div_mod (n k : ℕ) (h : k + 8 ≤ 160) :
    n % 2 ^ 160 / 2 ^ k % 256 = n / 2 ^ k % 256 := by
  have hsplit : (2 : ℕ) ^ 160 = 2 ^ k * 2 ^ (160 - k) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  refine Nat.mod_mod_of_dvd _ ?_
  have h256 : (256 : ℕ) = 2 ^ 8 := by decide
  rw [h256]
  exact pow_dvd_pow 2 (by omega)

/-- Byte `index` of the narrowed hash is byte `index + 12` of the original: the Ethereum rule that
an account identifier is the last twenty bytes of a digest. -/
theorem getByte_toH160 (value : H256) (index : ℕ) (h : index < 20) :
    value.toH160.getByte index = value.getByte (index + 12) := by
  rw [H160.getByte, H256.getByte, FixedBytes.getByte_of_index_lt _ _ h,
    FixedBytes.getByte_of_index_lt _ _ (by omega : index + 12 < 32)]
  congr 1
  change value.toH160.toNat / 2 ^ (8 * (20 - 1 - index)) % 256 =
    value.toNat / 2 ^ (8 * (32 - 1 - (index + 12))) % 256
  rw [toNat_toH160]
  have hindex : 8 * (20 - 1 - index) = 8 * (32 - 1 - (index + 12)) := by omega
  rw [hindex]
  exact mod_pow_div_mod _ _ (by omega)

/-- Widening places source byte `index` at byte `index + 12` of the result. -/
theorem getByte_ofH160 (value : H160) (index : ℕ) (h : index < 20) :
    (ofH160 value).getByte (index + 12) = value.getByte index := by
  rw [H256.getByte, H160.getByte, FixedBytes.getByte_of_index_lt _ _ (by omega : index + 12 < 32),
    FixedBytes.getByte_of_index_lt _ _ h]
  congr 1
  change (ofH160 value).toNat / 2 ^ (8 * (32 - 1 - (index + 12))) % 256 =
    value.toNat / 2 ^ (8 * (20 - 1 - index)) % 256
  rw [toNat_ofH160]
  have hindex : 8 * (32 - 1 - (index + 12)) = 8 * (20 - 1 - index) := by omega
  rw [hindex]

/-- The leading twelve bytes of a widened hash are zero. -/
theorem getByte_ofH160_of_lt (value : H160) (index : ℕ) (h : index < 12) :
    (ofH160 value).getByte index = 0 := by
  rw [H256.getByte, FixedBytes.getByte_of_index_lt _ _ (by omega : index < 32)]
  have hzero : (ofH160 value).toNat / 2 ^ (8 * (32 - 1 - index)) = 0 := by
    apply Nat.div_eq_of_lt
    refine lt_of_lt_of_le (toNat_ofH160 value ▸ value.toNat_lt) ?_
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change UInt8.ofNat ((ofH160 value).toNat / 2 ^ (8 * (32 - 1 - index)) % 256) = 0
  rw [hzero]
  rfl

end H256

end Lean4EVM
