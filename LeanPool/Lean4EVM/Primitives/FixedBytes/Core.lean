/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Digits.Defs

/-!
# Fixed-size byte core

This module owns the generic `FixedBytes size` representation, exact-length big-endian codec, and
their shared laws. Nominal Ethereum meanings are introduced only by the `H160`, `H256`, `Bytes32`,
and `Address` modules, preventing equal-width values from becoming interchangeable.
-/

namespace Lean4EVM

/-! ## Generic fixed-size bytes -/

/-- A byte string containing exactly `size` bytes. -/
@[ext]
structure FixedBytes (size : ℕ) where
  /-- The underlying `8 * size` bits. -/
  val : BitVec (8 * size)
  deriving Repr, Hashable

namespace FixedBytes

variable {size : ℕ}

/-- Returns the number of bits in `size` bytes. -/
def bitWidth (size : ℕ) : ℕ :=
  8 * size

/-- Returns the cardinality `2 ^ (8 * size)` of a fixed-byte domain. -/
def modulus (size : ℕ) : ℕ :=
  2 ^ bitWidth size

/-- Constructs fixed bytes by retaining the low `8 * size` bits of `n`. -/
def ofNat (size : ℕ) (n : ℕ) : FixedBytes size :=
  ⟨BitVec.ofNat (bitWidth size) n⟩

/-- Constructs fixed bytes only when `n` fits in `size` bytes. -/
def ofNat? (size : ℕ) (n : ℕ) : Option (FixedBytes size) :=
  if n < modulus size then some (ofNat size n) else none

/-- Returns the big-endian byte string interpreted as an unsigned natural number. -/
def toNat (value : FixedBytes size) : ℕ :=
  value.val.toNat

/-- Returns the exact-width hexadecimal representation. -/
def toHex (value : FixedBytes size) : String :=
  if size = 0 then "0x" else "0x" ++ value.val.toHex

/-- Returns the greatest `size`-byte value. -/
def max (size : ℕ) : FixedBytes size :=
  ⟨BitVec.allOnes (bitWidth size)⟩

/-- Returns the byte at `index` in big-endian order, or zero when out of bounds. -/
def getByte (value : FixedBytes size) (index : ℕ) : UInt8 :=
  if index < size then
    UInt8.ofNat ((value.toNat / 2 ^ (8 * (size - 1 - index))) % 256)
  else
    0

/-- Returns bit `index`, counting from the least-significant bit. -/
def testBit (value : FixedBytes size) (index : ℕ) : Bool :=
  value.val.getLsbD index

/-- Interprets a byte list as a big-endian natural number. -/
def byteListToNat (bytes : List UInt8) : ℕ :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Interprets a byte array as a big-endian natural number. -/
def byteArrayToNat (bytes : ByteArray) : ℕ :=
  byteListToNat bytes.data.toList

/-- Big-endian decoding is little-endian digit evaluation after reversing the bytes. -/
theorem byteListToNat_eq_ofDigits (bytes : List UInt8) :
    byteListToNat bytes = Nat.ofDigits 256 (bytes.reverse.map UInt8.toNat) := by
  unfold byteListToNat
  rw [List.foldl_eq_foldr_reverse, Nat.ofDigits_eq_foldr]
  simp only [List.foldr_map]
  congr 1
  funext byte acc
  simp [Nat.add_comm, Nat.mul_comm]

/-- A byte list decodes below the cardinality determined by its length. -/
theorem byteListToNat_lt (bytes : List UInt8) :
    byteListToNat bytes < 256 ^ bytes.length := by
  rw [byteListToNat_eq_ofDigits]
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (l := bytes.reverse.map UInt8.toNat)
    (by decide) (by
      intro digit hdigit
      rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
      exact UInt8.toNat_lt byte)
  simpa using h

/-- Equal-length byte lists with equal big-endian values are equal. -/
theorem byteListToNat_injective_of_length_eq {a b : List UInt8}
    (hlength : a.length = b.length) (hvalue : byteListToNat a = byteListToNat b) : a = b := by
  have hdigits : Nat.ofDigits 256 (a.reverse.map UInt8.toNat) =
      Nat.ofDigits 256 (b.reverse.map UInt8.toNat) := by
    simpa [byteListToNat_eq_ofDigits] using hvalue
  have hmapped : a.reverse.map UInt8.toNat = b.reverse.map UInt8.toNat := by
    apply Nat.ofDigits_inj_of_len_eq (b := 256) (by decide)
    · simpa using hlength
    · intro digit hdigit
      rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
      exact UInt8.toNat_lt byte
    · intro digit hdigit
      rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
      exact UInt8.toNat_lt byte
    · exact hdigits
  have hreversed : a.reverse = b.reverse :=
    (List.map_inj_right fun x y h => UInt8.toNat_inj.mp h).mp hmapped
  simpa using congrArg List.reverse hreversed

/-- A byte array decodes below the cardinality determined by its length. -/
theorem byteArrayToNat_lt (bytes : ByteArray) :
    byteArrayToNat bytes < 256 ^ bytes.size := by
  simpa [byteArrayToNat, ByteArray.size_data] using byteListToNat_lt bytes.data.toList

/-- Equal-length byte arrays with equal big-endian values are equal. -/
theorem byteArrayToNat_injective_of_size_eq {a b : ByteArray}
    (hsize : a.size = b.size) (hvalue : byteArrayToNat a = byteArrayToNat b) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply byteListToNat_injective_of_length_eq
  · simpa [ByteArray.size_data] using hsize
  · exact hvalue

/-- Encodes the low `size` bytes of `n` in big-endian order. -/
def natToByteList : (size : ℕ) → ℕ → List UInt8
  | 0, _ => []
  | size + 1, n =>
      UInt8.ofNat (n / 256 ^ size) :: natToByteList size (n % 256 ^ size)

/-- Parses a big-endian byte array when its length is exactly `size`. -/
def ofByteArray? (size : ℕ) (bytes : ByteArray) : Option (FixedBytes size) :=
  if bytes.size = size then some (ofNat size (byteArrayToNat bytes)) else none

/-- Serializes `value` as exactly `size` bytes in big-endian order. -/
def toByteArray (value : FixedBytes size) : ByteArray :=
  (natToByteList size value.toNat).toByteArray

/-- Zero is the all-zero byte string. -/
instance : Zero (FixedBytes size) where
  zero := ofNat size 0

/-- One has only the least-significant bit set, when the size is nonzero. -/
instance : One (FixedBytes size) where
  one := ofNat size 1

/-- Natural casts retain the low `8 * size` bits. -/
instance : NatCast (FixedBytes size) where
  natCast := ofNat size

/-- The default fixed byte string is zero. -/
instance : Inhabited (FixedBytes size) :=
  ⟨0⟩

/-- String conversion uses exact-width hexadecimal notation. -/
instance : ToString (FixedBytes size) where
  toString := toHex

/-- Complement flips every stored bit. -/
instance : Complement (FixedBytes size) where
  complement value := ⟨~~~value.val⟩

/-- Conjunction combines equal-position bits. -/
instance : AndOp (FixedBytes size) where
  and a b := ⟨a.val &&& b.val⟩

/-- Disjunction combines equal-position bits. -/
instance : OrOp (FixedBytes size) where
  or a b := ⟨a.val ||| b.val⟩

/-- Exclusive-or compares equal-position bits. -/
instance : XorOp (FixedBytes size) where
  xor a b := ⟨a.val ^^^ b.val⟩

/-- Equal unsigned values identify equal fixed byte strings. -/
theorem toNat_injective : Function.Injective (toNat : FixedBytes size → ℕ) := by
  intro ⟨a⟩ ⟨b⟩ h
  congr
  exact BitVec.eq_of_toNat_eq h

/-- Fixed byte strings use unsigned big-endian numeric order. -/
instance : LinearOrder (FixedBytes size) :=
  LinearOrder.lift' toNat toNat_injective

/-- Extracting the value of constructed fixed bytes performs width reduction. -/
@[simp]
theorem toNat_ofNat (size n : ℕ) :
    (ofNat size n).toNat = n % modulus size := by
  simp [ofNat, toNat, modulus, bitWidth]

/-- Natural casts into fixed bytes perform width reduction. -/
@[simp]
theorem toNat_natCast (n : ℕ) :
    ((n : FixedBytes size)).toNat = n % modulus size := by
  exact toNat_ofNat size n

/-- Converting fixed bytes to a natural number and back is lossless. -/
@[simp]
theorem ofNat_toNat (value : FixedBytes size) : ofNat size value.toNat = value := by
  apply toNat_injective
  rw [toNat_ofNat, Nat.mod_eq_of_lt]
  exact value.val.isLt

/-- Every `size`-byte value lies below its domain cardinality. -/
theorem toNat_lt_modulus (value : FixedBytes size) : value.toNat < modulus size := by
  exact value.val.isLt

/-- Checked construction succeeds exactly for representable values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : FixedBytes size} :
    ofNat? size n = some value ↔ n < modulus size ∧ ofNat size n = value := by
  simp only [ofNat?]
  split <;> simp_all

/-- Checked construction rejects exactly the out-of-range natural numbers. -/
@[simp]
theorem ofNat?_eq_none_iff (size n : ℕ) :
    ofNat? size n = none ↔ modulus size ≤ n := by
  simp [ofNat?]

/-- The greatest fixed byte value is one below the domain cardinality. -/
@[simp]
theorem toNat_max (size : ℕ) : (max size).toNat = modulus size - 1 := by
  simp [max, toNat, modulus, bitWidth]

/-- Unsigned order agrees with order on natural-number values. -/
@[simp]
theorem le_iff_toNat_le (a b : FixedBytes size) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

/-- Strict order agrees with order on natural-number values. -/
@[simp]
theorem lt_iff_toNat_lt (a b : FixedBytes size) : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

/-- Equality agrees with equality of natural-number values. -/
@[simp]
theorem toNat_inj {a b : FixedBytes size} : a.toNat = b.toNat ↔ a = b :=
  toNat_injective.eq_iff

/-- Complement has the expected unsigned numeric value. -/
@[simp]
theorem toNat_complement (value : FixedBytes size) :
    (~~~value).toNat = modulus size - 1 - value.toNat := by
  change (~~~value.val).toNat = modulus size - 1 - value.val.toNat
  simp [modulus, bitWidth]

/-- Bitwise conjunction agrees with conjunction of unsigned values. -/
@[simp]
theorem toNat_and (a b : FixedBytes size) : (a &&& b).toNat = a.toNat &&& b.toNat := by
  change (a.val &&& b.val).toNat = a.val.toNat &&& b.val.toNat
  simp

/-- Bitwise disjunction agrees with disjunction of unsigned values. -/
@[simp]
theorem toNat_or (a b : FixedBytes size) : (a ||| b).toNat = a.toNat ||| b.toNat := by
  change (a.val ||| b.val).toNat = a.val.toNat ||| b.val.toNat
  simp

/-- Bitwise exclusive-or agrees with exclusive-or of unsigned values. -/
@[simp]
theorem toNat_xor (a b : FixedBytes size) : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).toNat = a.val.toNat ^^^ b.val.toNat
  simp

/-- Testing a fixed byte value agrees with testing its unsigned value. -/
@[simp]
theorem testBit_eq (value : FixedBytes size) (index : ℕ) :
    value.testBit index = value.toNat.testBit index := by
  exact (BitVec.testBit_toNat value.val).symm

/-- Bits beyond the fixed byte width are false. -/
theorem testBit_of_bitWidth_le (value : FixedBytes size) (index : ℕ)
    (h : bitWidth size ≤ index) : value.testBit index = false := by
  exact BitVec.getLsbD_of_ge value.val index h

/-- Reading an in-range byte uses Ethereum's most-significant-byte-first indexing. -/
@[simp]
theorem getByte_of_index_lt (value : FixedBytes size) (index : ℕ) (h : index < size) :
    value.getByte index =
      UInt8.ofNat ((value.toNat / 2 ^ (8 * (size - 1 - index))) % 256) := by
  simp [getByte, h]

/-- Reading beyond the fixed byte width returns zero. -/
@[simp]
theorem getByte_of_index_ge (value : FixedBytes size) (index : ℕ) (h : size ≤ index) :
    value.getByte index = 0 := by
  simp [getByte, Nat.not_lt.mpr h]

/-- The big-endian encoder emits exactly its requested number of bytes. -/
@[simp]
theorem natToByteList_length (size n : ℕ) : (natToByteList size n).length = size := by
  induction size generalizing n with
  | zero => rfl
  | succ size ih => simp [natToByteList, ih]

/-- The modulus of `size` bytes is `256 ^ size`. -/
theorem byteBase_pow_eq_modulus (size : ℕ) : 256 ^ size = modulus size := by
  simp [modulus, bitWidth, pow_mul]

private theorem byteListToNat_natToByteList (size n acc : ℕ) (h : n < 256 ^ size) :
    (natToByteList size n).foldl (fun acc byte => acc * 256 + byte.toNat) acc =
      acc * 256 ^ size + n := by
  induction size generalizing n acc with
  | zero =>
      have hn : n = 0 := by simpa using h
      simp [natToByteList, hn]
  | succ size ih =>
      have hp : 0 < 256 ^ size := Nat.pow_pos (by decide)
      have hq : n / 256 ^ size < 256 := by
        rw [Nat.div_lt_iff_lt_mul hp]
        simpa [Nat.pow_succ, Nat.mul_comm] using h
      have hr : n % 256 ^ size < 256 ^ size := Nat.mod_lt _ hp
      simp only [natToByteList, List.foldl_cons]
      rw [ih _ _ hr, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hq]
      simp only [Nat.add_mul, Nat.pow_succ]
      rw [Nat.mul_assoc acc 256 (256 ^ size), Nat.mul_comm 256 (256 ^ size),
        ← Nat.mul_assoc acc (256 ^ size) 256, Nat.mul_comm (n / 256 ^ size) (256 ^ size),
        Nat.add_assoc, Nat.div_add_mod]

/-- Decoding a bounded value's fixed-size big-endian encoding is lossless. -/
@[simp]
theorem byteArrayToNat_toByteArray (value : FixedBytes size) :
    byteArrayToNat value.toByteArray = value.toNat := by
  unfold byteArrayToNat byteListToNat toByteArray
  simp only [List.toList_data_toByteArray]
  have h := value.toNat_lt_modulus
  rw [← byteBase_pow_eq_modulus] at h
  simpa using byteListToNat_natToByteList size value.toNat 0 h

/-- Serialization always emits exactly the declared number of bytes. -/
@[simp]
theorem toByteArray_size (value : FixedBytes size) : value.toByteArray.size = size := by
  simp [toByteArray]

/-- Exact-size parsing has a result precisely when the input length matches. -/
@[simp]
theorem ofByteArray?_isSome (size : ℕ) (bytes : ByteArray) :
    (ofByteArray? size bytes).isSome = decide (bytes.size = size) := by
  unfold ofByteArray?
  split <;> simp_all

/-- Exact-size parsing fails precisely when the input length differs. -/
@[simp]
theorem ofByteArray?_eq_none_iff (size : ℕ) (bytes : ByteArray) :
    ofByteArray? size bytes = none ↔ bytes.size ≠ size := by
  simp [ofByteArray?]

/-- Parsing returns a value exactly when the size and big-endian value agree. -/
theorem ofByteArray?_eq_some_iff {bytes : ByteArray} {value : FixedBytes size} :
    ofByteArray? size bytes = some value ↔
      bytes.size = size ∧ ofNat size (byteArrayToNat bytes) = value := by
  unfold ofByteArray?
  split <;> simp_all

/-- A length-valid array parses to its big-endian numeric value. -/
theorem ofByteArray?_eq_some_of_size (bytes : ByteArray) (h : bytes.size = size) :
    ofByteArray? size bytes = some (ofNat size (byteArrayToNat bytes)) := by
  simp [ofByteArray?, h]

/-- Parsing a serialized fixed byte value is lossless. -/
@[simp]
theorem ofByteArray?_toByteArray (value : FixedBytes size) :
    ofByteArray? size value.toByteArray = some value := by
  rw [ofByteArray?_eq_some_of_size value.toByteArray value.toByteArray_size,
    byteArrayToNat_toByteArray, ofNat_toNat]

/-- Serializing any successfully parsed exact-size input reproduces that input. -/
theorem toByteArray_ofByteArray?_eq_some {bytes : ByteArray} {value : FixedBytes size}
    (h : ofByteArray? size bytes = some value) : value.toByteArray = bytes := by
  rcases ofByteArray?_eq_some_iff.mp h with ⟨hsize, hvalue⟩
  rw [← hvalue]
  apply byteArrayToNat_injective_of_size_eq
  · simpa using hsize.symm
  · rw [byteArrayToNat_toByteArray, toNat_ofNat, Nat.mod_eq_of_lt]
    rw [← byteBase_pow_eq_modulus]
    simpa [hsize] using byteArrayToNat_lt bytes

end FixedBytes

/-! ## Generic ABI widths -/

/-- A generic four-byte ABI value, commonly used for function selectors. -/
abbrev Bytes4 := FixedBytes 4

/-- A generic eight-byte ABI value. -/
abbrev Bytes8 := FixedBytes 8

end Lean4EVM
