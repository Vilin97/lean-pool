/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/
import Mathlib.Data.BitVec

/-!
# Fixed-width unsigned integer core

This module owns `FixedUInt`, its executable modular arithmetic, the shared proof API, and the
nominal structures `U64`, `U128`, and `U256`. The concrete structures live here so width-specific
modules can depend on one acyclic representation layer. Type-owned operations and conversions are
defined in `U64`, `U128`, and `U256` modules.
-/

namespace Lean4EVM

/-- Representation interface shared by nominal fixed-width unsigned integer types. -/
class FixedUInt (α : Type) (width : outParam ℕ) where
  /-- Returns the fixed-width representation. -/
  toBitVec : α → BitVec width
  /-- Constructs a value from its exact-width representation. -/
  ofBitVec : BitVec width → α
  /-- Reconstructing a value from its representation is lossless. -/
  of_to : ∀ value, ofBitVec (toBitVec value) = value
  /-- Extracting the representation of a constructed value is lossless. -/
  to_of : ∀ bits, toBitVec (ofBitVec bits) = bits

namespace FixedUInt

variable {α : Type} {width : ℕ} [FixedUInt α width]

/-- Returns the modulus `2 ^ width` of a fixed-width arithmetic. -/
def modulus (width : ℕ) : ℕ :=
  2 ^ width

/-- Constructs a value by retaining the low `width` bits of `n`. -/
def ofNat (n : ℕ) : α :=
  FixedUInt.ofBitVec (BitVec.ofNat width n)

/-- Constructs a value when `n` fits in `width` bits. -/
def ofNat? (n : ℕ) : Option α :=
  if n < modulus width then some (ofNat n) else none

/-- Constructs a value from an integer using two's-complement wrapping. -/
def ofInt (n : ℤ) : α :=
  FixedUInt.ofBitVec (BitVec.ofInt width n)

/-- Constructs a value when `n` is nonnegative and fits in `width` bits. -/
def ofInt? (n : ℤ) : Option α :=
  if 0 ≤ n ∧ n < (modulus width : ℤ) then some (ofNat n.toNat) else none

/-- Returns the unsigned natural-number value. -/
def toNat (value : α) : ℕ :=
  (FixedUInt.toBitVec value).toNat

/-- Reinterprets the bit pattern as a signed two's-complement integer. -/
def toSignedInt (value : α) : ℤ :=
  (FixedUInt.toBitVec value).toInt

/-- Returns the exact-width hexadecimal representation. -/
def toHex (value : α) : String :=
  "0x" ++ (FixedUInt.toBitVec value).toHex

/-- Returns the greatest representable value. -/
def max : α :=
  FixedUInt.ofBitVec (BitVec.allOnes width)

/-- Returns `true` exactly when unsigned addition overflows. -/
def addOverflow (a b : α) : Bool :=
  decide (modulus width ≤ toNat a + toNat b)

/-- Returns `true` exactly when unsigned subtraction underflows. -/
def subOverflow (a b : α) : Bool :=
  decide (toNat a < toNat b)

/-- Returns `true` exactly when unsigned multiplication overflows. -/
def mulOverflow (a b : α) : Bool :=
  decide (modulus width ≤ toNat a * toNat b)

private def powStep (base : α) (bit : Bool) (result : α) : α :=
  let squared := FixedUInt.ofBitVec
    (FixedUInt.toBitVec result * FixedUInt.toBitVec result)
  if bit then
    FixedUInt.ofBitVec (FixedUInt.toBitVec squared * FixedUInt.toBitVec base)
  else
    squared

/-- Raises `base` to `exponent` by structural binary exponentiation. -/
def pow (base : α) (exponent : ℕ) : α :=
  Nat.binaryRec (ofNat 1) (fun bit _ result => powStep base bit result) exponent

/-- Adds two values modulo `2 ^ width`. -/
def wrappingAdd (a b : α) : α :=
  FixedUInt.ofBitVec (FixedUInt.toBitVec a + FixedUInt.toBitVec b)

/-- Subtracts two values modulo `2 ^ width`. -/
def wrappingSub (a b : α) : α :=
  FixedUInt.ofBitVec (FixedUInt.toBitVec a - FixedUInt.toBitVec b)

/-- Multiplies two values modulo `2 ^ width`. -/
def wrappingMul (a b : α) : α :=
  FixedUInt.ofBitVec (FixedUInt.toBitVec a * FixedUInt.toBitVec b)

/-- Negates a value modulo `2 ^ width`. -/
def wrappingNeg (value : α) : α :=
  FixedUInt.ofBitVec (-FixedUInt.toBitVec value)

/-- Raises a value to a natural exponent modulo `2 ^ width`. -/
def wrappingPow (base : α) (exponent : ℕ) : α :=
  pow base exponent

/-- Returns a wrapping sum together with its overflow flag. -/
def overflowingAdd (a b : α) : α × Bool :=
  (wrappingAdd a b, addOverflow a b)

/-- Returns a wrapping difference together with its underflow flag. -/
def overflowingSub (a b : α) : α × Bool :=
  (wrappingSub a b, subOverflow a b)

/-- Returns a wrapping product together with its overflow flag. -/
def overflowingMul (a b : α) : α × Bool :=
  (wrappingMul a b, mulOverflow a b)

/-- Adds two values when the exact sum fits. -/
def checkedAdd (a b : α) : Option α :=
  if addOverflow a b then none else some (wrappingAdd a b)

/-- Subtracts two values when the exact difference is nonnegative. -/
def checkedSub (a b : α) : Option α :=
  if subOverflow a b then none else some (wrappingSub a b)

/-- Multiplies two values when the exact product fits. -/
def checkedMul (a b : α) : Option α :=
  if mulOverflow a b then none else some (wrappingMul a b)

/-- Divides two values when the divisor is nonzero. -/
def checkedDiv (a b : α) : Option α :=
  if toNat b = 0 then none
  else some (ofNat (toNat a / toNat b))

/-- Computes a remainder when the divisor is nonzero. -/
def checkedMod (a b : α) : Option α :=
  if toNat b = 0 then none
  else some (ofNat (toNat a % toNat b))

/-- Returns quotient and remainder when the divisor is nonzero. -/
def checkedDivMod (a b : α) : Option (α × α) :=
  match checkedDiv a b, checkedMod a b with
  | some quotient, some remainder => some (quotient, remainder)
  | _, _ => none

/-- Adds two values and clamps overflow to the greatest value. -/
def saturatingAdd (a b : α) : α :=
  if addOverflow a b then max else wrappingAdd a b

/-- Subtracts two values and clamps underflow to zero. -/
def saturatingSub (a b : α) : α :=
  if subOverflow a b then ofNat 0 else wrappingSub a b

/-- Multiplies two values and clamps overflow to the greatest value. -/
def saturatingMul (a b : α) : α :=
  if mulOverflow a b then max else wrappingMul a b

/-- Returns the number of leading zero bits. -/
def leadingZeros (value : α) : ℕ :=
  (FixedUInt.toBitVec value).clz.toNat

/-- Returns the number of trailing zero bits. -/
def trailingZeros (value : α) : ℕ :=
  (FixedUInt.toBitVec value).ctz.toNat

/-- Returns the number of set bits. -/
def countOnes (value : α) : ℕ :=
  (FixedUInt.toBitVec value).cpop.toNat

/-- Returns bit `index`, counting from the least-significant bit. -/
def testBit (value : α) (index : ℕ) : Bool :=
  (FixedUInt.toBitVec value).getLsbD index

/-- Rotates the bit pattern left by `amount` modulo the word width. -/
def rotateLeft (value : α) (amount : ℕ) : α :=
  FixedUInt.ofBitVec ((FixedUInt.toBitVec value).rotateLeft amount)

/-- Rotates the bit pattern right by `amount` modulo the word width. -/
def rotateRight (value : α) (amount : ℕ) : α :=
  FixedUInt.ofBitVec ((FixedUInt.toBitVec value).rotateRight amount)

/-- Zero is the all-zero word. -/
instance : Zero α where
  zero := ofNat 0

/-- One is the word with only its least-significant bit set. -/
instance : One α where
  one := ofNat 1

/-- Natural casts wrap modulo the word modulus. -/
instance : NatCast α where
  natCast := ofNat

/-- Integer casts use two's-complement wrapping. -/
instance : IntCast α where
  intCast := ofInt

/-- Natural scalar multiplication is computed modulo the word modulus. -/
instance : SMul ℕ α where
  smul n value :=
    FixedUInt.ofBitVec (n • FixedUInt.toBitVec value)

/-- Integer scalar multiplication is computed modulo the word modulus. -/
instance : SMul ℤ α where
  smul n value :=
    FixedUInt.ofBitVec (n • FixedUInt.toBitVec value)

/-- The default fixed-width value is zero. -/
instance : Inhabited α :=
  ⟨ofNat 0⟩

/-- String conversion uses exact-width hexadecimal notation. -/
instance : ToString α where
  toString := toHex

/-- Addition wraps at the word width. -/
instance : Add α where
  add := wrappingAdd

/-- Subtraction wraps at the word width. -/
instance : Sub α where
  sub := wrappingSub

/-- Multiplication wraps at the word width. -/
instance : Mul α where
  mul := wrappingMul

/-- Negation wraps at the word width. -/
instance : Neg α where
  neg := wrappingNeg

/-- Natural powers use wrapping multiplication. -/
instance : Pow α ℕ where
  pow := wrappingPow

/-- Complement flips every bit in the word. -/
instance : Complement α where
  complement value := FixedUInt.ofBitVec (~~~FixedUInt.toBitVec value)

/-- Conjunction combines equal-position bits. -/
instance : AndOp α where
  and a b := FixedUInt.ofBitVec (FixedUInt.toBitVec a &&& FixedUInt.toBitVec b)

/-- Disjunction combines equal-position bits. -/
instance : OrOp α where
  or a b := FixedUInt.ofBitVec (FixedUInt.toBitVec a ||| FixedUInt.toBitVec b)

/-- Exclusive-or compares equal-position bits. -/
instance : XorOp α where
  xor a b := FixedUInt.ofBitVec (FixedUInt.toBitVec a ^^^ FixedUInt.toBitVec b)

/-- Left shift returns zero before evaluating an amount at least the word width. -/
instance : HShiftLeft α ℕ α where
  hShiftLeft value amount :=
    if amount < width then
      FixedUInt.ofBitVec (FixedUInt.toBitVec value <<< amount)
    else
      ofNat 0

/-- Logical right shift fills vacated bits with zero. -/
instance : HShiftRight α ℕ α where
  hShiftRight value amount := FixedUInt.ofBitVec (FixedUInt.toBitVec value >>> amount)

@[simp]
theorem toBitVec_ofBitVec (bits : BitVec width) :
    FixedUInt.toBitVec (FixedUInt.ofBitVec bits : α) = bits :=
  FixedUInt.to_of bits

@[simp]
theorem ofBitVec_toBitVec (value : α) :
    FixedUInt.ofBitVec (FixedUInt.toBitVec value) = value :=
  FixedUInt.of_to value

/-- Equality follows from equality of exact-width representations. -/
theorem toBitVec_injective : Function.Injective (FixedUInt.toBitVec : α → BitVec width) := by
  intro a b h
  rw [← ofBitVec_toBitVec a, ← ofBitVec_toBitVec b, h]

/-- Binary exponentiation agrees with exponentiation of the underlying bit vector. -/
theorem toBitVec_pow (base : α) (exponent : ℕ) :
    FixedUInt.toBitVec (pow base exponent) = FixedUInt.toBitVec base ^ exponent := by
  induction exponent using Nat.binaryRec with
  | zero => simp [pow, ofNat]
  | bit bit n ih =>
    rw [pow, Nat.binaryRec_eq]
    · change FixedUInt.toBitVec (powStep base bit (pow base n)) = _
      cases bit
      · simp only [powStep, Bool.false_eq_true, ↓reduceIte, toBitVec_ofBitVec, ih]
        rw [← pow_add]
        congr 1
        simp [Nat.bit]
        omega
      · simp only [powStep, ↓reduceIte, toBitVec_ofBitVec, ih]
        rw [← pow_add, ← pow_succ]
        congr 1
        simp [Nat.bit]
        omega
    · left
      apply toBitVec_injective
      simp [powStep, ofNat]

/-- Equality follows from equality of unsigned values. -/
theorem toNat_injective : Function.Injective (toNat : α → ℕ) := by
  intro a b h
  have hbits : FixedUInt.toBitVec a = FixedUInt.toBitVec b :=
    BitVec.eq_of_toNat_eq h
  calc
    a = FixedUInt.ofBitVec (FixedUInt.toBitVec a) := (ofBitVec_toBitVec a).symm
    _ = FixedUInt.ofBitVec (FixedUInt.toBitVec b) := congrArg FixedUInt.ofBitVec hbits
    _ = b := ofBitVec_toBitVec b

/-- Wrapped natural construction is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_ofNat (n : ℕ) :
    FixedUInt.toBitVec (ofNat n : α) = BitVec.ofNat width n := by
  simp [ofNat]

/-- Zero is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_zero : FixedUInt.toBitVec (0 : α) = 0 := by
  change FixedUInt.toBitVec (ofNat 0 : α) = 0
  simp

/-- One is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_one : FixedUInt.toBitVec (1 : α) = 1 := by
  change FixedUInt.toBitVec (ofNat 1 : α) = 1
  simp

/-- Natural casts are preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_natCast (n : ℕ) :
    FixedUInt.toBitVec (n : α) = (n : BitVec width) := by
  change FixedUInt.toBitVec (ofNat n : α) = BitVec.ofNat width n
  simp

/-- Integer casts are preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_intCast (n : ℤ) :
    FixedUInt.toBitVec (n : α) = (n : BitVec width) := by
  change FixedUInt.toBitVec (ofInt n : α) = BitVec.ofInt width n
  simp [ofInt]

/-- Fixed-width values inherit the unsigned linear order of natural numbers. -/
instance : LinearOrder α :=
  LinearOrder.lift' toNat toNat_injective

/-- Two fixed-width values are equal exactly when their unsigned values are equal. -/
@[simp]
theorem toNat_inj {a b : α} : toNat a = toNat b ↔ a = b :=
  toNat_injective.eq_iff

/-- Converting `n` with wrapping retains its residue modulo `2 ^ width`. -/
@[simp]
theorem toNat_ofNat (n : ℕ) :
    toNat (ofNat n : α) = n % modulus width := by
  simp [toNat, ofNat, modulus]

/-- Natural casts reduce modulo the word modulus. -/
theorem toNat_natCast (n : ℕ) :
    toNat (n : α) = n % modulus width := by
  change toNat (ofNat n : α) = _
  exact toNat_ofNat n

/-- Numeric literals at least two reduce modulo the word modulus. -/
theorem toNat_ofNat_lit (n : ℕ) [n.AtLeastTwo] :
    toNat (ofNat(n) : α) = n % modulus width := by
  exact toNat_natCast n

/-- Binary exponentiation computes natural exponentiation modulo the word modulus. -/
@[simp]
theorem toNat_pow (base : α) (exponent : ℕ) :
    toNat (pow base exponent) = toNat base ^ exponent % modulus width := by
  unfold toNat
  rw [toBitVec_pow]
  induction exponent with
  | zero => simp [modulus]
  | succ exponent ih =>
    rw [pow_succ, BitVec.toNat_mul, ih, Nat.pow_succ]
    simp [modulus, Nat.mul_mod]

/-- Wrapped integer construction agrees with reduction modulo the word modulus. -/
@[simp]
theorem toNat_ofInt (n : ℤ) :
    toNat (ofInt n : α) = (n % (modulus width : ℤ)).toNat := by
  simp [toNat, ofInt, modulus]

/-- Signed reinterpretation of an integer is its balanced residue at the word modulus. -/
@[simp]
theorem toSignedInt_ofInt (n : ℤ) :
    toSignedInt (ofInt n : α) = n.bmod (modulus width) := by
  simp [toSignedInt, ofInt, modulus]

/-- The unsigned value of zero is zero. -/
@[simp]
theorem toNat_zero : toNat (0 : α) = 0 := by
  simp [toNat]

/-- The unsigned value of one is one for every nonempty word. -/
@[simp]
theorem toNat_one (h : 0 < width := by omega) : toNat (1 : α) = 1 := by
  change toNat (ofNat 1 : α) = 1
  rw [toNat_ofNat, Nat.mod_eq_of_lt]
  simpa [modulus] using Nat.one_lt_two_pow (Nat.ne_of_gt h)

/-- Signed reinterpretation maps the zero word to zero. -/
@[simp]
theorem toSignedInt_zero : toSignedInt (0 : α) = 0 := by
  simp [toSignedInt]

/-- Converting a fixed-width value to a natural and back is lossless. -/
@[simp]
theorem ofNat_toNat (value : α) : ofNat (toNat value) = value := by
  apply toNat_injective
  rw [toNat_ofNat, Nat.mod_eq_of_lt]
  exact (FixedUInt.toBitVec value).isLt

/-- Every unsigned value is smaller than its word modulus. -/
theorem toNat_lt_modulus (value : α) : toNat value < modulus width :=
  (FixedUInt.toBitVec value).isLt

/-- Checked natural construction succeeds exactly for representable values. -/
theorem ofNat?_eq_some_iff {n : ℕ} {value : α} :
    ofNat? n = some value ↔ n < modulus width ∧ ofNat n = value := by
  simp only [ofNat?]
  split <;> simp_all

/-- Checked natural construction rejects exactly the out-of-range values. -/
@[simp]
theorem ofNat?_eq_none_iff (n : ℕ) :
    (ofNat? n : Option α) = none ↔ modulus width ≤ n := by
  simp [ofNat?]

/-- Checked integer construction succeeds exactly for nonnegative representable values. -/
theorem ofInt?_eq_some_iff {n : ℤ} {value : α} :
    ofInt? n = some value ↔
      0 ≤ n ∧ n < (modulus width : ℤ) ∧ ofNat n.toNat = value := by
  simp only [ofInt?]
  split <;> simp_all

/-- Checked integer construction rejects negative and out-of-range values. -/
@[simp]
theorem ofInt?_eq_none_iff (n : ℤ) :
    (ofInt? n : Option α) = none ↔
      n < 0 ∨ (modulus width : ℤ) ≤ n := by
  simp only [ofInt?]
  split_ifs with h
  · simp only [false_iff]
    exact not_or_intro (not_lt.mpr h.1) (not_le.mpr h.2)
  · simp only [true_iff]
    rcases not_and_or.mp h with hnegative | hlarge
    · exact Or.inl (lt_of_not_ge hnegative)
    · exact Or.inr (le_of_not_gt hlarge)

/-- The greatest fixed-width value is `2 ^ width - 1`. -/
@[simp]
theorem toNat_max : toNat (max : α) = modulus width - 1 := by
  simp [toNat, max, modulus]

/-- Addition is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_add (a b : α) :
    FixedUInt.toBitVec (a + b) = FixedUInt.toBitVec a + FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a + FixedUInt.toBitVec b)) = _
  simp

/-- Subtraction is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_sub (a b : α) :
    FixedUInt.toBitVec (a - b) = FixedUInt.toBitVec a - FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a - FixedUInt.toBitVec b)) = _
  simp

/-- Multiplication is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_mul (a b : α) :
    FixedUInt.toBitVec (a * b) = FixedUInt.toBitVec a * FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a * FixedUInt.toBitVec b)) = _
  simp

/-- Negation is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_neg (value : α) :
    FixedUInt.toBitVec (-value) = -FixedUInt.toBitVec value := by
  change FixedUInt.toBitVec (FixedUInt.ofBitVec (-FixedUInt.toBitVec value)) = _
  simp

/-- Natural scalar multiplication is preserved by the exact-width representation. -/
theorem toBitVec_nsmul (n : ℕ) (value : α) :
    FixedUInt.toBitVec (n • value) = n • FixedUInt.toBitVec value := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (n • FixedUInt.toBitVec value)) = _
  simp

/-- Integer scalar multiplication is preserved by the exact-width representation. -/
theorem toBitVec_zsmul (n : ℤ) (value : α) :
    FixedUInt.toBitVec (n • value) = n • FixedUInt.toBitVec value := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (n • FixedUInt.toBitVec value)) = _
  simp

/-- Wrapping arithmetic forms a commutative ring modulo `2 ^ width`. -/
instance : CommRing α :=
  Function.Injective.commRing FixedUInt.toBitVec toBitVec_injective
    toBitVec_zero toBitVec_one toBitVec_add toBitVec_mul toBitVec_neg toBitVec_sub
    toBitVec_nsmul toBitVec_zsmul toBitVec_pow toBitVec_natCast toBitVec_intCast

/-- Addition wraps modulo the word modulus. -/
@[simp]
theorem toNat_add (a b : α) :
    toNat (a + b) = (toNat a + toNat b) % modulus width :=
  by
    change toNat (wrappingAdd a b) = (toNat a + toNat b) % modulus width
    unfold toNat wrappingAdd modulus
    rw [toBitVec_ofBitVec]
    rfl

/-- Subtraction wraps modulo the word modulus. -/
@[simp]
theorem toNat_sub (a b : α) :
    toNat (a - b) = ((modulus width - toNat b) + toNat a) % modulus width :=
  by
    change toNat (wrappingSub a b) =
      ((modulus width - toNat b) + toNat a) % modulus width
    unfold toNat wrappingSub modulus
    rw [toBitVec_ofBitVec]
    rfl

/-- Multiplication wraps modulo the word modulus. -/
@[simp]
theorem toNat_mul (a b : α) :
    toNat (a * b) = (toNat a * toNat b) % modulus width :=
  by
    change toNat (wrappingMul a b) = (toNat a * toNat b) % modulus width
    unfold toNat wrappingMul modulus
    rw [toBitVec_ofBitVec]
    rfl

/-- Negation wraps modulo the word modulus. -/
@[simp]
theorem toNat_neg (value : α) :
    toNat (-value) = (modulus width - toNat value) % modulus width := by
  change toNat (wrappingNeg value) =
    (modulus width - toNat value) % modulus width
  unfold toNat wrappingNeg modulus
  rw [toBitVec_ofBitVec]
  exact BitVec.toNat_neg _

/-- Bitwise complement is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_complement (value : α) :
    FixedUInt.toBitVec (~~~value) = ~~~FixedUInt.toBitVec value := by
  change FixedUInt.toBitVec (FixedUInt.ofBitVec (~~~FixedUInt.toBitVec value)) = _
  simp

/-- Bitwise conjunction is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_and (a b : α) :
    FixedUInt.toBitVec (a &&& b) = FixedUInt.toBitVec a &&& FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a &&& FixedUInt.toBitVec b)) = _
  simp

/-- Bitwise disjunction is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_or (a b : α) :
    FixedUInt.toBitVec (a ||| b) = FixedUInt.toBitVec a ||| FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a ||| FixedUInt.toBitVec b)) = _
  simp

/-- Bitwise exclusive-or is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_xor (a b : α) :
    FixedUInt.toBitVec (a ^^^ b) = FixedUInt.toBitVec a ^^^ FixedUInt.toBitVec b := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec a ^^^ FixedUInt.toBitVec b)) = _
  simp

/-- Left shift is preserved below the width and is zero for every larger amount. -/
@[simp]
theorem toBitVec_shiftLeft (value : α) (amount : ℕ) :
    FixedUInt.toBitVec (value <<< amount) =
      if amount < width then FixedUInt.toBitVec value <<< amount else 0 := by
  simp only [HShiftLeft.hShiftLeft]
  split <;> simp_all [ofNat]

/-- Logical right shift is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_shiftRight (value : α) (amount : ℕ) :
    FixedUInt.toBitVec (value >>> amount) = FixedUInt.toBitVec value >>> amount := by
  change FixedUInt.toBitVec
    (FixedUInt.ofBitVec (FixedUInt.toBitVec value >>> amount)) = _
  simp

/-- A left shift by at least the word width is zero without evaluating a huge shift. -/
@[simp]
theorem shiftLeft_eq_zero_of_width_le (value : α) (amount : ℕ) (h : width ≤ amount) :
    value <<< amount = 0 := by
  change value <<< amount = ofNat 0
  apply toBitVec_injective
  simp [Nat.not_lt.mpr h]

/-- A logical right shift by at least the word width is zero. -/
@[simp]
theorem shiftRight_eq_zero_of_width_le (value : α) (amount : ℕ) (h : width ≤ amount) :
    value >>> amount = 0 := by
  change value >>> amount = ofNat 0
  apply toBitVec_injective
  simp [BitVec.ushiftRight_eq_zero h]

/-- Bitwise complement has the expected unsigned value. -/
@[simp]
theorem toNat_complement (value : α) :
    toNat (~~~value) = modulus width - 1 - toNat value := by
  simp [toNat, modulus]

/-- Bitwise conjunction agrees with natural-number conjunction. -/
@[simp]
theorem toNat_and (a b : α) : toNat (a &&& b) = toNat a &&& toNat b := by
  simp [toNat]

/-- Bitwise disjunction agrees with natural-number disjunction. -/
@[simp]
theorem toNat_or (a b : α) : toNat (a ||| b) = toNat a ||| toNat b := by
  simp [toNat]

/-- Bitwise exclusive-or agrees with natural-number exclusive-or. -/
@[simp]
theorem toNat_xor (a b : α) : toNat (a ^^^ b) = toNat a ^^^ toNat b := by
  simp [toNat]

/-- Testing a conjunction tests both operands at the same bit. -/
@[simp]
theorem testBit_and (a b : α) (index : ℕ) :
    testBit (a &&& b) index = (testBit a index && testBit b index) := by
  simp [testBit]

/-- Testing a disjunction tests either operand at the same bit. -/
@[simp]
theorem testBit_or (a b : α) (index : ℕ) :
    testBit (a ||| b) index = (testBit a index || testBit b index) := by
  simp [testBit]

/-- Testing an exclusive-or compares the operand bits. -/
@[simp]
theorem testBit_xor (a b : α) (index : ℕ) :
    testBit (a ^^^ b) index = xor (testBit a index) (testBit b index) := by
  simp [testBit]

/-- Complement negates in-range bits and leaves out-of-range bits false. -/
@[simp]
theorem testBit_complement (value : α) (index : ℕ) :
    testBit (~~~value) index =
      (decide (index < width) && !testBit value index) := by
  simp [testBit]

/-- A bounded left shift agrees with natural-number shifting modulo the word modulus. -/
theorem toNat_shiftLeft_of_lt (value : α) (amount : ℕ) (h : amount < width) :
    toNat (value <<< amount) = (toNat value <<< amount) % modulus width := by
  simp [toNat, h, modulus]

/-- Logical right shift agrees with natural-number shifting. -/
@[simp]
theorem toNat_shiftRight (value : α) (amount : ℕ) :
    toNat (value >>> amount) = toNat value >>> amount := by
  simp [toNat]

/-- Left rotation is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_rotateLeft (value : α) (amount : ℕ) :
    FixedUInt.toBitVec (rotateLeft value amount) =
      (FixedUInt.toBitVec value).rotateLeft amount := by
  simp [rotateLeft]

/-- Right rotation is preserved by the exact-width representation. -/
@[simp]
theorem toBitVec_rotateRight (value : α) (amount : ℕ) :
    FixedUInt.toBitVec (rotateRight value amount) =
      (FixedUInt.toBitVec value).rotateRight amount := by
  simp [rotateRight]

/-- Left rotation depends only on the amount modulo the word width. -/
theorem rotateLeft_mod (value : α) (amount : ℕ) :
    rotateLeft value (amount % width) = rotateLeft value amount := by
  apply toBitVec_injective
  simp [BitVec.rotateLeft_mod_eq_rotateLeft]

/-- Right rotation depends only on the amount modulo the word width. -/
theorem rotateRight_mod (value : α) (amount : ℕ) :
    rotateRight value (amount % width) = rotateRight value amount := by
  apply toBitVec_injective
  simp [BitVec.rotateRight_mod_eq_rotateRight]

/-- The overflow flag for addition has its stated arithmetic meaning. -/
@[simp]
theorem addOverflow_eq_true (a b : α) :
    addOverflow a b = true ↔ modulus width ≤ toNat a + toNat b := by
  simp [addOverflow]

/-- The underflow flag for subtraction has its stated arithmetic meaning. -/
@[simp]
theorem subOverflow_eq_true (a b : α) :
    subOverflow a b = true ↔ toNat a < toNat b := by
  simp [subOverflow]

/-- The overflow flag for multiplication has its stated arithmetic meaning. -/
@[simp]
theorem mulOverflow_eq_true (a b : α) :
    mulOverflow a b = true ↔ modulus width ≤ toNat a * toNat b := by
  simp [mulOverflow]

/-- The value component of overflowing addition is the wrapping sum. -/
@[simp]
theorem overflowingAdd_fst (a b : α) : (overflowingAdd a b).1 = a + b :=
  rfl

/-- The flag component of overflowing addition records exact overflow. -/
@[simp]
theorem overflowingAdd_snd (a b : α) :
    (overflowingAdd a b).2 = decide (modulus width ≤ toNat a + toNat b) :=
  rfl

/-- The value component of overflowing subtraction is the wrapping difference. -/
@[simp]
theorem overflowingSub_fst (a b : α) : (overflowingSub a b).1 = a - b :=
  rfl

/-- The flag component of overflowing subtraction records exact underflow. -/
@[simp]
theorem overflowingSub_snd (a b : α) :
    (overflowingSub a b).2 = decide (toNat a < toNat b) :=
  rfl

/-- The value component of overflowing multiplication is the wrapping product. -/
@[simp]
theorem overflowingMul_fst (a b : α) : (overflowingMul a b).1 = a * b :=
  rfl

/-- The flag component of overflowing multiplication records exact overflow. -/
@[simp]
theorem overflowingMul_snd (a b : α) :
    (overflowingMul a b).2 = decide (modulus width ≤ toNat a * toNat b) :=
  rfl

/-- Checked addition succeeds when the exact sum fits. -/
theorem checkedAdd_eq_some_of_lt (a b : α)
    (h : toNat a + toNat b < modulus width) :
    checkedAdd a b = some (a + b) := by
  change checkedAdd a b = some (wrappingAdd a b)
  simp [checkedAdd, addOverflow, Nat.not_le.mpr h]

/-- Checked addition fails exactly on overflow. -/
@[simp]
theorem checkedAdd_eq_none_iff (a b : α) :
    checkedAdd a b = none ↔ modulus width ≤ toNat a + toNat b := by
  simp [checkedAdd, addOverflow]

/-- Checked subtraction succeeds when the result is nonnegative. -/
theorem checkedSub_eq_some_of_le (a b : α) (h : toNat b ≤ toNat a) :
    checkedSub a b = some (a - b) := by
  change checkedSub a b = some (wrappingSub a b)
  simp [checkedSub, subOverflow, Nat.not_lt.mpr h]

/-- Checked subtraction fails exactly on underflow. -/
@[simp]
theorem checkedSub_eq_none_iff (a b : α) :
    checkedSub a b = none ↔ toNat a < toNat b := by
  simp [checkedSub, subOverflow]

/-- Checked multiplication succeeds when the exact product fits. -/
theorem checkedMul_eq_some_of_lt (a b : α)
    (h : toNat a * toNat b < modulus width) :
    checkedMul a b = some (a * b) := by
  change checkedMul a b = some (wrappingMul a b)
  simp [checkedMul, mulOverflow, Nat.not_le.mpr h]

/-- Checked multiplication fails exactly on overflow. -/
@[simp]
theorem checkedMul_eq_none_iff (a b : α) :
    checkedMul a b = none ↔ modulus width ≤ toNat a * toNat b := by
  simp [checkedMul, mulOverflow]

/-- Checked division fails exactly for a zero divisor. -/
@[simp]
theorem checkedDiv_eq_none_iff (a b : α) : checkedDiv a b = none ↔ toNat b = 0 := by
  simp [checkedDiv]

/-- Checked remainder fails exactly for a zero divisor. -/
@[simp]
theorem checkedMod_eq_none_iff (a b : α) : checkedMod a b = none ↔ toNat b = 0 := by
  simp [checkedMod]

/-- Checked division returns the natural-number quotient for a nonzero divisor. -/
theorem checkedDiv_eq_some_of_ne_zero (a b : α) (h : toNat b ≠ 0) :
    checkedDiv a b = some (ofNat (toNat a / toNat b)) := by
  simp [checkedDiv, h]

/-- Checked remainder returns the natural-number remainder for a nonzero divisor. -/
theorem checkedMod_eq_some_of_ne_zero (a b : α) (h : toNat b ≠ 0) :
    checkedMod a b = some (ofNat (toNat a % toNat b)) := by
  simp [checkedMod, h]

/-- Checked quotient and remainder fail exactly for a zero divisor. -/
@[simp]
theorem checkedDivMod_eq_none_iff (a b : α) :
    checkedDivMod a b = none ↔ toNat b = 0 := by
  by_cases h : toNat b = 0
  · simp [checkedDivMod, checkedDiv, checkedMod, h]
  · simp [checkedDivMod, checkedDiv, checkedMod, h]

/-- Checked quotient and remainder expose the Euclidean decomposition. -/
theorem checkedDivMod_eq_some_of_ne_zero (a b : α) (h : toNat b ≠ 0) :
    checkedDivMod a b =
      some (ofNat (toNat a / toNat b), ofNat (toNat a % toNat b)) := by
  simp [checkedDivMod, checkedDiv, checkedMod, h]

/-- Saturating addition returns the maximum value on overflow. -/
theorem saturatingAdd_eq_max_of_overflow (a b : α)
    (h : modulus width ≤ toNat a + toNat b) :
    saturatingAdd a b = max := by
  simp [saturatingAdd, addOverflow, h]

/-- Saturating addition agrees with wrapping addition when the exact sum fits. -/
theorem saturatingAdd_eq_add_of_lt (a b : α)
    (h : toNat a + toNat b < modulus width) :
    saturatingAdd a b = a + b := by
  change saturatingAdd a b = wrappingAdd a b
  simp [saturatingAdd, addOverflow, Nat.not_le.mpr h]

/-- Saturating subtraction returns zero on underflow. -/
theorem saturatingSub_eq_zero_of_lt (a b : α) (h : toNat a < toNat b) :
    saturatingSub a b = 0 := by
  change saturatingSub a b = ofNat 0
  simp [saturatingSub, subOverflow, h]

/-- Saturating subtraction agrees with wrapping subtraction without underflow. -/
theorem saturatingSub_eq_sub_of_le (a b : α) (h : toNat b ≤ toNat a) :
    saturatingSub a b = a - b := by
  change saturatingSub a b = wrappingSub a b
  simp [saturatingSub, subOverflow, Nat.not_lt.mpr h]

/-- Saturating multiplication returns the maximum value on overflow. -/
theorem saturatingMul_eq_max_of_overflow (a b : α)
    (h : modulus width ≤ toNat a * toNat b) :
    saturatingMul a b = max := by
  simp [saturatingMul, mulOverflow, h]

/-- Saturating multiplication agrees with wrapping multiplication when the product fits. -/
theorem saturatingMul_eq_mul_of_lt (a b : α)
    (h : toNat a * toNat b < modulus width) :
    saturatingMul a b = a * b := by
  change saturatingMul a b = wrappingMul a b
  simp [saturatingMul, mulOverflow, Nat.not_le.mpr h]

/-- The population count never exceeds the bit width. -/
theorem countOnes_le_width (value : α) : countOnes value ≤ width :=
  BitVec.toNat_cpop_le _

/-- The leading-zero count never exceeds the bit width. -/
theorem leadingZeros_le_width (value : α) : leadingZeros value ≤ width := by
  simpa [leadingZeros, BitVec.le_def] using
    (BitVec.clz_le (x := FixedUInt.toBitVec value))

/-- The trailing-zero count never exceeds the bit width. -/
theorem trailingZeros_le_width (value : α) : trailingZeros value ≤ width := by
  simpa [trailingZeros, BitVec.ctz_eq_reverse_clz, BitVec.le_def] using
    (BitVec.clz_le (x := (FixedUInt.toBitVec value).reverse))

/-- Unsigned order agrees with natural-number order. -/
@[simp]
theorem lt_iff_toNat_lt (a b : α) : a < b ↔ toNat a < toNat b :=
  Iff.rfl

/-- Unsigned non-strict order agrees with natural-number order. -/
@[simp]
theorem le_iff_toNat_le (a b : α) : a ≤ b ↔ toNat a ≤ toNat b :=
  Iff.rfl

end FixedUInt

/-- A nominal 64-bit unsigned integer for bounded Ethereum counters and gas quantities. -/
@[ext]
structure U64 where
  /-- The exact 64-bit representation. -/
  val : BitVec 64
  deriving Repr, Hashable

/-- A nominal 128-bit unsigned integer for Rust and host-runtime quantities. -/
@[ext]
structure U128 where
  /-- The exact 128-bit representation. -/
  val : BitVec 128
  deriving Repr, Hashable

/-- A nominal 256-bit unsigned integer used for EVM words and Ethereum quantities. -/
@[ext]
structure U256 where
  /-- The exact 256-bit representation. -/
  val : BitVec 256
  deriving Repr, Hashable

/-- Exact-width representation for `U64`. -/
instance : FixedUInt U64 64 where
  toBitVec := U64.val
  ofBitVec := U64.mk
  of_to := by intro; rfl
  to_of := by intro; rfl

/-- Exact-width representation for `U128`. -/
instance : FixedUInt U128 128 where
  toBitVec := U128.val
  ofBitVec := U128.mk
  of_to := by intro; rfl
  to_of := by intro; rfl

/-- Exact-width representation for `U256`. -/
instance : FixedUInt U256 256 where
  toBitVec := U256.val
  ofBitVec := U256.mk
  of_to := by intro; rfl
  to_of := by intro; rfl

/-- The generic representation of a `U64` is its stored bit vector. -/
@[simp]
theorem U64.toBitVec_eq_val (value : U64) : FixedUInt.toBitVec value = value.val :=
  rfl

/-- The generic representation of a `U128` is its stored bit vector. -/
@[simp]
theorem U128.toBitVec_eq_val (value : U128) : FixedUInt.toBitVec value = value.val :=
  rfl

/-- The generic representation of a `U256` is its stored bit vector. -/
@[simp]
theorem U256.toBitVec_eq_val (value : U256) : FixedUInt.toBitVec value = value.val :=
  rfl

end Lean4EVM
