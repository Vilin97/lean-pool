/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

import LeanPool.Cryptography.Hashes.SHA3.Lemmas

/-!
# SHA-3 Permutation-Based Hash and Extendable-Output Functions

## Description

This file implements four cryptographic hash functions, SHA3-224,
SHA3-256, SHA3-384, and SHA3-512, and two extendable-output functions
(XOFs), SHAKE128 and SHAKE256 of the SHA-3 family of functions in Lean
4.

It provides one-shot, and streaming APIs.

## Implementation Notes

⚠️ The implementation assumes little-endian, 64 bit word size
architecture, which is what Lean4 currently supports.

It operates on Lean `ByteArray` input for now, and returns `ByteArray`
output.

The SHA-3 instances are exposed as `SHA3.sha224`, `SHA3.sha256`, `SHA3.sha384`,
and `SHA3.sha512`; the SHAKE instances are exposed as `SHAKE128` and `SHAKE256`.
They support the relevant API operations such as `update()`, `final()`, and
`squeeze()` through dot notation.

## Tags

SHA-3 Keccak SHA3-224 SHA3-256 SHA3-384 SHA3-512 XOF SHAKE128 SHAKE256
-/

namespace Cryptography

private def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

-- An array of 25 UInt64 values
private abbrev Arr25 := { val : Array UInt64 // val.size = 25}
private abbrev State := Arr25

-- An array of 5 UInt64 values
private abbrev Arr5 := { val : Array UInt64 // val.size = 5}

private def rotationValues : Arr25 :=
  ⟨ #[0, 63, 2, 36, 37, 28, 20, 58, 9, 44, 61, 54, 21, 39, 25, 23, 19,
   49, 43, 56, 46, 62, 3, 8, 50], by decide ⟩

@[always_inline, inline] private def mkState : State :=
  ⟨ Array.replicate 25 0, by decide ⟩

instance : GetElem Arr25 Nat UInt64 (λ _ i ↦ i < 25) where
  getElem state idx _ :=  state.val[idx]

instance : GetElem Arr5 Nat UInt64 (λ _ i ↦ i < 5) where
  getElem arr5 idx _ :=  arr5.val[idx]

-- proof that array size does not change upon modification
@[always_inline,inline] private def subtypeModify.{u} {α : Type u} {n : Nat} (xs : { val : Array α  // val.size = n }) (i : Nat) (elem: α  ) : { a : Array α  // a.size = n } :=
  let val := xs.val.modify i (λ _ => elem)
  ⟨val, (xs.val.size_modify) ▸ xs.property⟩


-- max capacity for all SHA3/Shake instances (1024 / 8 + 1)
-- This permits to prove that internal buffer access is within bounds later
-- Careful, always instantiate `Capacity` with a proof, as OfNat uses `%`
private abbrev Capacity := Fin 129

/-- Sponge function, defined by its capacity, padding, and output bit length -/
structure HashFunction where private ofParams ::
  /-- The sponge capacity in bytes; the rate is derived as `200 - capacity`. -/
  capacity : Capacity
  /-- The domain-separation padding delimiter byte (`0x06` for SHA-3, `0x1f` for SHAKE). -/
  paddingDelimiter : Nat
  /-- The fixed number of output bits produced by the hash function. -/
  outputBitsLen : Nat

private inductive SpongeState where
  | absorbing
  | squeezing

-- Needed for Repr'esenting `KeccakC` buffer
private instance : Repr ByteArray where
  reprPrec d _ := repr d.data

private def KeccakPPermutationSize := 200

-- We make rate a finite type `Rate`, so we can prove that array accesses
-- using an index derived from rate (and capacity) are within bounds
-- Rate is b - c so < (1600/8) - c + 1
private abbrev RateValue (capacity : Capacity) := Fin (KeccakPPermutationSize - capacity + 1 )

-- An index into `buffer` rate of buffer, where buffer is broken down into |rate|capacity|
private abbrev RateIndex (capacity : Capacity) := Fin (KeccakPPermutationSize - capacity )

theorem RateIndexLTBlockMinCap {n : Capacity} (ri : RateIndex n) : ri < KeccakPPermutationSize - n := by
  omega

theorem RateIndexLTBlockMinCapMinOne
  {n : Capacity}
  (ri : RateIndex n)
  (h1 : ¬(ri == KeccakPPermutationSize - n - 1) = true)
  : ri + 1 < KeccakPPermutationSize - n := by
  simp at h1
  have h2 : ri < KeccakPPermutationSize - n :=   (by exact RateIndexLTBlockMinCap ri);
  refine Nat.add_lt_of_lt_sub ?h
  omega

private abbrev FixedBuffer := {val : ByteArray // val.size =  KeccakPPermutationSize }

@[simp] theorem FixedBufferSize (fb : FixedBuffer):  fb.val.size = KeccakPPermutationSize := by exact fb.2

@[always_inline,inline] private def mkFixedBuffer : FixedBuffer  :=
    ⟨ ByteArray.mk (Array.replicate KeccakPPermutationSize 0),
      by simp [KeccakPPermutationSize, ByteArray.size, Array.size_replicate] ⟩

-- theorem `size_set` from: https://github.com/leanprover-community/batteries/blob/ad3ba5ff13913874b80146b54d0a4e5b9b739451/Batteries/Data/ByteArray.lean#L51
/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
@[simp] theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size :=
  Array.size_set h

@[always_inline,inline] private def fixedBufferModify (fb : FixedBuffer) (i : Fin fb.val.size) (elem: UInt8) : FixedBuffer :=
  let val := fb.val.set i  elem
  ⟨val, by rw [size_set]; exact fb.2⟩

instance : GetElem (FixedBuffer) Nat UInt8 (λ fb i ↦ i < fb.val.size ) where
  getElem fb idx h :=  fb.val[idx]

/-- The base cryptographic sponge context -/
private structure KeccakC (hf : HashFunction)  where
  A  : State
  state : SpongeState := SpongeState.absorbing
  rate : RateValue hf.capacity := ⟨ 0, by omega ⟩
  buffer  : FixedBuffer
  bufPos : RateIndex hf.capacity := ⟨ 0, by simp [KeccakPPermutationSize]; omega ⟩
  outputBytesLen := 0
  lastReadPos : RateValue hf.capacity := ⟨ 0, by omega  ⟩

private def mkKeccakCBase (hf : HashFunction) : KeccakC hf :=
  let A  := mkState
  let rate : RateValue hf.capacity := ⟨ KeccakPPermutationSize - hf.capacity, by omega ⟩ --  KECCAK[c] b=1600
  let buffer := mkFixedBuffer
  {A := A, rate := rate, outputBytesLen := hf.outputBitsLen, buffer := buffer }

-- We define two possible sponge contexts, implemented as subtypes:
-- `AbsorbingKeccakC` : our sponge is absorbing
-- `SqueezingKeccakC` : our sponge is squeezing
-- subtypes require a proof that their properties hold
private def AbsorbingKeccakC (hf : HashFunction) : Type := {keccak : KeccakC hf // keccak.state = SpongeState.absorbing}
private def SqueezingKeccakC (hf : HashFunction) : Type := {keccak : KeccakC hf // keccak.state = SpongeState.squeezing}

/-- Instantiate a fresh sponge context for a hash function; it always starts in
the absorbing state. -/
def HashFunction.mk (hf : HashFunction) : {keccak : KeccakC hf // keccak.state = SpongeState.absorbing}  :=
  let base := {mkKeccakCBase hf with state := SpongeState.absorbing}
  ⟨base, rfl⟩

@[always_inline, inline] private def rotateBy (x: UInt64) (howMuch : UInt64) : UInt64 :=
  (x >>> howMuch) ||| (x <<< (64 - howMuch))

/--
The steps that comprise a round of KECCAK-p[b, nr] are denoted by θ,
ρ, π, χ, and ι.
-/

-- theta
private def θ (A : State) : State := Id.run do
  let mut C : Arr5 := ⟨ Array.replicate 5 0, by decide ⟩
  let mut D : Arr5 := ⟨ Array.replicate 5 0, by decide ⟩
  let mut A := A

  for hx : x in [:5] do
    C := subtypeModify C x
          ( A[x    ]'(StateIndexWithinBounds521 x 0 hx (by trivial)) ^^^
            A[x + 5 ]'(StateIndexWithinBounds521 x 5 hx (by trivial)) ^^^
            A[x + 10]'(StateIndexWithinBounds521 x 10 hx (by trivial))  ^^^
            A[x + 15]'(StateIndexWithinBounds521 x 15 hx (by trivial)) ^^^
            A[x + 20]'(StateIndexWithinBounds521 x 20 hx (by trivial)))
  for hx : x in [:5] do
    D := subtypeModify D x
          ( C[(x + 4) % 5] ^^^
            ((((C[(x + 1) % 5]) <<< 1) |||
            ((C[(x + 1) % 5]) >>> 63)))) -- Lean's `%` is remainder, not modulo
    for hy : y in [:5] do
      A := subtypeModify A (x + 5 * y)
            ( (A[(x + 5 * y)]'(StateIndexWithinBounds55 x y hx hy)  ^^^
            (D[x])))

  A

-- rho pi
-- we apply ρ, and π in the same loop
private def ρπ (A : State) : State := Id.run do
  let mut A' := mkState
  for hx : x in [:5] do
    for hy : y in [:5] do
      let i := (x + 3 * y) % 5 + 5 * x
      A' := subtypeModify A' (x + 5 * y)
              (rotateBy (A[i]'(StateIndexWithinBounds55' i hx hy (by trivial)))
                (rotationValues[i]'(StateIndexWithinBounds55' i hx hy (by trivial))))
  A'

-- chi
private def χ (A' : State) : State := Id.run do
  let mut A := A'
  for hx : x in [:5] do
    have phx : x < 5 := hx.2.1
    for hy : y in [:5] do
      have phy : y < 5 := hy.2.1
      A := subtypeModify A (x + 5 * y)
            (A'[x + 5 * y]'(by omega) ^^^
            ((A'[(x + 1) % 5 + 5 * y]'(by omega) ^^^
            0xffffffffffffffff) &&&
            (A'[(x + 2) %5 + 5 * y]'(by omega) )))
  A

-- iota
@[always_inline,inline] private def ι (A : State) (ir : Nat) (h : ir < roundConstants.size) : State := Id.run do
  subtypeModify A 0 ((A[0]) ^^^ (roundConstants[ir]'h ))

/--
The KECCAK-p[b, nr] permutation consists of nr iterations of:
Rnd(A, ir) = iota(chi(π(ρ(theta(A)))), ir).
-/
@[always_inline,inline] private def keccakP (A : State) : State := Id.run do
  let mut A := A
  -- KECCAK[c] number round nr := 24
  for h :  round in [:roundConstants.size] do
    let ⟨_h₁, h₂⟩ := h -- h1 : col.start <= round, h2 := round < 25
    A :=  A |> θ |> ρπ |> χ |> (ι · round h₂.1  )
  A

private def storeUInt64 (num : UInt64) : ByteArray :=
  ByteArray.mk #[
    num.toUInt8,
    (num >>> 0x08).toUInt8,
    (num >>> 0x10).toUInt8,
    (num >>> 0x18).toUInt8,
    (num >>> 0x20).toUInt8,
    (num >>> 0x28).toUInt8,
    (num >>> 0x30).toUInt8,
    (num >>> 0x38).toUInt8
  ]

@[always_inline,inline] private def FixedBuffer.toUInt64LE  (fb : FixedBuffer) (index : Nat) (h : 7 + index < fb.val.size  ) : UInt64 :=
  (fb.val[7 + index]'(by rw [fb.2]; omega )).toUInt64 <<< 0x38 |||
  (fb.val[6 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x30 |||
  (fb.val[5 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x28 |||
  (fb.val[4 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x20 |||
  (fb.val[3 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x18 |||
  (fb.val[2 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x10 |||
  (fb.val[1 + index]'(by rw [fb.2]; omega )).toUInt64  <<< 0x8  |||
  (fb.val[0 + index]'(by rw [fb.2]; omega )).toUInt64

private class Absorb (α : Type) (β : Type) where
  absorb : α  → β →  α

-- We force the caller to prove that RateIndex pos + offset will not silently wrap as RateIndex is a Fin.
-- if the implementation is correct, it should not happen but want to avoid
@[always_inline,inline] private def RateIndex.add
  {n} (pos offset : RateIndex n)
  (_ : pos + offset < KeccakPPermutationSize - n ) :=
  pos + offset

private def absorb
  {hf : HashFunction}
  (k : AbsorbingKeccakC hf)
  (inputBytes : ByteArray)
  : AbsorbingKeccakC hf := Id.run do
  let mut k := k
  let mut buffer := k.val.buffer
  let mut bufPos := k.val.bufPos
  for hi : i in [:inputBytes.size] do
    buffer := fixedBufferModify buffer ⟨ bufPos, by omega⟩  inputBytes[i]
    if hif : bufPos.val == KeccakPPermutationSize - hf.capacity - 1 then
      let mut A := k.val.A
      for hj : j in [:25] do
        have phj : j < 25 := hj.2.1
        let start := j <<< 3 -- lane size = 8
        A := subtypeModify A j ((A[j]) ^^^
                                  (FixedBuffer.toUInt64LE buffer start (by simp [KeccakPPermutationSize]; omega)))
      k := ⟨{k.val with A := keccakP A, buffer := buffer, bufPos := ⟨ 0, by simp [KeccakPPermutationSize]; omega⟩}, k.property⟩
      bufPos := ⟨ 0, by simp [KeccakPPermutationSize]; omega⟩
    else
      bufPos := RateIndex.add  bufPos  ⟨ 1, by simp [KeccakPPermutationSize]; omega⟩ ( by exact RateIndexLTBlockMinCapMinOne bufPos hif)

  ⟨{k.val with buffer := buffer, bufPos := bufPos}, k.property⟩

instance {hf : HashFunction} : Absorb (AbsorbingKeccakC hf) ByteArray where
  absorb := absorb

private class Squeeze (α : Type) (β : Type) (γ : outParam Type) where
  squeeze : α  → β → γ

-- A block index `i` taken from the rate window `[0, (rate + 7) / 8)` is a valid
-- lane index into the 25-lane state, since the rate never exceeds the permutation
-- size of 200 bytes (so `(rate + 7) / 8 ≤ 25`).
theorem squeezeIndexBound {cap : Capacity} (rate : RateValue cap) (i : Nat)
    (h : i < (rate.val + 7) / 8) : i < 25 := by
  have := rate.isLt
  unfold KeccakPPermutationSize at *
  omega

-- As a learning exercise, we don't copy the whole state to a fixed size buffer and output that buffer on request
-- This necessitates generating output directly from a sliding window over the state array.
private def squeezeAbsorbedInput {hf : HashFunction} (k : SqueezingKeccakC hf) (len : Nat) : SqueezingKeccakC hf × ByteArray := Id.run do
  let mut k := k
  let mut output := ByteArray.emptyWithCapacity len

  let mut updatedOutputBytesLen := len

  let mut startingBlock := k.val.lastReadPos.val % k.val.rate / 8
  let mut startOffset := k.val.lastReadPos.val % 8

  if (k.val.lastReadPos.val = k.val.rate) then
    k := ⟨{k.val with A := keccakP k.val.A, lastReadPos := ⟨ 0, by omega⟩}, k.property⟩
    startingBlock := 0

  -- temp variable to aid within bounds array access proofs
  let mut newLastReadPos : RateValue hf.capacity := ⟨ 0, by omega⟩

  repeat do
    if hi : (updatedOutputBytesLen + k.val.lastReadPos) <= k.val.rate then
      newLastReadPos := ⟨ updatedOutputBytesLen + k.val.lastReadPos, by omega  ⟩
      break

    for hi : i in [startingBlock: (k.val.rate + 7) / 8] do
      have phi : i < (k.val.rate + 7) / 8 :=  hi.2.1
      output := output.append $ storeUInt64 (k.val.A[i]'(squeezeIndexBound k.val.rate i phi))

    updatedOutputBytesLen := updatedOutputBytesLen - (k.val.rate - k.val.lastReadPos)

    k := ⟨{k.val with A := keccakP k.val.A, lastReadPos := ⟨ 0, by omega⟩}, k.property⟩
    startingBlock := 0

  if updatedOutputBytesLen > 0 then
    for hi : i in [ startingBlock : (newLastReadPos + 7) / 8] do
      have phi : i <  (newLastReadPos + 7) / 8 :=  hi.2.1
      output := output.append $ storeUInt64 (k.val.A[i]'(squeezeIndexBound newLastReadPos i phi))

    k := ⟨{k.val with lastReadPos := ⟨ newLastReadPos, by omega⟩}, k.property⟩

  (k , output.extract startOffset (len + startOffset))

private instance {hf : HashFunction} : Squeeze (SqueezingKeccakC hf) Nat (Id (SqueezingKeccakC hf × ByteArray)) where
  squeeze  := squeezeAbsorbedInput

private def DomainDelimitAndPad101
  { n : Capacity }
  (buffer : FixedBuffer )
  (bufPos : RateIndex n)
  (rate : RateValue n)
  (paddingDelimiter : Nat)
  : FixedBuffer := Id.run do
  let mut buffer := buffer
  let q : RateValue n :=  ⟨ rate  - bufPos, by omega ⟩  -- padding bytes required
  if hq : q == 1 then
    buffer := fixedBufferModify buffer ⟨ bufPos, by omega ⟩  (paddingDelimiter + 0x80).toUInt8
  else
    buffer := fixedBufferModify buffer ⟨ bufPos, by omega ⟩  paddingDelimiter.toUInt8
    for hi : i in [bufPos + 1 : rate - 1 ] do
      have phi : i < rate - 1 := hi.2.1
      buffer := fixedBufferModify buffer ⟨ i, by omega ⟩  0
    buffer := fixedBufferModify buffer ⟨  rate - 1, by simp [KeccakPPermutationSize]; omega  ⟩  (0x80).toUInt8
  buffer

private def squeezeNotFullyAbsorbedInput {hf : HashFunction} (ak : AbsorbingKeccakC hf) (len : Nat) : SqueezingKeccakC hf × ByteArray := Id.run do
  let mut ak := ak
  -- absorb
  let buffer := DomainDelimitAndPad101 ak.val.buffer ak.val.bufPos ak.val.rate hf.paddingDelimiter
  let mut A := ak.val.A
  for hi : i in [:25] do
    have phi : i < 25 := hi.2.1
    let start := i <<< 3
    A := subtypeModify A i ((A[i]) ^^^
                              (FixedBuffer.toUInt64LE  buffer start (by simp [KeccakPPermutationSize]; omega)))
  ak := ⟨{ak.val with A := keccakP A, buffer := buffer}, ak.property⟩
  -- squeeze
  let sk : SqueezingKeccakC hf := ⟨ {ak.val with state := SpongeState.squeezing}, by trivial ⟩
  Squeeze.squeeze sk len

private instance {hf : HashFunction}  : Squeeze (AbsorbingKeccakC hf) Nat (Id (SqueezingKeccakC hf × ByteArray))  where
  squeeze := squeezeNotFullyAbsorbedInput

-- Implement the hash and xof function APIs.

namespace HashFunction

/-- Finalize an absorbing sponge: pad the buffered input and squeeze out the
configured number of output bytes. -/
def final {hf : HashFunction} (s : AbsorbingKeccakC hf) : ByteArray  :=
  (Squeeze.squeeze s s.val.outputBytesLen).2

/-- Absorb more input bytes into the running sponge state. -/
def update {hf : HashFunction} (s : AbsorbingKeccakC hf) (bs : ByteArray)  :=
  Absorb.absorb s bs

/-- One-shot hashing: absorb the whole input and squeeze the configured output. -/
def hashData {hf : HashFunction} (bs : ByteArray) : ByteArray :=
  let k : AbsorbingKeccakC hf := hf.mk
  (Squeeze.squeeze (Absorb.absorb k bs) k.val.outputBytesLen).2

end HashFunction

/-- An extendable-output function (XOF), modelled as a `HashFunction` whose output
length is requested at squeeze time rather than fixed in advance. -/
def XOF := HashFunction

namespace XOF

/-- Transition an absorbing XOF sponge into the squeezing state without producing
any output. -/
def toSqueezing {xof : XOF} (k : AbsorbingKeccakC xof) : SqueezingKeccakC xof :=
  (Squeeze.squeeze k 0).1

/-- Absorb more input bytes into a XOF sponge. -/
nonrec def absorb {xof : XOF} (s : AbsorbingKeccakC xof) (bs : ByteArray) : AbsorbingKeccakC xof :=
  absorb s bs

/-- Squeeze `l` output bytes from a XOF sponge. -/
def squeeze {xof : XOF} {α : Type} [Squeeze α Nat ((SqueezingKeccakC xof) × ByteArray)]
    (k : α) (l : Nat) : ((SqueezingKeccakC xof) × ByteArray)  :=
  Squeeze.squeeze k l

end XOF

-- Implement our hash, and xof functions

namespace SHA3

/-- The SHA3-224 hash function: capacity 56, padding delimiter `0x06`, 28-byte output. -/
def sha224 : HashFunction := HashFunction.ofParams 56 0x06 28

/-- The SHA3-256 hash function: capacity 64, padding delimiter `0x06`, 32-byte output. -/
def sha256 : HashFunction := HashFunction.ofParams 64 0x06 32

/-- The SHA3-384 hash function: capacity 96, padding delimiter `0x06`, 48-byte output. -/
def sha384 : HashFunction := HashFunction.ofParams 96 0x06 48

/-- The SHA3-512 hash function: capacity 128, padding delimiter `0x06`, 64-byte output. -/
def sha512 : HashFunction := HashFunction.ofParams 128 0x06 64

end SHA3

/-- The SHAKE128 extendable-output function: capacity 32, padding delimiter `0x1f`. -/
def SHAKE128 : XOF := HashFunction.ofParams 32 0x1f 32

/-- The SHAKE256 extendable-output function: capacity 64, padding delimiter `0x1f`. -/
def SHAKE256 : XOF := HashFunction.ofParams 64 0x1f 64

end Cryptography
