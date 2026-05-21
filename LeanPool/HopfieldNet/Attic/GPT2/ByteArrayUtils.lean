/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.LLM.GPT2.Core

namespace LLM.GPT2.ByteArray

open Batteries
open LLM.GPT2

--  Section 2: Optimized ByteArray Float I/O

/--
Reads a Float from a ByteArray at the given offset in Little Endian format.
Assumes offset is valid and aligned for performance.
Uses direct byte manipulation instead of `extract`.
Returns `none` if the read would go beyond the array bounds.
-/
@[inline]
def readFloatLE? (b : ByteArray) (o : Nat) : Option Float :=
  if o + bytesPerFloat ≤ b.size then
    let b0 := UInt64.ofNat (b.get! o).toNat
    let b1 := UInt64.ofNat (b.get! (o+1)).toNat
    let b2 := UInt64.ofNat (b.get! (o+2)).toNat
    let b3 := UInt64.ofNat (b.get! (o+3)).toNat
    let b4 := UInt64.ofNat (b.get! (o+4)).toNat
    let b5 := UInt64.ofNat (b.get! (o+5)).toNat
    let b6 := UInt64.ofNat (b.get! (o+6)).toNat
    let b7 := UInt64.ofNat (b.get! (o+7)).toNat
    let u64val := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
                  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)
    some (Float.ofBits u64val)
  else none

/--
Writes a Float value to a ByteArray at the given offset in Little Endian format.
Will panic if the write goes beyond the array bounds (`set!` panics).
Assumes offset is valid and aligned for performance.
-/
@[inline]
def writeFloatLE! (b : ByteArray) (o : Nat) (v : Float) : ByteArray := Id.run do
  let u64val := Float.toUInt64 v
  let mut new_b := b
  new_b := new_b.set! o         (u64val >>> 0).toUInt8
  new_b := new_b.set! (o + 1) (u64val >>> 8).toUInt8
  new_b := new_b.set! (o + 2) (u64val >>> 16).toUInt8
  new_b := new_b.set! (o + 3) (u64val >>> 24).toUInt8
  new_b := new_b.set! (o + 4) (u64val >>> 32).toUInt8
  new_b := new_b.set! (o + 5) (u64val >>> 40).toUInt8
  new_b := new_b.set! (o + 6) (u64val >>> 48).toUInt8
  new_b := new_b.set! (o + 7) (u64val >>> 56).toUInt8
  return new_b

end LLM.GPT2.ByteArray
