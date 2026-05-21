/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Batteries.Data.ByteArray
import Init.Data.Array.Bootstrap
import Batteries.Data.Fin.Basic
import Init.Data.Array.Lemmas
import Init.Data.List.Lemmas

open Decidable

namespace LLM.GPT2

--  Section 1: Core Constants and Types

/-- Number of bytes used to represent a Float value (64-bit double). -/
@[inline]
def bytesPerFloat : Nat := 8

/-- Basic dimension type, ensuring positivity. -/
structure Dim where
  val : Nat
  isPos : val > 0
  deriving Repr

instance : Coe Dim Nat where
  coe := Dim.val

/--
`TensorError` represents possible errors that can occur during tensor initialization or access operations.

Variants:
- `nameNotFound`: Raised when a tensor with the specified name cannot be found.
- `shapeMismatch`: Raised when the actual tensor rank does not match the expected rank.
- `negativeDimension`: Raised when a tensor shape contains a negative dimension.
- `indexOutOfBounds`: Raised when provided indices are out of bounds for the given tensor shape.
- `offsetNotAligned`: Raised when a memory offset is not aligned to the required boundary.
- `bufferSizeMismatch`: Raised when the buffer size does not match the expected size.
- `bufferSizeNotDivisible`: Raised when the buffer size is not divisible by a required divisor.
- `writeOutOfBounds`: Raised when a write operation exceeds the bounds of the underlying storage.

This type is useful for robust error handling in tensor-related computations.
-/
inductive TensorError where
  | nameNotFound (name : String) : TensorError
  | shapeMismatch (expectedRank : Nat) (gotRank : Nat) : TensorError
  | negativeDimension (shape : Array Nat) : TensorError
  | indexOutOfBounds (indices : Array Nat) (shape : Array Nat) : TensorError
  | offsetNotAligned (offset : Nat) (alignment : Nat) : TensorError
  | bufferSizeMismatch (expected : Nat) (got : Nat) : TensorError
  | bufferSizeNotDivisible (size : Nat) (divisor : Nat) : TensorError
  | writeOutOfBounds (absByteIndex : Nat) (viewOffsetBytes: Nat)
    (viewSizeBytes : Nat) (storageSize : Nat) : TensorError
  deriving Repr, DecidableEq

end LLM.GPT2
