/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Alok Singh
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

/-- Errors during Initialization or Tensor Access. -/
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
