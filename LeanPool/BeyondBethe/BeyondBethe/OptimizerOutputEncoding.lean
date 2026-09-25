/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec

/-!
# Canonical finite-word encoding of optimizer output

This dependency-light module fixes the typed optimizer output and its exact
right-nested binary encoding.  It is shared by both the optimizer producer
and the certificate consumer, so neither side depends on the other's
correctness theorem.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Rational data returned by a normalized regularized-Bethe optimizer. -/
structure RationalOptimizerOutput (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℚ
  rowPotential : Fin n → ℚ
  columnPotential : Fin n → ℚ

/-- Canonical right-nested list encoding of a rational vector. -/
def rationalVectorBinaryCode {n : ℕ} (v : Fin n → ℚ) : List Bool :=
  binaryListCode rationalEntryBinaryCode (List.ofFn v)

/-- Canonical optimizer-output word: matrix, then row and column potentials. -/
def rationalOptimizerOutputCode {n : ℕ}
    (out : RationalOptimizerOutput n) : List Bool :=
  pair (rationalMatrixBinaryEncoding.encode ⟨n, out.matrix⟩)
    (pair (rationalVectorBinaryCode out.rowPotential)
      (rationalVectorBinaryCode out.columnPotential))

end BeyondBethe
