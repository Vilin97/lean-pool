/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot
-/

/-!
# Bounds Lemmas for the Keccak State Array

The Keccak-p permutation operates on a state of 25 lanes indexed by a column
`x ∈ [0, 5)` and a row `y ∈ [0, 5)`. The lemmas in this file discharge the
within-bounds obligations for the various `x + offset` and `x + 5 * y` index
expressions used in `Cryptography.Hashes.SHA3.Basic`, so that every state-array
access is provably in range.
-/

namespace Cryptography

/-- A column index plus a fixed offset below 21 stays within the 25-lane state. -/
theorem StateIndexWithinBounds521
  (index : Nat)
  (offset : Nat)
  (hCol : index ∈ [:5])
  (hOffset : offset < 21)
  : index + offset < 25 := by
  have hc : index < 5 := hCol.2.1
  omega

/-- A column index plus five times a row index stays within the 25-lane state. -/
theorem StateIndexWithinBounds55
  (index : Nat)
  (offset : Nat)
  (hCol : index ∈ [:5])
  (hOffset : offset ∈ [:5])
  : index + 5 * offset < 25 := by
  have hc : index < 5 := hCol.2.1
  have ho : offset < 5 := hOffset.2.1
  omega

/-- The ρ/π permuted index `(x + 3 * y) % 5 + 5 * x` stays within the 25-lane state. -/
theorem StateIndexWithinBounds55'
  (index : Nat)
  {x y : Nat}
  (hCol₁ : x ∈ [:5])
  (hCol₂ : y ∈ [:5])
  (hi : index = (x + 3 * y) % 5 + 5 * x)
  : index < 25 := by
  have hc : x < 5 := hCol₁.2.1
  have ho : y < 5 := hCol₂.2.1
  omega

end Cryptography
