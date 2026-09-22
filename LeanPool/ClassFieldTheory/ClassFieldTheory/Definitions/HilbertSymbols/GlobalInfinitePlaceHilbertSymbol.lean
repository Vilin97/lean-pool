/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Infinite-place Hilbert factors
-/

open scoped NumberField
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- The Hilbert factor at an infinite place.  It is nontrivial only at a real
place for the quadratic exponent, when both arguments are negative.

In the product-formula theorem the field contains a primitive `n`-th root of
unity; under that hypothesis real places occur only in the cases covered by
this formula. -/
def globalInfinitePlaceHilbertSymbol
    (F : Type u) [Field F]
    (n : ℕ+) (v : InfinitePlace F) (a b : Fˣ) :
    rootsOfUnity (n : ℕ) F := by
  by_cases hn : (n : ℕ) = 2
  · by_cases hv : v.IsReal
    · by_cases ha : InfinitePlace.embedding_of_isReal hv (a : F) < 0
      · by_cases hb : InfinitePlace.embedding_of_isReal hv (b : F) < 0
        · refine ⟨(-1 : Fˣ), ?_⟩
          change (-1 : Fˣ) ^ (n : ℕ) = 1
          rw [hn]
          simp
        · exact 1
      · exact 1
    · exact 1
  · exact 1

end ClassFieldTheory
