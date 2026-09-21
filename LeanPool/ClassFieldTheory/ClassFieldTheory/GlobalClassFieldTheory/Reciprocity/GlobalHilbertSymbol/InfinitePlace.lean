/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RootCharacters
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
/-!
# Hilbert symbols at infinite places

At a complex place the Hilbert symbol is trivial.  At a real place, once the
base field contains the relevant roots of unity, the only nontrivial case is
the quadratic one: its value is `-1` exactly when both arguments are negative.
The definition below records that evaluation directly in `μₙ(K)`.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- The Hilbert symbol of two global units at an infinite place.  Complex
places and nonquadratic exponents contribute `1`; a real quadratic place
contributes `-1` precisely when both real embeddings are negative. -/
noncomputable def infinitePlaceHilbertSymbol
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) := by
  by_cases hn : (n : ℕ) = 2
  · by_cases hv : v.IsReal
    · by_cases ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0
      · by_cases hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0
        · refine ⟨(-1 : Kˣ), ?_⟩
          change (-1 : Kˣ) ^ (n : ℕ) = 1
          rw [hn]
          simp
        · exact 1
      · exact 1
    · exact 1
  · exact 1

omit [NumberField K] in
/-- Every complex infinite place has trivial Hilbert symbol. -/
@[simp]
theorem infinitePlaceHilbertSymbol_eq_one_of_isComplex
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ)
    (hv : v.IsComplex) :
    infinitePlaceHilbertSymbol K n v a b = 1 := by
  have hvNotReal : ¬v.IsReal :=
    InfinitePlace.not_isReal_iff_isComplex.mpr hv
  simp [infinitePlaceHilbertSymbol, hvNotReal]

omit [NumberField K] in
/-- Away from the quadratic exponent, every infinite-place factor is
trivial. -/
@[simp]
theorem infinitePlaceHilbertSymbol_eq_one_of_ne_two
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) ≠ 2) :
    infinitePlaceHilbertSymbol K n v a b = 1 := by
  simp [infinitePlaceHilbertSymbol, hn]

omit [NumberField K] in
/-- Explicit real-place evaluation of the quadratic Hilbert symbol. -/
theorem infinitePlaceHilbertSymbol_real_apply
    (n : ℕ+) (v : InfinitePlace K) (a b : Kˣ)
    (hn : (n : ℕ) = 2) (hv : v.IsReal) :
    (infinitePlaceHilbertSymbol K n v a b).1 =
      if InfinitePlace.embedding_of_isReal hv (a : K) < 0 ∧
          InfinitePlace.embedding_of_isReal hv (b : K) < 0 then
        (-1 : Kˣ)
      else
        1 := by
  by_cases ha : InfinitePlace.embedding_of_isReal hv (a : K) < 0
  · by_cases hb : InfinitePlace.embedding_of_isReal hv (b : K) < 0
    · simp [infinitePlaceHilbertSymbol, hn, hv, ha, hb]
    · simp [infinitePlaceHilbertSymbol, hn, hv, ha, hb]
  · simp [infinitePlaceHilbertSymbol, hn, hv, ha]

end Reciprocity
end GlobalClassFieldTheory
