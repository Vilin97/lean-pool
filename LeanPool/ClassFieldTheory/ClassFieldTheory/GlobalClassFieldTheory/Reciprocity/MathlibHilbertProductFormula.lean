/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
public import Mathlib.Algebra.BigOperators.Finprod
/-!
# Mathlib-facing Hilbert product formula

The established product formula is transported from the internal subgroup of
roots of unity to Mathlib's `rootsOfUnity`.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

open scoped Classical in
/-- The finite-place Hilbert factor, transported from the internal
unit-root subgroup to Mathlib's `rootsOfUnity`. -/
noncomputable def globalFinitePlaceHilbertSymbol
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    rootsOfUnity (n : ℕ) F :=
  (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ))
    (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
      F n hnF hmu v a b)

open scoped Classical in
/-- **Hilbert product formula.**  The product of the local symbols of two
global units over every finite and infinite place is one. -/
theorem hilbertProductFormula
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (a b : Fˣ) :
    (∏ v : InfinitePlace F,
        globalInfinitePlaceHilbertSymbol F n v a b) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        globalFinitePlaceHilbertSymbol F n hnF hmu v a b = 1 := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
  have hfinite :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_hasFiniteMulSupport
      F n hnF hmu a b
  change
    (∏ v : InfinitePlace F,
        e (GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol
          F n v a b)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        e (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
          F n hnF hmu v a b) = 1
  calc
    _ = e
        ((∏ v : InfinitePlace F,
            GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol
              F n v a b) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
              F n hnF hmu v a b) := by
      rw [map_mul, map_prod, map_finprod e hfinite]
    _ = e 1 := congrArg e
      (GlobalClassFieldTheory.Reciprocity.hilbertSymbol_allPlaces_product_eq_one
        F n hnF hmu a b)
    _ = 1 := map_one e

end ClassFieldTheory
