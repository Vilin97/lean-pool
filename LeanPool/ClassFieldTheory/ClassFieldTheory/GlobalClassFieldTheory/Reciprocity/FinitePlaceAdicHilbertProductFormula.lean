/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertComparison
/-!
# A coherent Hilbert pairing family in a small number field

The finite-place family already constructed from the local norm-residue
pairing satisfies the local laws. Its finite factors agree with the factors
of the global Hilbert product formula.
-/

@[expose] public section

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

/-- The adic local pairings form a coherent global family, with their actual
finite-place factors satisfying the Hilbert product formula. -/
theorem finitePlaceAdicHilbertPairingFamily_productFormula
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    let B := finitePlaceAdicHilbertPairingFamily F n hmu
    GlobalHilbertPairingFamily.IsLocallyHilbert F B ∧
      GlobalHilbertPairingFamily.HasFiniteSupport F B hmu ∧
      ∀ a b : Fˣ,
        (∏ v : InfinitePlace F,
            globalInfinitePlaceHilbertSymbol F n v a b) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
  let B := finitePlaceAdicHilbertPairingFamily F n hmu
  have hnF : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  refine ⟨finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F n hmu, ?_, ?_⟩
  · intro a b
    have hsource :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_hasFiniteMulSupport
        F n hnF hmu a b
    have htarget : Function.HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 F) =>
          globalFinitePlaceHilbertSymbol F n hnF hmu v a b) :=
      hsource.fun_comp
        (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)).map_one
    convert htarget using 1
    funext v
    exact finitePlaceAdicHilbertPairingFamily_finiteFactor F n hnF hmu v a b
  · intro a b
    calc
      _ = (∏ v : InfinitePlace F,
              globalInfinitePlaceHilbertSymbol F n v a b) *
            ∏ᶠ v : HeightOneSpectrum (𝓞 F),
              globalFinitePlaceHilbertSymbol F n hnF hmu v a b := by
          congr 1
          apply finprod_congr
          intro v
          exact finitePlaceAdicHilbertPairingFamily_finiteFactor
            F n hnF hmu v a b
      _ = 1 := hilbertProductFormula F n hnF hmu a b

end ClassFieldTheory
