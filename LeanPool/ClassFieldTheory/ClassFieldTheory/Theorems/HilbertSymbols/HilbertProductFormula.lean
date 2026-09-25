/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFamily
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalInfinitePlaceHilbertSymbol
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertProductFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormulaAlgEquiv
public import Mathlib.Algebra.BigOperators.Finprod
/-!
# Existence of a coherent global Hilbert-pairing family

For a number field containing the `n`-th roots of unity, local class field
theory supplies a Hilbert pairing on every finite completion.  These
pairings can be chosen coherently: their values on two nonzero elements of
the number field have finite multiplicative support, and together with the
explicit infinite-place factors they satisfy the Hilbert product formula.

The statement is existential on purpose.  Mathlib provides the completions,
power-class groups, and roots of unity, but it does not choose a local Artin
map or a Hilbert symbol.  Consequently this theorem asserts the existence of
one family satisfying all the stated local pairing laws, including the
Kummer norm-residue criterion, and the global formula.  It does not disguise
the remaining choice of a value normalization as a definition.
-/

@[expose] public section

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- **Hilbert product formula.**  There is a family of local Hilbert
pairings on the finite completions whose global evaluations have finite
support and whose product, including the canonical infinite-place factors,
is one. -/
theorem exists_globalHilbertPairingFamily_productFormula
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    ∃ B : GlobalHilbertPairingFamily F n,
      GlobalHilbertPairingFamily.IsLocallyHilbert F B ∧
      GlobalHilbertPairingFamily.HasFiniteSupport F B hmu ∧
      ∀ a b : Fˣ,
        (∏ v : InfinitePlace F,
            globalInfinitePlaceHilbertSymbol F n v a b) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
  let : Small.{0} F := numberField_small F
  let S := Shrink.{0} F
  let : NumberField S := numberField_shrink F
  let e : S ≃ₐ[ℚ] F := (Shrink.ringEquiv F).toRatAlgEquiv
  have hmuS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨e.symm ζ,
      (mem_primitiveRoots n.pos).2
        (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
          e.symm.injective)⟩
  let BS := finitePlaceAdicHilbertPairingFamily S n hmuS
  let B := globalHilbertPairingFamilyCongr e n hmuS BS
  obtain ⟨hLocal, hSupport, hFormula⟩ :=
    finitePlaceAdicHilbertPairingFamily_productFormula S n hmuS
  refine ⟨B, ?_, ?_, ?_⟩
  · exact globalHilbertPairingFamilyCongr_isLocallyHilbert
      e n hmuS BS hLocal
  · exact globalHilbertPairingFamilyCongr_hasFiniteSupport
      e n hmuS hmu BS hSupport
  · exact globalHilbertPairingFamilyCongr_productFormula
      e n hmuS hmu BS hFormula

end ClassFieldTheory
