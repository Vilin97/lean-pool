/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
/-!
# The selected separable valuation under a semilinear equivalence

The base valuation certificate supplies the pullback on base elements.
Henselian uniqueness then identifies the selected valuation rings on the
separable closures; no equality of the extension valuations is assumed.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  hasExtension_valuation_of_valuationSubring_pullback →
    hasExtension_valuation_of_valuationSubring_pullback


noncomputable
section

namespace ClassFieldTower.Martinet.Shafarevich

open LocalClassFieldTheory LocalFieldTheory

/-- Valuation-compatible base and closure equivalences preserve the selected
valuation subrings used to define local residue degree. -/
theorem localSeparableValuationSubring_comap_semilinear
    (K K' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    (c : K ≃+* K') (e : SeparableClosure K ≃+* SeparableClosure K')
    (he : ∀ x : K, e (algebraMap K (SeparableClosure K) x) =
      algebraMap K' (SeparableClosure K') (c x))
    (hc : SemilinearValuationCompatible K K' c) :
    localSeparableValuationSubring K =
      (localSeparableValuationSubring K').comap e.toRingHom := by
  let _ : Algebra K K' := c.toRingHom.toAlgebra
  let _ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation K') := hc
  let B := (localSeparableValuationSubring K').comap e.toRingHom
  let _ : (localCompleteDVF K).valuation.HasExtension B.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap K (SeparableClosure K) x) ∈ localSeparableValuationSubring K' ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring
    rw [he, localSeparableValuationSubring_pullback]
    exact Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation K') x
  exact localSeparableValuationSubring_eq_of_hasExtension K B

end ClassFieldTower.Martinet.Shafarevich
