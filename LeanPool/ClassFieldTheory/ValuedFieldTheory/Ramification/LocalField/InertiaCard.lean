/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.InertiaRamificationCard
/-!
# Inertia order and ramification index for a chosen local extension

The residue field of a nonarchimedean local field is finite.  A finite
extension of its chosen complete discrete valuation has finite-dimensional
residue field, hence a separable residue extension.  This supplies the
residue-separability hypothesis of the general inertia-cardinality theorem.
-/

@[expose] public section

noncomputable
section

open scoped ValuativeRel
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory.HilbertRamification.CompleteDVF

/-- The inertia group of the chosen valuation ring has order equal to the
ramification index of the chosen finite Galois local extension. -/
theorem chosenLocalExtension_inertia_card_eq_ramificationIndex
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nat.card
        ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring.inertiaSubgroup K) =
      ramificationIndex (localCompleteDVF K).toDVF
        (chosenLocalExtensionCompleteDVF K L).toDVF := by
  let base := localCompleteDVF K
  let target := chosenLocalExtensionCompleteDVF K L
  let : base.valuation.HasExtension target.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension K L
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : FiniteDimensional base.residueField target.residueField :=
    residueField_finiteDimensional_of_moduleFinite base target
  let : Finite base.residueField := by
    change Finite 𝓀[K]
    infer_instance
  let : Algebra.IsAlgebraic base.residueField target.residueField :=
    Algebra.IsAlgebraic.of_finite _ _
  let : Algebra.IsSeparable base.residueField target.residueField :=
    inferInstance
  let : Algebra.IsSeparable
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal) := by
    change Algebra.IsSeparable base.residueField target.residueField
    infer_instance
  exact natCard_decompositionInertiaSubgroup_eq_ramificationIndex base target

end RamificationTheory.LocalField

end
