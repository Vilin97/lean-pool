/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FirstRamificationComparison
/-!
# The first lower ramification group of a local field extension

The canonical complete-DVF valuation on a finite local extension specializes
the general comparison between the first lower group and Hilbert's
ramification group. The latter is transported from the decomposition group
back to the full Galois group.
-/

noncomputable section

open scoped ValuativeRel
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace RamificationTheory.LocalField

open LocalFieldTheory

/-- The first lower group of the chosen local extension is Hilbert's
ramification group for its canonical valuation ring. -/
theorem localLowerRamificationGroup_one_eq_hilbertRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localLowerRamificationGroup K L 1 =
      Subgroup.comap
        (RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup
          (base := localCompleteDVF K)
          (target := chosenLocalExtensionCompleteDVF K L)).toMonoidHom
        (RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInDecomposition K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring) := by
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
  exact
    RamificationTheory.HilbertRamification.lowerRamificationGroup_one_eq_hilbertRamificationGroup
    base target (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L)

/-- Triviality of the first lower group is exactly triviality of Hilbert's
ramification group; the two transports above are both injective. -/
theorem localLowerRamificationGroup_one_eq_bot_iff_hilbertRamificationGroup_eq_bot
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localLowerRamificationGroup K L 1 = ⊥ ↔
      RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring = ⊥ := by
  let A := (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
  let e := RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup
    (base := localCompleteDVF K) (target := chosenLocalExtensionCompleteDVF K L)
  let H := RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K A
  let f := (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A).subtype
  rw [localLowerRamificationGroup_one_eq_hilbertRamificationGroup]
  change (H.map f).comap e.toMonoidHom = ⊥ ↔ H = ⊥
  have hrecover :
      ((H.map f).comap e.toMonoidHom).map e.toMonoidHom = H.map f :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective (H.map f)
  calc
    (H.map f).comap e.toMonoidHom = ⊥ ↔
        ((H.map f).comap e.toMonoidHom).map e.toMonoidHom = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (H.map f).comap e.toMonoidHom)
        (f := e.toMonoidHom) e.injective).symm
    _ ↔ H.map f = ⊥ := by rw [hrecover]
    _ ↔ H = ⊥ :=
      Subgroup.map_eq_bot_iff_of_injective (H := H) (f := f) (by
        intro x y hxy
        exact Subtype.ext hxy)

end RamificationTheory.LocalField
