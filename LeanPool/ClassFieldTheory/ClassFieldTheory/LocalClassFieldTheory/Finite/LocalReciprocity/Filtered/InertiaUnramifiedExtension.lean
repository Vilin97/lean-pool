/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified
/-!
# Finite local extensions fixed by inertia are unramified

A finite Galois intermediate field of a local separable closure whose fixing
subgroup contains the kernel of the residue-degree map is unramified for its
canonical spectral valuation.  The proof constructs its finite abstract field,
uses the existing abstract-to-valued unramifiedness theorem, and transports the
result along the infinite Galois correspondence.
-/

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open LocalClassFieldTheory LocalFieldTheory RamificationTheory ClassFormation
open CyclicCohomology
open LocalFieldTheory.IsNonarchimedeanLocalField

/- The private predicate isolates the canonical spectral instance setup for
equality transport.  The public theorem below exposes the same instances
directly, so consumers need not use this implementation predicate. -/
private def SpectrallyUnramifiedLocalIntermediateField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] : Prop := by
  letI : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  exact IsUnramifiedValuedExtension K E

private theorem spectrallyUnramifiedLocalIntermediateField_congr
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K))
    [hEfin : FiniteDimensional K E] [hFfin : FiniteDimensional K F]
    (h : E = F) :
    SpectrallyUnramifiedLocalIntermediateField K E ↔
      SpectrallyUnramifiedLocalIntermediateField K F := by
  subst F
  rfl

/-- A finite Galois local intermediate field fixed by inertia is unramified
for its canonical spectral valuation. -/
theorem localIntermediateField_isUnramified_of_inertia_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E]
    (hE : MonoidHom.ker (localResidueDegree K).toMonoidHom ≤ E.fixingSubgroup) :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension
        (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : Module.Finite 𝒪[K] 𝒪[E] :=
      localCompleteDVF_integerRing_moduleFinite K E
    IsUnramifiedValuedExtension K E := by
  let H : FiniteAbstractField (Gal(SeparableClosure K / K)) :=
    { field := closedFixingSubgroup K (SeparableClosure K) E
      finite := by
        apply Nat.finite_of_card_ne_zero
        change (extensionSubgroup
          (baseField (Gal(SeparableClosure K / K)))
          (closedFixingSubgroup K (SeparableClosure K) E)
          (le_baseField _)).index ≠ 0
        have hindex : (extensionSubgroup
            (baseField (Gal(SeparableClosure K / K)))
            (closedFixingSubgroup K (SeparableClosure K) E)
            (le_baseField _)).index = E.fixingSubgroup.index := by
          symm
          rw [← Subgroup.relIndex_top_right]
          rfl
        rw [hindex, ← IntermediateField.finrank_eq_fixingSubgroup_index
          (SeparableClosure K) E]
        exact (Module.finrank_pos (R := K) (M := E)).ne' }
  have hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal := by
    change (E.fixingSubgroup.subgroupOf
      (⊤ : Subgroup (Gal(SeparableClosure K / K)))).Normal
    infer_instance
  have hunramified :
      H.toFiniteAbstractExtension.IsUnramified (localResidueDatum K) := by
    change
      (baseField (Gal(SeparableClosure K / K))).toSubgroup ⊓
          (localResidueDegree K).toMonoidHom.ker ≤ E.fixingSubgroup
    exact inf_le_right.trans hE
  have h := abstractFixedField_isUnramifiedValuedExtension K H hnormal hunramified
  have hfixed : abstractFixedField K (SeparableClosure K) H.field = E :=
    InfiniteGalois.fixedField_fixingSubgroup E
  exact
    (spectrallyUnramifiedLocalIntermediateField_congr K
      (abstractFixedField K (SeparableClosure K) H.field) E
      (hEfin := abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite) hfixed).mp h

end ClassFieldTower.Martinet.Shafarevich
