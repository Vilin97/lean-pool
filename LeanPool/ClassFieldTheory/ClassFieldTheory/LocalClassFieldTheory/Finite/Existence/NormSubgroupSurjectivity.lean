/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
/-!
# Surjectivity criteria for the local norm-subgroup map

This file translates the abstract existence theorem into ordinary field norms.
It proves the compositum and intersection formulas, isolates the norm-topology
criterion which makes the ordinary norm-subgroup order embedding surjective,
and constructs norm-topology witnesses from concrete finite Galois extensions.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K : Type) [Field K]

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The ordinary norm subgroup of a compositum is the intersection of the
two ordinary norm subgroups. -/
theorem finiteAbelianNormSubgroup_compositum
    (L₁ L₂ : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroup K (L₁.compositum L₂) =
      finiteAbelianNormSubgroup K L₁ ⊓
        finiteAbelianNormSubgroup K L₂ := by
  have habs :=
    FiniteAbelianSubextension.normSubgroup_compositum
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      (intrinsicFiniteAbstractBase K) L₁ L₂
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
          (intrinsicAbstractBase K)) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom) habs
  change ((L₁.compositum L₂).normSubgroup
      (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    (L₁.normSubgroup (intrinsicAbsoluteUnits K) ⊓
      L₂.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom at hmapped
  rw [AddSubgroup.map_inf _ _ _
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.injective] at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  apply Subgroup.ext
  intro x
  change Additive.ofMul x ∈ additiveNormSubgroup K
      (abstractFixedField K (SeparableClosure K)
        (L₁.compositum L₂).field) ↔
    Additive.ofMul x ∈
      (additiveNormSubgroup K
        (abstractFixedField K (SeparableClosure K) L₁.field) ⊓
       additiveNormSubgroup K
        (abstractFixedField K (SeparableClosure K) L₂.field))
  exact Iff.of_eq (congrArg
    (fun S : AddSubgroup (Additive Kˣ) => Additive.ofMul x ∈ S) hmapped)

/-- The ordinary norm subgroup of an intersection field is the supremum of
the two ordinary norm subgroups. -/
theorem finiteAbelianNormSubgroup_intersection
    (L₁ L₂ : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroup K (L₁.intersection L₂) =
      finiteAbelianNormSubgroup K L₁ ⊔
        finiteAbelianNormSubgroup K L₂ := by
  have habs :=
    FiniteAbelianSubextension.normSubgroup_intersection
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      (intrinsicFiniteAbstractBase K) L₁ L₂
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
          (intrinsicAbstractBase K)) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom) habs
  change ((L₁.intersection L₂).normSubgroup
      (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    (L₁.normSubgroup (intrinsicAbsoluteUnits K) ⊔
      L₂.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom at hmapped
  rw [AddSubgroup.map_sup] at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  apply (Subgroup.toAddSubgroup :
    Subgroup Kˣ ≃o AddSubgroup (Additive Kˣ)).injective
  change additiveNormSubgroup K
      (abstractFixedField K (SeparableClosure K)
        (L₁.intersection L₂).field) =
    Subgroup.toAddSubgroup
      (finiteAbelianNormSubgroup K L₁ ⊔
        finiteAbelianNormSubgroup K L₂)
  rw [(Subgroup.toAddSubgroup :
    Subgroup Kˣ ≃o AddSubgroup (Additive Kˣ)).map_sup]
  exact hmapped

/-- A native open finite-index subgroup which is open for the abstract norm
topology is the ordinary norm subgroup of a finite abelian subextension. -/
theorem exists_finiteAbelianNormSubgroup_eq_of_normOpen
    (H : OpenFiniteIndexSubgroup K)
    (hnormOpen :
      IsNormOpen (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        ((H.subgroup.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :
          AddSubgroup (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
            (intrinsicAbstractBase K))) : Set _)) :
    ∃ L, finiteAbelianNormSubgroupMap K L = H := by
  let : H.subgroup.FiniteIndex := H.finiteIndex
  let Habs : AddSubgroup
      (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
        (intrinsicAbstractBase K)) :=
    H.subgroup.toAddSubgroup.map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom
  have hopen :
      IsNormOpen (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        (Habs : Set _) := by
    simpa only [Habs] using hnormOpen
  let Hopen : FiniteAbelianSubextension.NormOpenAddSubgroup
      (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) := ⟨Habs, hopen⟩
  obtain ⟨L, hL⟩ :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      (intrinsicFiniteAbstractBase K) Hopen
  refine ⟨L, ?_⟩
  apply OpenFiniteIndexSubgroup.ext
  have habs : L.normSubgroup (intrinsicAbsoluteUnits K) = Habs :=
    congrArg Subtype.val hL
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
          (intrinsicAbstractBase K)) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom) habs
  change (L.normSubgroup (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    Habs.map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  have hcancel :
      Habs.map (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
        H.subgroup.toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      refine ⟨baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K) x, ⟨x, hx, rfl⟩, ?_⟩
      exact (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm_apply_apply x
  rw [hcancel] at hmapped
  apply Subgroup.ext
  intro x
  change Additive.ofMul x ∈ additiveNormSubgroup K
      (abstractFixedField K (SeparableClosure K) L.field) ↔
    Additive.ofMul x ∈ H.subgroup.toAddSubgroup
  exact Iff.of_eq (congrArg
    (fun S : AddSubgroup (Additive Kˣ) => Additive.ofMul x ∈ S) hmapped)

/-- If all native finite-index subgroups are norm-open, the ordinary
norm-subgroup order embedding is surjective. -/
theorem finiteAbelianNormSubgroupMap_surjective_of_normOpen
    (hnormOpen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex],
      IsNormOpen (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        ((H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :
          AddSubgroup (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
            (intrinsicAbstractBase K))) : Set _)) :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  intro H
  let : H.subgroup.FiniteIndex := H.finiteIndex
  apply exists_finiteAbelianNormSubgroup_eq_of_normOpen K H
  exact hnormOpen H.subgroup

omit [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- A finite Galois extension whose ordinary norm subgroup is contained in
`H` witnesses that `H` is open for the abstract norm topology. -/
theorem finiteIndexSubgroup_isNormOpen_of_normSubgroup_le
    (E : Type) [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (H : Subgroup Kˣ)
    (hnorm : localNormSubgroup K E ≤ H) :
    let A := intrinsicAbsoluteUnits K
    let B := intrinsicAbstractBase K
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let R : IntermediateField K (SeparableClosure K) := AlgHom.fieldRange i
  let : FiniteDimensional K R :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let : IsGalois K R := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  let L : FiniteGaloisSubextension B := {
    field := RamificationTheory.closedFixingSubgroup K (SeparableClosure K) R
    below := fixingSubgroupLeBase K (SeparableClosure K) R
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite
      K (SeparableClosure K) R }
  have hnormLe : additiveNormSubgroup K R ≤ H.toAddSubgroup := by
    intro x hx
    change Additive.toMul x ∈ localNormSubgroup K R at hx
    change Additive.toMul x ∈ H
    apply hnorm
    rw [← localNormSubgroup_fieldRange_eq K (SeparableClosure K) E i]
    exact hx
  have hmap :
      (L.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K R := by
    simpa [A, B, L, R, e,
      FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K (SeparableClosure K) R)
  have hLE :
      L.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    intro x hx
    have hxmap : e.symm x ∈
        (L.normSubgroup A).map e.symm.toAddMonoidHom :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap
    exact ⟨e.symm x, hnormLe hxmap, e.apply_symm_apply x⟩
  exact (normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨L, hLE⟩

omit [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Package a concrete finite Galois extension in the absolute Galois model,
retaining a prescribed upper bound for its ordinary norm subgroup. -/
theorem exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le
    (E : Type) [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (J : Subgroup Kˣ)
    (hnorm : localNormSubgroup K E ≤ J) :
    ∃ T : FiniteGaloisSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        J.toAddSubgroup := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let R : IntermediateField K (SeparableClosure K) := AlgHom.fieldRange i
  let : FiniteDimensional K R :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let : IsGalois K R := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  let T : FiniteGaloisSubextension B := {
    field := RamificationTheory.closedFixingSubgroup K (SeparableClosure K) R
    below := fixingSubgroupLeBase K (SeparableClosure K) R
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite
      K (SeparableClosure K) R }
  have hmap :
      (T.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K R := by
    simpa [A, B, e, T, R, FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K (SeparableClosure K) R)
  refine ⟨T, ?_⟩
  intro x hx
  rw [hmap] at hx
  change Additive.toMul x ∈ J
  apply hnorm
  rw [← localNormSubgroup_fieldRange_eq K (SeparableClosure K) E i]
  exact hx

end LocalField

end LocalClassFieldTheory

end
