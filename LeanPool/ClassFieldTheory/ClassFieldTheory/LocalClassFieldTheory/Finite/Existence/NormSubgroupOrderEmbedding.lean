/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
/-!
# Finite abelian subextensions and native norm subgroups

A finite abelian subextension of the fixed separable closure determines an
ordinary norm subgroup of the local multiplicative group. This module proves
that the resulting assignment is an order embedding into the opposite poset
of native open finite-index subgroups. Surjectivity is the remaining local
existence-theorem input.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K : Type) [Field K]

/-- Finiteness over the concrete ground-field fixing group implies
finiteness over the abstract class-formation `baseField`. -/
theorem finiteAbelianSubextension_finite_over_absoluteBase
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) := by
  let : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) L.field L.below) :=
    L.finite
  simpa only using
    (FiniteGaloisSubextension.finite_extension_trans L.below
      (le_baseField (intrinsicAbstractBase K)))

/-- Normality over the concrete ground-field fixing group is normality over
the abstract class-formation `baseField`. -/
theorem finiteAbelianSubextension_normal_over_absoluteBase
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    (extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
      (le_baseField L.field)).Normal := by
  refine { conj_mem := fun h hh g ↦ ?_ }
  rw [mem_extensionSubgroup_iff] at hh ⊢
  let h' : (intrinsicAbstractBase K).toSubgroup := ⟨h, L.below hh⟩
  let g' : (intrinsicAbstractBase K).toSubgroup := ⟨g, by
    rw [show intrinsicAbstractBase K =
        baseField (intrinsicAbsoluteGalois K) from
      closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)]
    exact g.property⟩
  have hh' : h' ∈ extensionSubgroup
      (intrinsicAbstractBase K) L.field L.below :=
    (mem_extensionSubgroup_iff
      (intrinsicAbstractBase K) L.field L.below h').2 hh
  have hout := L.normal.conj_mem h' hh' g'
  have hout' := (mem_extensionSubgroup_iff
    (intrinsicAbstractBase K) L.field L.below _).1 hout
  change ((g : intrinsicAbsoluteGalois K) *
      (h : intrinsicAbsoluteGalois K) *
      (g : intrinsicAbsoluteGalois K)⁻¹) ∈ L.field
  change ((g' : intrinsicAbsoluteGalois K) *
      (h' : intrinsicAbsoluteGalois K) *
      (g' : intrinsicAbsoluteGalois K)⁻¹) ∈ L.field at hout'
  exact hout'

/-- The actual norm subgroup of the fixed field represented by an abstract
finite abelian extension. -/
def finiteAbelianNormSubgroup
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Subgroup Kˣ :=
  localNormSubgroup K (abstractFixedField K (SeparableClosure K) L.field)

/-- The fixed field represented by an abstract finite abelian extension is
an actual finite abelian extension of `K`.  The commutativity assertion is
transported across the concrete quotient--Galois-group equivalence, rather
than being inferred merely from the name of the abstract package. -/
theorem finiteAbelianSubextension_fixedField_isAbelianGalois
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    IsAbelianGalois K
      (abstractFixedField K (SeparableClosure K) L.field) := by
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  let : (extensionSubgroup
      (intrinsicAbstractBase K) L.field L.below).Normal := L.normal
  let e : L.extensionQuotient ≃* Gal(E/K) := by
    let e₀ := baseFixingExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) E
    have hclosed : closedFixingSubgroup K (SeparableClosure K) E =
        L.field :=
      closedFixingSubgroup_abstractFixedField_eq
        K (SeparableClosure K) L.field
    have hsub :
        extensionSubgroup (intrinsicAbstractBase K)
            (closedFixingSubgroup K (SeparableClosure K) E)
            (fixingSubgroupLeBase K (SeparableClosure K) E) =
          extensionSubgroup (intrinsicAbstractBase K) L.field L.below := by
      ext σ
      rw [mem_extensionSubgroup_iff, mem_extensionSubgroup_iff]
      exact SetLike.ext_iff.mp hclosed σ.1
    exact L.extensionQuotientMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq hsub.symm).trans e₀)
  refine { is_comm.comm := fun σ τ ↦ ?_ }
  exact e.symm.injective (by
    simpa only [map_mul] using
      mul_comm (e.symm σ) (e.symm τ))

/-- The concrete fixed field of an abstract compositum is the compositum of
the two concrete fixed fields inside the chosen separable closure. -/
theorem finiteAbelianSubextension_compositum_fixedField
    (U T : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    abstractFixedField K (SeparableClosure K) (U.compositum T).field =
      abstractFixedField K (SeparableClosure K) U.field ⊔
        abstractFixedField K (SeparableClosure K) T.field := by
  let EU := abstractFixedField K (SeparableClosure K) U.field
  let ET := abstractFixedField K (SeparableClosure K) T.field
  rw [← InfiniteGalois.fixedField_fixingSubgroup (EU ⊔ ET)]
  apply congrArg IntermediateField.fixedField
  change
    (U.field.toSubgroup ⊓ T.field.toSubgroup) =
      (EU ⊔ ET).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_sup]
  rw [show EU.fixingSubgroup = U.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField U.field,
    show ET.fixingSubgroup = T.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField T.field]

/-- The relative class-formation norm of a unit in an arbitrary abstract fixed
field is the ordinary field norm, before identifying the base fixed units
with `Kˣ`. -/
theorem relativeNorm_abstractFixedFieldUnit_val_of_isGalois
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    ((Additive.toMul
      ((relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) =
      algebraMap K (SeparableClosure K)
        (Algebra.norm K
          (x : abstractFixedField K (SeparableClosure K) H)) := by
  let E := abstractFixedField K (SeparableClosure K) H
  let y : ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) H :=
    abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed
    K (SeparableClosure K) E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K (SeparableClosure K) H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable
      K (SeparableClosure K) E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (intrinsicAbsoluteUnits K)
    (intrinsicAbstractBase K) (intrinsicAbstractBase K)
    (closedFixingSubgroup K (SeparableClosure K) E) H
    (fixingSubgroupLeBase K (SeparableClosure K) E) hH
    rfl (closedFixingSubgroup_abstractFixedField_eq
      K (SeparableClosure K) H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive (SeparableClosure K)ˣ ↦
      ((Additive.toMul z : (SeparableClosure K)ˣ) : SeparableClosure K))
    htransport
  change
    ((Additive.toMul
      ((relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH y).1 : Additive (SeparableClosure K)ˣ) :
        (SeparableClosure K)ˣ) : SeparableClosure K) = _
  exact htransport'.symm.trans hnorm

/-- The preceding norm identity after identifying the base fixed units with
`Additive Kˣ`. -/
theorem baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (H : ClosedSubgroup (intrinsicAbsoluteGalois K))
    (hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
    [Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) H hH)]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H (Additive.ofMul x))) =
      Additive.ofMul
        (normUnits K (abstractFixedField K (SeparableClosure K) H) x) := by
  apply (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).injective
  rw [(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).apply_symm_apply]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  calc
    _ = algebraMap K (SeparableClosure K)
        (Algebra.norm K
          (x : abstractFixedField K (SeparableClosure K) H)) :=
      relativeNorm_abstractFixedFieldUnit_val_of_isGalois K H hH x
    _ = algebraMap K (SeparableClosure K)
        ((normUnits K (abstractFixedField K (SeparableClosure K) H) x :
          Kˣ) : K) := by
      rw [LocalFieldTheory.normUnits_apply_coe]
    _ = _ :=
      (baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K)
        (normUnits K (abstractFixedField K (SeparableClosure K) H) x)).symm

/-- Transporting the abstract finite norm subgroup back to `Kˣ` gives
literally the ordinary norm subgroup of the represented fixed field. -/
theorem map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    (L.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
      additiveNormSubgroup K
        (abstractFixedField K (SeparableClosure K) L.field) := by
  let : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) L.field L.below) :=
    L.finite
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) L.field).symm b)
    have hb :
        abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) L.field (Additive.ofMul u) = b := by
      change abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field
            ((abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) L.field).symm b) = b
      exact (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) L.field).apply_symm_apply b
    rw [← hb]
    change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
        L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field (Additive.ofMul u))) ∈
        additiveNormSubgroup K E
    rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) L.field (Additive.ofMul u), ?_⟩
      apply (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.injective
      change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
          (relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K)
            L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) L.field (Additive.ofMul u))) =
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (normUnits K E u)))
      rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits,
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm_apply_apply]
    · change (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- An abstract fixed-coefficient norm containment transports back to the
corresponding containment of ordinary norm subgroups in `Kˣ`. -/
theorem finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K))
    (H : Subgroup Kˣ)
    (h :
      L.normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom) :
    finiteAbelianNormSubgroup K L ≤ H := by
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  intro x hx
  have hxAdd :
      Additive.ofMul x ∈
        additiveNormSubgroup K
          (abstractFixedField K (SeparableClosure K) L.field) := by
    exact hx
  rw [← map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup K L] at hxAdd
  rcases hxAdd with ⟨y, hy, hyx⟩
  rcases h hy with ⟨z, hz, hzy⟩
  have hzEq : z = Additive.ofMul x := by
    calc
      z = e.symm (e z) := (e.symm_apply_apply z).symm
      _ = e.symm y := congrArg e.symm hzy
      _ = Additive.ofMul x := hyx
  change Additive.ofMul x ∈ H.toAddSubgroup
  simpa [hzEq] using hz

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- States the theorem `finiteAbelianNormSubgroup_isOpen`. -/
theorem finiteAbelianNormSubgroup_isOpen
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    IsOpen (finiteAbelianNormSubgroup K L : Set Kˣ) := by
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  exact localNormSubgroup_isOpen K E

/-- States the theorem `finiteAbelianNormSubgroup_finiteIndex`. -/
theorem finiteAbelianNormSubgroup_finiteIndex
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    (finiteAbelianNormSubgroup K L).FiniteIndex := by
  let E := abstractFixedField K (SeparableClosure K) L.field
  let : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) L.field
        (le_baseField L.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K L
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) L.field inferInstance
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K L)
  let : Finite (Gal(E/K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K E]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (Abelianization (Gal(E/K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  let : Finite (NormQuotient K E) :=
    Finite.of_equiv (Abelianization (Gal(E/K)))
      (abelianizationEquivNormQuotient K E).toEquiv
  let : Finite (Kˣ ⧸ localNormSubgroup K E) := by
    change Finite (NormQuotient K E)
    infer_instance
  change (localNormSubgroup K E).FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The norm-subgroup map, sending a finite abelian extension to its ordinary
norm subgroup, with native openness and finite index recorded. -/
noncomputable def finiteAbelianNormSubgroupMap :
    FiniteAbelianSubextension (intrinsicAbstractBase K) →
      OpenFiniteIndexSubgroup K :=
  fun L ↦ ⟨finiteAbelianNormSubgroup K L,
    finiteAbelianNormSubgroup_isOpen K L,
    finiteAbelianNormSubgroup_finiteIndex K L⟩

/-- States the theorem `finiteAbelianNormSubgroupMap_injective`. -/
theorem finiteAbelianNormSubgroupMap_injective :
    Function.Injective (finiteAbelianNormSubgroupMap K) := by
  intro L₁ L₂ hL
  apply FiniteAbelianSubextension.normSubgroupMap_injective
    (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)
    (intrinsicFiniteAbstractBase K)
  apply Subtype.ext
  apply (AddSubgroup.map_injective
    (f := (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom)
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.injective)
  change (L₁.normSubgroup (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    (L₂.normSubgroup (intrinsicAbsoluteUnits K)).map
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup]
  have hsub : finiteAbelianNormSubgroup K L₁ =
      finiteAbelianNormSubgroup K L₂ :=
    congrArg OpenFiniteIndexSubgroup.subgroup hL
  exact congrArg Subgroup.toAddSubgroup hsub

/-- The order reversal for finite abelian subextensions, expressed for the actual fixed fields and
their ordinary norm subgroups. -/
theorem finiteAbelianSubextension_le_iff_normSubgroup_le
    (L₁ L₂ : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    L₁ ≤ L₂ ↔
      finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ := by
  refine (FiniteAbelianSubextension.le_iff_normSubgroup_le
    (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)
    (intrinsicFiniteAbstractBase K) L₁ L₂).trans ?_
  rw [← AddSubgroup.map_le_map_iff_of_injective
    (f := (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom)
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.injective]
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup]
  rfl

/-- The ordinary norm-subgroup assignment is an order embedding into the
opposite poset of native open finite-index subgroups. -/
noncomputable def finiteAbelianNormSubgroupOrderEmbedding :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ↪o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toFun := finiteAbelianNormSubgroupMap K
  inj' := finiteAbelianNormSubgroupMap_injective K
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

end LocalField

end LocalClassFieldTheory
