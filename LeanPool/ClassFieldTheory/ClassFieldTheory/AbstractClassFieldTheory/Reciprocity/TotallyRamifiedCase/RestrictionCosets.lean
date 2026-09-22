/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
/-!
# Restriction transport for finite Galois subextensions

This file constructs quotient restriction maps, their coset equivalences,
and the compatible relative actions and norms used in ramified towers.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Restriction between the named finite Galois quotient boundaries. -/
def bundledRestrictionHom
    {K : ClosedSubgroup G}
    (M L : FiniteGaloisSubextension K)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    M.extensionQuotient →* L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction
      K L.field M.field hML L.below).comp
        M.extensionQuotientMulEquiv.toMonoidHom)

/-- The coset map from the lower maximal-unramified quotient to a totally
ramified quotient. -/
noncomputable def abstractReciprocityRestrictionCosetMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) →
      (E.base.toSubgroup ⧸ E.subgroup) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  exact Quotient.map'
    (fun x : M₀.toSubgroup =>
      (⟨x.1, hM₀K x.2⟩ : E.base.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hME hxy)

/-- The restriction coset map is bijective when the upper extension is
totally ramified and the auxiliary field contains the relevant inertia. -/
theorem abstractReciprocityRestrictionCosetMap_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    Function.Bijective (M.abstractReciprocityRestrictionCosetMap D E hME) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    let aK : E.base.toSubgroup := ⟨a.1, hM₀K a.2⟩
    let bK : E.base.toSubgroup := ⟨b.1, hM₀K b.2⟩
    let z : E.base.toSubgroup := aK⁻¹ * bK
    have habE : aK⁻¹ * bK ∈ E.subgroup := by
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    have hzE : z.1 ∈ E.field.toSubgroup :=
      (mem_extensionSubgroup_iff E.base E.field E.below z).1 habE
    have haP : aK ∈ M.intermediateSubgroup S := by
      rw [← M.extensionSubgroup_intermediateField_eq S]
      exact (mem_extensionSubgroup_iff E.base M₀ hM₀K aK).2 a.2
    have hbP : bK ∈ M.intermediateSubgroup S := by
      rw [← M.extensionSubgroup_intermediateField_eq S]
      exact (mem_extensionSubgroup_iff E.base M₀ hM₀K bK).2 b.2
    have hzP : z ∈ M.intermediateSubgroup S :=
      (M.intermediateSubgroup S).mul_mem
        ((M.intermediateSubgroup S).inv_mem haP) hbP
    change (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) z ∈
        (D.fieldInertiaWithin E.base).map
          (QuotientGroup.mk'
            (extensionSubgroup E.base M.field M.below)) at hzP
    obtain ⟨i, hiI, hi⟩ := hzP
    have hizM : i⁻¹ * z ∈ extensionSubgroup E.base M.field M.below :=
      QuotientGroup.eq.mp hi
    have hizM' : i.1⁻¹ * z.1 ∈ M.field.toSubgroup :=
      (mem_extensionSubgroup_iff E.base M.field M.below (i⁻¹ * z)).1 hizM
    have hiE : i.1 ∈ E.field.toSubgroup := by
      have hmul := E.field.toSubgroup.mul_mem hzE
        (E.field.toSubgroup.inv_mem (hME hizM'))
      simpa [mul_inv_rev, mul_assoc] using hmul
    have hiM : i.1 ∈ M.field.toSubgroup := hInertia i hiI hiE
    have hzM : z.1 ∈ M.field.toSubgroup := by
      have hmul := M.field.toSubgroup.mul_mem hiM hizM'
      simpa [mul_assoc] using hmul
    exact hzM
  · intro x
    refine Quotient.inductionOn' x ?_
    intro k
    have hkDegree : D.degree k.1 ∈
        E.base.toSubgroup.map D.degree.toMonoidHom := ⟨k.1, k.2, rfl⟩
    obtain ⟨e, heE, heDegree⟩ :=
      (E.isTotallyRamified_iff_image_le D).1 hTot hkDegree
    let eE : E.field.toSubgroup := ⟨e, heE⟩
    let eK : E.base.toSubgroup := Subgroup.inclusion E.below eE
    let i : E.base.toSubgroup := k * eK⁻¹
    have hiI : i ∈ D.fieldInertiaWithin E.base := by
      change D.degree i.1 = 1
      dsimp [i, eK, eE]
      rw [map_mul, map_inv]
      change D.degree k.1 * (D.degree e)⁻¹ = 1
      change D.degree e = D.degree k.1 at heDegree
      rw [heDegree]
      simp
    have hiS : (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) i ∈ S :=
      ⟨i, hiI, rfl⟩
    have hiP : i ∈ M.intermediateSubgroup S := hiS
    let iM₀ : M₀.toSubgroup := ⟨i.1, ⟨i, hiP, rfl⟩⟩
    refine ⟨QuotientGroup.mk iM₀, ?_⟩
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    change (i⁻¹ * k).1 ∈ E.field.toSubgroup
    simpa [i, eK, eE, mul_inv_rev, mul_assoc] using eE.2

/-- The equivalence induced by the totally ramified restriction coset map. -/
noncomputable def abstractReciprocityRestrictionCosetEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) ≃
      E.quotient :=
  Equiv.ofBijective (M.abstractReciprocityRestrictionCosetMap D E hME)
    (M.abstractReciprocityRestrictionCosetMap_bijective
      D E hME hTot hInertia)

/-- The multiplicative restriction equivalence from the lower Galois group
to the original totally ramified quotient. -/
noncomputable def abstractReciprocityRestrictionMulEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    letI : Group E.quotient := by
      change Group
        (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
      infer_instance
    N.extensionQuotient ≃*
      E.quotient := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let N := M.lowerFiniteGalois S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  letI : (extensionSubgroup M₀ M.field N.below).Normal := N.normal
  letI : Group E.quotient := by
    change Group
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
    infer_instance
  let r : N.extensionQuotient →*
      E.quotient :=
    QuotientGroup.map
      (extensionSubgroup M₀ M.field N.below)
      (extensionSubgroup E.base E.field E.below)
      (Subgroup.inclusion hM₀K)
      (by
        intro m hm
        exact hME hm)
  apply MulEquiv.ofBijective r
  have hr : (r : N.extensionQuotient →
      E.quotient) =
      M.abstractReciprocityRestrictionCosetMap D E hME := by
    funext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl
  rw [hr]
  exact M.abstractReciprocityRestrictionCosetMap_bijective
    D E hME hTot hInertia

/-- Relative coset actions are transported by the restriction coset
equivalence. -/
theorem relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field)
    (r : let M₀ := M.maximalUnramifiedSubextension D
      let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
        M.field_le_intermediateField (M.inertiaImage D)
      M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      relativeCosetAction A E.base E.field E.below a
        (M.abstractReciprocityRestrictionCosetEquiv
          D E hME hTot hInertia r) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  refine Quotient.inductionOn' r ?_
  intro x
  rfl

/-- Relative norm commutes with fixed-field inclusion along the totally
ramified restriction equivalence. -/
theorem abstractReciprocity_relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteAbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) =
      fixedFieldInclusion A E.base M₀ hM₀K
        (relativeNorm A E.base E.field E.below a) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  let hMfinite : Finite
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    M.extension_over_intermediate_finite S
  let : Finite
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    E.finiteQuotient
  let e : (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) ≃
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    M.abstractReciprocityRestrictionCosetEquiv
      D E.toAbstractExtension hME hTot hInertia
  apply Subtype.ext
  let : Fintype
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    Fintype.ofFinite _
  let : Fintype
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    Fintype.ofFinite _
  change (∑ r, relativeCosetAction A M₀ M.field hMM₀
      (fixedFieldInclusion A E.field M.field hME a) r) =
    ∑ q, relativeCosetAction A E.base E.field E.below a q
  calc
    ∑ r, relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      ∑ r, relativeCosetAction A E.base E.field E.below a (e r) := by
        apply Fintype.sum_congr
        intro r
        exact M.relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
          A D E.toAbstractExtension hME hTot hInertia a r
    _ = ∑ q, relativeCosetAction A E.base E.field E.below a q :=
      e.sum_comp (relativeCosetAction A E.base E.field E.below a)

/-- Two auxiliary quotient elements commute when they have the same
restriction and the auxiliary field contains the inertia subgroup. -/
theorem commute_of_same_restriction_of_inertia_le
    (D : DegreeData G)
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    Commute g t := by
  rw [Commute]
  let a : E.base.toSubgroup := Quotient.out g
  let b : E.base.toSubgroup := Quotient.out t
  have ha : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) a = g :=
    Quotient.out_eq' g
  have hb : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) b = t :=
    Quotient.out_eq' t
  have hcosetE :
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (a * b) =
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (b * a) := by
    rw [map_mul, map_mul]
    have haE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) a =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below g := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) a =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) a) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below g :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) ha
    have hbE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) b =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below t := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) b =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) b) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below t :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) hb
    rw [haE, hbE, hres]
  let z : E.base.toSubgroup := (a * b)⁻¹ * (b * a)
  have hzE : z ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hcosetE
  have hzE' : z.1 ∈ E.field.toSubgroup :=
    (mem_extensionSubgroup_iff E.base E.field E.below z).1 hzE
  have hzDegree : D.degree z.1 = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, map_mul, map_mul]
    apply Multiplicative.ext
    change -((D.degree a.1).toAdd + (D.degree b.1).toAdd) +
        ((D.degree b.1).toAdd + (D.degree a.1).toAdd) = 0
    abel
  have hzM : z.1 ∈ M.field.toSubgroup :=
    hIE ⟨hzE', hzDegree⟩
  have hzH : z ∈ extensionSubgroup E.base M.field M.below :=
    (mem_extensionSubgroup_iff E.base M.field M.below z).2 hzM
  calc
    g * t = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (a * b) := by
      rw [map_mul, ha, hb]
    _ = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (b * a) :=
      QuotientGroup.eq.mpr hzH
    _ = t * g := by rw [map_mul, ha, hb]

/-- Equal restrictions induce equal relative coset actions on elements
fixed by the upper field. -/
theorem relativeCosetAction_eq_of_restriction_eq
    (A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) g =
      relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) t := by
  refine Quotient.inductionOn₂' g t ?_ hres
  intro x y hxy
  simp only [relativeCosetAction_mk, fixedFieldInclusion_coe]
  have hxyE : x⁻¹ * y ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hxy
  let e : E.field.toSubgroup := ⟨(x⁻¹ * y).1, hxyE⟩
  have hy : y = x * Subgroup.inclusion E.below e := by
    apply Subtype.ext
    simp [e]
  rw [hy]
  change A.ρ x.1 a.1 = A.ρ (x.1 * e.1) a.1
  rw [map_mul]
  change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ e.1 a.1)
  rw [a.2 e]

end FiniteGaloisSubextension

end ClassFormation
