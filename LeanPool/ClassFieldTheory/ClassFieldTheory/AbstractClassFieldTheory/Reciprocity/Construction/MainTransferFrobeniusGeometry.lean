/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.DoubleCosetOrbitGeometry
/-!
# Transfer--norm Frobenius geometry

For a finite Galois extension and an intermediate field, this module builds the
Frobenius-side subgroup and orbit equivalences used in transfer--norm
naturality.  The reusable orbit and double-coset constructions are isolated in
`DoubleCosetOrbitGeometry`.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology
open CategoryTheory

noncomputable section

open scoped BigOperators
open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The absolute group of an intermediate field, identified with its
literal copy inside the absolute group of the base field. -/
noncomputable def transferNormNaturalityIntermediateAbsoluteEquiv
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    K'.toSubgroup ≃* extensionSubgroup K K' hK'K :=
  MulEquiv.ofBijective
    ((Subgroup.inclusion hK'K).codRestrict
      (extensionSubgroup K K' hK'K) (fun k' => k'.2))
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h), by
      rintro ⟨k, hk'⟩
      let k' : K'.toSubgroup := ⟨k.1, hk'⟩
      exact ⟨k', Subtype.ext rfl⟩⟩

/-- The absolute intermediate-field equivalence evaluates by the underlying transfer map. -/
@[simp]
theorem transferNormNaturalityIntermediateAbsoluteEquiv_apply
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (k' : K'.toSubgroup) :
    ((transferNormNaturalityIntermediateAbsoluteEquiv K K' hK'K k').1 : G) = k'.1 :=
  rfl

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal] :
    (extensionSubgroup K' L hLK').Normal := by
  have hcomap : extensionSubgroup K' L hLK' =
      (extensionSubgroup K L (hLK'.trans hK'K)).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, mem_extensionSubgroup_iff,
      mem_extensionSubgroup_iff]
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData

/-- The restriction map on the infinite Frobenius quotients is injective
when the top field is unchanged. -/
theorem transferNormNaturalityFrobeniusTowerMap_injective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Injective
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  have hmem :
      (Subgroup.inclusion E.below k')⁻¹ * Subgroup.inclusion E.below l' ∈
        D.extensionInertiaWithin E.base.field L (hL.trans E.below) :=
    QuotientGroup.eq.mp h
  constructor
  · apply (mem_extensionSubgroup_iff E.field.field L hL (k'⁻¹ * l')).2
    have hG := (mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below)
      ((Subgroup.inclusion E.below k')⁻¹ *
        Subgroup.inclusion E.below l')).1 hmem.1
    simpa using hG
  · have hI := hmem.2
    change D.degree (((Subgroup.inclusion E.below k')⁻¹ *
      Subgroup.inclusion E.below l' : E.base.field.toSubgroup) : G) = 1 at hI
    change D.degree ((k'⁻¹ * l' : E.field.field.toSubgroup) : G) = 1
    exact hI

/-- The copy of `G(\widetilde L/K')` inside
`G(\widetilde L/K)`.  This is the subgroup `H` used in the classical
double-coset proof of transfer--norm naturality. -/
def transferNormNaturalityFrobeniusIntermediateSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Subgroup (E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :=
  (D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl).range

/-- The subgroup above is also the image of `G_K'` under the quotient
projection `G_K → G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL =
      (extensionSubgroup E.base.field E.field.field E.below).map
        (QuotientGroup.mk'
          (D.extensionInertiaWithin E.base.field L
            (hL.trans E.below))) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨Subgroup.inclusion E.below k', ?_, rfl⟩
    exact k'.2
  · rintro ⟨k, hk', rfl⟩
    let k' : E.field.field.toSubgroup := ⟨k.1, hk'⟩
    refine ⟨QuotientGroup.mk k', ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion E.below k') =
      QuotientGroup.mk k
    rfl

/-- Quotient projection maps the literal absolute subgroup belonging to
`K'` onto its copy `H` inside `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityIntermediateToFrobeniusSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    extensionSubgroup E.base.field E.field.field E.below →*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  refine ((QuotientGroup.mk'
    (D.extensionInertiaWithin E.base.field L (hL.trans E.below))).comp
      (extensionSubgroup E.base.field E.field.field E.below).subtype).codRestrict
        (D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL) ?_
  intro m
  change QuotientGroup.mk m.1 ∈
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  exact ⟨m.1, m.2, rfl⟩

/-- The map from the intermediate quotient onto the Frobenius subgroup is surjective. -/
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Surjective
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL) := by
  intro h
  have hh : h.1 ∈
      (extensionSubgroup E.base.field E.field.field E.below).map
      (QuotientGroup.mk'
        (D.extensionInertiaWithin E.base.field L (hL.trans E.below))) := by
    rw [← D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
      E L hL]
    exact h.2
  obtain ⟨m, hm, hval⟩ := hh
  refine ⟨⟨m, hm⟩, ?_⟩
  apply Subtype.ext
  unfold transferNormNaturalityIntermediateToFrobeniusSubgroup
  simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hval

/-- The intermediate-to-Frobenius map has the stated value on each representative. -/
@[simp]
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_apply
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (m : extensionSubgroup E.base.field E.field.field E.below) :
    (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
      E L hL m).1 =
        (QuotientGroup.mk m.1 : E.base.field.toSubgroup ⧸
          D.extensionInertiaWithin E.base.field L (hL.trans E.below)) := by
  rfl

/-- The canonical coset equivalence from `G_K/G_Σ` to
`G(\widetilde L/K)/Γ` intertwines the two copies of the `K'`-action. -/
theorem frobeniusFixedCosetClosureEquiv_equivariant
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (m : extensionSubgroup E.base.field E.field.field E.below)
    (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ)) :
    D.frobeniusFixedCosetClosureEquiv E.base L (hL.trans E.below) σ (m • x) =
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m) •
        D.frobeniusFixedCosetClosureEquiv E.base L
          (hL.trans E.below) σ x := by
  refine Quotient.inductionOn' x ?_
  intro k
  change QuotientGroup.mk (QuotientGroup.mk (m.1 * k)) =
    QuotientGroup.mk
      ((D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m).1 * QuotientGroup.mk k)
  rw [D.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply]
  rfl

/-- Restriction from the infinite Frobenius quotient onto the finite
Galois quotient is surjective. -/
theorem transferNormNaturalityExtensionRestriction_surjective
    (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Function.Surjective (D.extensionRestriction K L hLK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- The kernel of restriction to `G(L/K)` is contained in the subgroup
coming from `G(\widetilde L/K')`. -/
theorem transferNormNaturalityExtensionRestriction_ker_le_intermediate
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (D.extensionRestriction E.base.field L (hL.trans E.below)).ker ≤
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  intro q hq
  revert hq
  refine QuotientGroup.induction_on q ?_
  intro k hk
  change D.extensionRestriction E.base.field L (hL.trans E.below)
      (QuotientGroup.mk k) = 1 at hk
  rw [D.extensionRestriction_mk] at hk
  have hkL : k ∈
      extensionSubgroup E.base.field L (hL.trans E.below) := by
    exact QuotientGroup.eq_one_iff k |>.1 hk
  have hkK' : k ∈
      extensionSubgroup E.base.field E.field.field E.below := by
    apply (mem_extensionSubgroup_iff
      E.base.field E.field.field E.below k).2
    exact hL ((mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below) k).1 hkL)
  exact ⟨k, hkK', rfl⟩

/-- `H` has finite index in `G(\widetilde L/K)`, with no normality
assumption on the intermediate extension `K'/K`. -/
theorem transferNormNaturalityFrobeniusIntermediateFiniteIndex
    (D : DegreeData G) [IsTopologicalGroup G]
    (R : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ R.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup R.base.field L (hL.trans R.below)).Normal]
    [hL'normal : (extensionSubgroup R.field.field L hL).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup R L hL).FiniteIndex := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    R L hL]
  let I := D.extensionInertiaWithin R.base.field L (hL.trans R.below)
  let M := extensionSubgroup R.base.field R.field.field R.below
  have hIM : I ≤ M := by
    intro k hk
    apply (mem_extensionSubgroup_iff
      R.base.field R.field.field R.below k).2
    exact hL ((mem_extensionSubgroup_iff R.base.field L
      (hL.trans R.below) k).1 hk.1)
  let p := QuotientGroup.mk' I
  have hker : p.ker ≤ M := by
    simpa [p] using hIM
  let : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff,
    M.index_map_eq (QuotientGroup.mk'_surjective I) hker]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The copy of `G(\widetilde L/K')` is closed in
`G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediate_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    IsClosed (D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL : Set
        (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below))) := by
  let : CompactSpace E.field.field.toSubgroup :=
    isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
  let : IsClosed
      (D.extensionInertiaWithin E.field.field L hL :
        Set E.field.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.field L hL
  let : IsClosed (D.extensionInertiaWithin E.base.field L
      (hL.trans E.below) : Set E.base.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  change IsClosed (Set.range f)
  have hrange : Set.range f = Set.range f.toContinuousMap := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
  rw [hrange]
  simpa only [Set.image_univ] using
    (isCompact_univ.image f.continuous).isClosed

/-- The transfer-orbit index set
`⟨σ⟩ \ G(\widetilde L/K) / H` is canonically the norm double-coset
index set `G_K' \ G_K / G_Σ`.  The equivalence is inversion of double
cosets, followed by passage from powers of `σ` to their closure `Γ` and
the canonical identification `G_K/G_Σ ≃ G(\widetilde L/K)/Γ`. -/
noncomputable def transferNormNaturalityTransferNormOrbitEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)) ≃
      Quotient (orbitRel
        (extensionSubgroup E.base.field E.field.field E.below)
        (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ))) := by
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let M := extensionSubgroup E.base.field E.field.field E.below
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let f : M →* H := D.transferNormNaturalityIntermediateToFrobeniusSubgroup
    E L hL
  let e := D.frobeniusFixedCosetClosureEquiv
    E.base L (hL.trans E.below) σ
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  have hΓ :
      (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup = Γ.toSubgroup := by
    simp [Γ, DegreeData.frobeniusClosure]
  let eΓ : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup ≃
      P ⧸ Γ.toSubgroup := Subgroup.quotientEquivOfEq hΓ
  have heΓ (h : H)
      (x : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup) :
      eΓ (h • x) = h • eΓ x := by
    refine Quotient.inductionOn' x ?_
    intro p
    rfl
  let eΓorbit := orbitQuotientEquivOfSurjectiveEquivariant
    (MonoidHom.id H) Function.surjective_id eΓ heΓ
  have hf : Function.Surjective f :=
    D.transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
      E L hL
  have he (m : M)
      (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK) :
      e (m • x) = f m • e x := by
    exact D.frobeniusFixedCosetClosureEquiv_equivariant
      E L hL σ m x
  let eAction := orbitQuotientEquivOfSurjectiveEquivariant f hf e he
  exact (orbitQuotientSwapEquiv (Subgroup.zpowers σ.1) H).trans
    ((orbitQuotientClosedCyclicEquiv H hHclosed σ.1).trans
      (eΓorbit.trans eAction.symm))

/-- The transfer-norm orbit equivalence sends quotient representatives to their norm orbits. -/
@[simp]
theorem transferNormNaturalityTransferNormOrbitEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (k : E.base.field.toSubgroup) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
        (Quotient.mk'' (QuotientGroup.mk
          (QuotientGroup.mk k : E.base.field.toSubgroup ⧸
            D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
          (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸
              D.transferNormNaturalityFrobeniusIntermediateSubgroup
                E L hL)) =
      Quotient.mk'' (QuotientGroup.mk k⁻¹ :
        E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ)) := by
  unfold transferNormNaturalityTransferNormOrbitEquiv
  simp only [Equiv.trans_apply, orbitQuotientSwapEquiv_mk,
    orbitQuotientClosedCyclicEquiv_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_symm_mk,
    Subgroup.quotientEquivOfEq_mk]
  apply congrArg Quotient.mk''
  exact (D.frobeniusFixedCosetClosureEquiv E.base L
    (hL.trans E.below) σ).symm_apply_apply (QuotientGroup.mk k⁻¹)

/-- On the classical chosen transfer representative `t`, the preceding
equivalence is literally the norm orbit represented by `t⁻¹`. -/
theorem transferNormNaturalityTransferNormOrbitEquiv_apply
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ q =
      Quotient.mk'' (QuotientGroup.mk (Quotient.out q.out.out)⁻¹ :
        E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ)) := by
  let orbitEquiv := D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  calc
    orbitEquiv q = orbitEquiv (Quotient.mk'' q.out) :=
      congrArg orbitEquiv (Quotient.out_eq' q).symm
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk q.out.out)) :=
      congrArg orbitEquiv (congrArg Quotient.mk'' (Quotient.out_eq' q.out).symm)
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk
        (QuotientGroup.mk (Quotient.out q.out.out)))) :=
      congrArg orbitEquiv (congrArg Quotient.mk''
        (congrArg QuotientGroup.mk (Quotient.out_eq' q.out.out).symm))
    _ = _ := D.transferNormNaturalityTransferNormOrbitEquiv_mk
      E L hL σ (Quotient.out q.out.out)

end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
