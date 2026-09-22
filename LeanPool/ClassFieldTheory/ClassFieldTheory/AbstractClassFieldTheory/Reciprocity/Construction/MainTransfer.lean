/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.TransferNaturality
/-!
Constructs the transfer map for intermediate Galois quotients and relates it to Frobenius
restriction and norm naturality.
-/

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators
open MulAction

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]


/-- The inclusion `G(L/K') → G(L/K)` induced by `K' ⊆ K`. -/
def transferNormNaturalityIntermediateInclusion
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') →*
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  finiteReciprocityNaturalityRestriction K K' L L (hLK'.trans hK'K) hLK'
    hK'K le_rfl

/--
Establishes the identity `transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
(QuotientGroup.mk k') = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateInclusion_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

/-- The inclusion of finite Galois groups attached to an intermediate field
is injective. -/
theorem transferNormNaturalityIntermediateInclusion_injective
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Function.Injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply (mem_extensionSubgroup_iff K' L hLK' (k'⁻¹ * l')).2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        extensionSubgroup K L (hLK'.trans hK'K) :=
    QuotientGroup.eq.mp h
  have hG := (mem_extensionSubgroup_iff K L (hLK'.trans hK'K)
    ((Subgroup.inclusion hK'K k')⁻¹ *
      Subgroup.inclusion hK'K l')).1 hmem
  simpa using hG

/-- The copy of `G(L/K')` inside `G(L/K)`. -/
def transferNormNaturalityIntermediateSubgroup
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Subgroup (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) :=
  (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).range

/-- The canonical identification of `G(L/K')` with its image in
`G(L/K)`. -/
noncomputable def transferNormNaturalityIntermediateQuotientEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ≃*
      transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K :=
  MulEquiv.ofBijective
    (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).rangeRestrict
    ⟨fun _ _ h =>
        transferNormNaturalityIntermediateInclusion_injective K K' L hLK' hK'K
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateQuotientEquiv_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
      (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

/-- Restriction sends the Frobenius-level intermediate subgroup exactly
onto the finite intermediate Galois subgroup. -/
theorem transferNormNaturalityFrobeniusIntermediate_map_restriction
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup
        E L hL).map
        (D.extensionRestriction E.base.field L (hL.trans E.below)) =
      transferNormNaturalityIntermediateSubgroup
        E.base.field E.field.field L hL E.below := by
  have hcomm (x : E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) :
      transferNormNaturalityIntermediateInclusion
          E.base.field E.field.field L hL E.below
          (D.extensionRestriction E.field.field L hL x) =
        D.extensionRestriction E.base.field L (hL.trans E.below)
          (D.finiteReciprocityNaturalityFrobeniusTowerMap
            E.base.field E.field.field L L
            (hL.trans E.below) hL E.below le_rfl x) := by
    refine QuotientGroup.induction_on x ?_
    intro k'
    rfl
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    rcases hh with ⟨x, rfl⟩
    exact ⟨D.extensionRestriction E.field.field L hL x, hcomm x⟩
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨QuotientGroup.mk (Subgroup.inclusion E.below k'), ?_, rfl⟩
    exact ⟨QuotientGroup.mk k', rfl⟩

end DegreeData

/-- The left vertical arrow in transfer--norm naturality.  This is Mathlib's actual
transfer into the abelianization of the intermediate subgroup, transported
along the canonical identification with `G(L/K')`. -/
noncomputable def transferNormNaturalityTransfer
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))] :
    Abelianization (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)) →*
      Abelianization (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let e := transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
  exact e.symm.abelianizationCongr.toMonoidHom.comp
    (Abelianization.lift
      (MonoidHom.transfer (Abelianization.of : H →* Abelianization H)))

namespace DegreeData

/-- Transfer commutes with restriction from the infinite Frobenius
quotients to the finite Galois quotients.  This is the quotient-naturality
step in the proof of transfer--norm naturality. -/
theorem transferNormNaturalityTransfer_restriction_natural
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    [hLfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field L (hL.trans E.below))] :
    (transferNormNaturalityTransfer
        E.base.field E.field.field L hL E.below).comp
        (Abelianization.map
          (D.extensionRestriction E.base.field L (hL.trans E.below))) =
      (Abelianization.map
        (D.extensionRestriction E.field.field L hL)).comp
        (D.transferNormNaturalityFrobeniusTransfer E L hL) := by
  let P := E.base.field.toSubgroup ⧸
    D.extensionInertiaWithin E.base.field L (hL.trans E.below)
  let Q := E.base.field.toSubgroup ⧸
    extensionSubgroup E.base.field L (hL.trans E.below)
  let f : P →* Q :=
    D.extensionRestriction E.base.field L (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  let H₀ := transferNormNaturalityIntermediateSubgroup
    E.base.field E.field.field L hL E.below
  let e := D.transferNormNaturalityFrobeniusIntermediateEquiv
    E L hL
  let e₀ := transferNormNaturalityIntermediateQuotientEquiv
    E.base.field E.field.field L hL E.below
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hf : Function.Surjective f :=
    D.transferNormNaturalityExtensionRestriction_surjective
      E.base.field L (hL.trans E.below)
  have hker : f.ker ≤ H :=
    D.transferNormNaturalityExtensionRestriction_ker_le_intermediate
      E L hL
  have hmap : H.map f = H₀ :=
    D.transferNormNaturalityFrobeniusIntermediate_map_restriction
      E L hL
  let c : H.map f ≃* H₀ := MulEquiv.subgroupCongr hmap
  have hnat := abelianization_transfer_natural_of_surjective
    f hf H hker
  dsimp only at hnat
  have htransferCast :
      c.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H.map f →* Abelianization (H.map f)))) =
        Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H₀ →* Abelianization H₀)) := by
    exact abelianization_transfer_congr_subgroup (H.map f) H₀ hmap
  have hcomm (x : E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) :
      transferNormNaturalityIntermediateInclusion
          E.base.field E.field.field L hL E.below
          (D.extensionRestriction E.field.field L hL x) =
        f (D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl x) := by
    refine QuotientGroup.induction_on x ?_
    intro k'
    rfl
  have htransport :
      (e₀.symm.abelianizationCongr.toMonoidHom.comp
          c.abelianizationCongr.toMonoidHom).comp
            (Abelianization.map (f.subgroupMap H)) =
        (Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
          e.symm.abelianizationCongr.toMonoidHom := by
    apply Abelianization.hom_ext
    apply MonoidHom.ext
    intro h
    simp only [MonoidHom.comp_apply, Abelianization.map_of]
    apply congrArg Abelianization.of
    obtain ⟨x, rfl⟩ := e.surjective h
    have hex : e.symm.toMonoidHom (e x) = x := e.symm_apply_apply x
    rw [hex]
    apply e₀.injective
    calc
      e₀ (e₀.symm.toMonoidHom
          (c.toMonoidHom ((f.subgroupMap H) (e x)))) =
          c.toMonoidHom ((f.subgroupMap H) (e x)) :=
        e₀.apply_symm_apply _
      _ = e₀ (D.extensionRestriction E.field.field L hL x) := by
        apply Subtype.ext
        exact (hcomm x).symm
  unfold transferNormNaturalityTransfer DegreeData.transferNormNaturalityFrobeniusTransfer
  dsimp only
  calc
    (e₀.symm.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H₀ →* Abelianization H₀)))).comp
        (Abelianization.map f) =
      (e₀.symm.abelianizationCongr.toMonoidHom.comp
          (c.abelianizationCongr.toMonoidHom.comp
            (Abelianization.lift
              (MonoidHom.transfer
                (Abelianization.of : H.map f →*
                  Abelianization (H.map f)))))).comp
        (Abelianization.map f) := by rw [htransferCast]
    _ = (e₀.symm.abelianizationCongr.toMonoidHom.comp
          c.abelianizationCongr.toMonoidHom).comp
        ((Abelianization.map (f.subgroupMap H)).comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →* Abelianization H)))) := by
      rw [hnat]
      simp only [MonoidHom.comp_assoc]
    _ = ((Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
            e.symm.abelianizationCongr.toMonoidHom).comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →* Abelianization H))) := by
      rw [← MonoidHom.comp_assoc, htransport]
    _ = (Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
        (e.symm.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →* Abelianization H)))) := by
      simp only [MonoidHom.comp_assoc]

/-- For a positive Frobenius lift, finite transfer is the product of the
restrictions of the positive transfer factors.  This is the first displayed
transfer identity in the proof of transfer--norm naturality. -/
theorem transferNormNaturalityTransfer_frobenius_product
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    [Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field L (hL.trans E.below))]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL
    letI : H.FiniteIndex :=
      D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
        E L hL
    let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸ H))
    letI : Fintype Ω := Fintype.ofFinite _
    transferNormNaturalityTransfer E.base.field E.field.field L hL E.below
        (Abelianization.of
          (D.frobeniusRestriction E.base L (hL.trans E.below) σ)) =
      ∏ q : Ω, Abelianization.of
        (D.frobeniusRestriction E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) := by
  dsimp only
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
      E L hL
  let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
    ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
      (hL.trans E.below)) ⧸ H))
  let : Fintype Ω := Fintype.ofFinite _
  have hnat := D.transferNormNaturalityTransfer_restriction_natural
    E L hL
  have hnatσ := DFunLike.congr_fun hnat (Abelianization.of σ.1)
  have hprod := D.transferNormNaturalityFrobeniusTransfer_doubleCoset_formula
    E L hL σ.1
  calc
    transferNormNaturalityTransfer E.base.field E.field.field L hL E.below
        (Abelianization.of
          (D.frobeniusRestriction E.base L (hL.trans E.below) σ)) =
      Abelianization.map (D.extensionRestriction E.field.field L hL)
        (D.transferNormNaturalityFrobeniusTransfer E L hL
          (Abelianization.of σ.1)) := by
        simpa only [MonoidHom.comp_apply, Abelianization.map_of,
          DegreeData.frobeniusRestriction] using hnatσ
    _ = Abelianization.map (D.extensionRestriction E.field.field L hL)
        (∏ q : Ω, Abelianization.of
          ((D.transferNormNaturalityFrobeniusIntermediateEquiv
            E L hL).symm
              ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
                  q.out.out,
                QuotientGroup.out_conj_pow_minimalPeriod_mem
                  H σ.1 q.out⟩)) := by
        rw [hprod]
    _ = ∏ q : Ω, Abelianization.of
        (D.frobeniusRestriction E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro q _
        rw [Abelianization.map_of]
        rfl

end DegreeData

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The finite reciprocity equivalence factored through the maximal abelian quotient.  This
is the horizontal reciprocity arrow in transfer--norm naturality. -/
noncomputable def transferNormNaturalityAbelianizedReciprocity
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Additive (Abelianization
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) →+
      FiniteNormQuotient A K.field L hLK :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift
      (AddMonoidHom.toMultiplicativeRight
        (D.finiteReciprocityHom A v hAxiom K L hLK)))

/--
Establishes the identity `D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
(Additive.ofMul (Abelianization.of q)) = D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul
q)`.
-/
@[simp]
theorem transferNormNaturalityAbelianizedReciprocity_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul q) := by
  exact Abelianization.lift_apply_of
    (AddMonoidHom.toMultiplicativeRight
      (D.finiteReciprocityHom A v hAxiom K L hLK)) q

end DegreeData

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The double-coset transfer formula for transfer--norm naturality.  The indexing type is
`⟨σ⟩ \\ G(L/K) / G(L/K')`, represented by the orbit quotient of the action
of `zpowers σ` on the left-coset space. -/
theorem transferNormNaturality_transfer_doubleCoset_formula
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (σ : K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
    letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
    letI : Fintype (Quotient (orbitRel (Subgroup.zpowers σ)
        ((K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K)) ⧸ H))) :=
      Fintype.ofFinite _
    transferNormNaturalityTransfer K K' L hLK' hK'K (Abelianization.of σ) =
      ∏ q : Quotient (orbitRel (Subgroup.zpowers σ)
          ((K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K)) ⧸ H)),
        Abelianization.of
          ((transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K).symm
            ⟨q.out.out⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out *
                q.out.out,
              QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out⟩) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  dsimp only
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let := Fintype.ofFinite
    (Quotient (orbitRel (Subgroup.zpowers σ)
      ((K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)) ⧸ H)))
  rw [transferNormNaturalityTransfer]
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  exact abelianizationCongr_of
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K).symm _

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The invariant carrier used by `extensionFixedRepresentation` is
canonically the ambient fixed subgroup `A_L`. -/
def transferNormNaturalityExtensionFixedEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, by
    intro l
    let s : extensionSubgroup K L hLK :=
      ⟨Subgroup.inclusion hLK l, l.2⟩
    exact a.2 s⟩
  invFun a := ⟨a.1, by
    rintro ⟨k, hk⟩
    exact a.2 ⟨k.1, hk⟩⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
ambientFixedAddSubgroup A L) : A.V) = a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
      ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1
= a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_symm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1 =
      a.1 :=
  rfl

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed choice of right-coset representatives for the intermediate
subgroup in `G(L/K)`. -/
private noncomputable def chosenTransferNormNaturalityRightTransversal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K).RightTransversal :=
  ⟨Set.range Quotient.out, Subgroup.isComplement_range_right Quotient.out_eq'⟩

/-- Multiplication gives the right-coset decomposition
`G(L/K') × T ≃ G(L/K)` used. -/
private noncomputable def transferNormNaturalityRightCosetProductEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
        (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
          Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  (Equiv.prodCongr
      (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K).toEquiv
      (Equiv.refl _)).trans
    (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K).2.equiv.symm

@[simp]
private theorem transferNormNaturalityRightCosetProductEquiv_apply
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t) =
      transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r * t.1 :=
  rfl

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient action on the invariant carrier agrees with the relative
coset action used to define the norm. -/
private theorem transferNormNaturality_relativeCosetAction_eq_extensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK
        (transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a) q =
      ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 := by
  let := hnormal
  refine QuotientGroup.induction_on q ?_
  intro k
  rw [relativeCosetAction_mk]
  change A.ρ k.1 a.1 =
    ((extensionFixedRepresentation A K L hLK hnormal).ρ
      (QuotientGroup.mk k) a).1
  exact (extensionFixedRepresentation_quotient_mk_apply_val
    A K L hLK a k).symm

/-- Restricting the quotient action to `G(L/K')` agrees with the relative
coset action for `L | K'`. -/
private theorem transferNormNaturality_relativeCosetAction_intermediate
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :
    relativeCosetAction A K' L hLK'
        (transferNormNaturalityExtensionFixedEquiv A K L
          (hLK'.trans hK'K) hLnormal a) r =
      ((extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
          (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r) a).1 := by
  refine QuotientGroup.induction_on r ?_
  intro k'
  rw [relativeCosetAction_mk, transferNormNaturalityIntermediateInclusion_mk]
  change A.ρ k'.1 a.1 =
    ((extensionFixedRepresentation A K L (hLK'.trans hK'K) hLnormal).ρ
      (QuotientGroup.mk (Subgroup.inclusion hK'K k')) a).1
  exact (extensionFixedRepresentation_quotient_mk_apply_val
    A K L (hLK'.trans hK'K) a (Subgroup.inclusion hK'K k')).symm

/-- The element of `A_L` obtained by summing the conjugates indexed by a
right transversal for `G(L/K')` in `G(L/K)`.  Its `L | K'` norm is the
`L | K` norm of the original element. -/
noncomputable def transferNormNaturalityNormWitness
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  exact eA (∑ t : (T : Set _), E.ρ t.1 (eA.symm a))

private theorem transferNormNaturality_extensionAction_product
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t)) a =
      (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
        ((extensionFixedRepresentation A K L
          (hLK'.trans hK'K) hLnormal).ρ t.1 a) := by
  rw [transferNormNaturalityRightCosetProductEquiv_apply, map_mul]
  rfl

/-- The norm identity underlying the right vertical arrow of transfer--norm naturality.  It is
the additive form of the product calculation. -/
theorem transferNormNaturality_norm_doubleCoset_formula
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    fixedFieldInclusion A K K' hK'K
        (relativeNorm A K L (hLK'.trans hK'K) a) =
      relativeNorm A K' L hLK'
        (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let : Fintype (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) := Fintype.ofFinite _
  let : Fintype (K'.toSubgroup ⧸
      extensionSubgroup K' L hLK') := Fintype.ofFinite _
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  let aE := eA.symm a
  let valHom : E.V →+ A.V :=
    (ambientFixedAddSubgroup A L).subtype.comp eA.toAddMonoidHom
  apply Subtype.ext
  simp only [fixedFieldInclusion_coe, relativeNorm_apply_coe,
    relativeNormValue]
  have ha : eA aE = a := eA.apply_symm_apply a
  have hwitness :
      eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) =
        ∑ t : (T : Set (K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE := by
    simp [transferNormNaturalityNormWitness, T, E, eA, aE]
  have hE :
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
        ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
    calc
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
          ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityRightCosetProductEquiv
              K K' L hLK' hK'K p) aE :=
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K).sum_comp
          (fun q => E.ρ q aE) |>.symm
      _ = ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityIntermediateInclusion
              K K' L hLK' hK'K p.1) (E.ρ p.2.1 aE) := by
        apply Fintype.sum_congr
        intro p
        exact transferNormNaturality_extensionAction_product
          A K K' L hLK' hK'K aE p.1 p.2
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
            ∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))),
              E.ρ (transferNormNaturalityIntermediateInclusion
                K K' L hLK' hK'K r) (E.ρ t.1 aE) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
        apply Fintype.sum_congr
        intro r
        rw [map_sum]
  calc
    (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K),
      relativeCosetAction A K L (hLK'.trans hK'K) a q) =
        ∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), (E.ρ q aE).1 := by
      apply Fintype.sum_congr
      intro q
      rw [← ha]
      exact transferNormNaturality_relativeCosetAction_eq_extensionAction
        A K L (hLK'.trans hK'K) hLnormal aE q
    _ = (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE).1 := by
      change (∑ q, valHom (E.ρ q aE)) = valHom (∑ q, E.ρ q aE)
      rw [map_sum]
    _ = (∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 :=
      congrArg Subtype.val hE
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 := by
      change valHom (∑ r,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)) =
        ∑ r, valHom
          (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE))
      rw [map_sum]
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        relativeCosetAction A K' L hLK'
          (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
      apply Fintype.sum_congr
      intro r
      rw [← hwitness]
      have hr := transferNormNaturality_relativeCosetAction_intermediate
        A K K' L hLK' hK'K
        (eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a)) r
      calc
        _ = relativeCosetAction A K' L hLK'
            (eA (eA.symm
              (transferNormNaturalityNormWitness A K K' L hLK' hK'K a))) r := by
          simpa only [E, eA] using hr.symm
        _ = relativeCosetAction A K' L hLK'
            (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
          rw [eA.apply_symm_apply]

/-- The right vertical arrow of transfer--norm naturality: inclusion `A_K → A_{K'}`
descended to the actual finite norm quotients. -/
def transferNormNaturalityNormQuotientInclusion
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))] :
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      FiniteNormQuotient A K' L hLK' := by
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let targetClass : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A K' L hLK' :=
    (finiteNormClassHom A K' L hLK').comp
      (fixedFieldInclusion A K K' hK'K)
  refine finiteNormQuotientLift A K L (hLK'.trans hK'K) targetClass ?_
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A K' L hLK' _).2
  refine ⟨transferNormNaturalityNormWitness A K K' L hLK' hK'K a, ?_⟩
  exact (transferNormNaturality_norm_doubleCoset_formula
    A K K' L hLK' hK'K a).symm

/-- The transfer-side map sends a finite norm class to the class of its fixed-field inclusion. -/
@[simp]
theorem transferNormNaturality_normQuotientInclusion_finiteNormClass
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (x : ambientFixedAddSubgroup A K) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K
        (finiteNormClass A K L (hLK'.trans hK'K) x) =
      finiteNormClass A K' L hLK'
        (fixedFieldInclusion A K K' hK'K x) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  unfold transferNormNaturalityNormQuotientInclusion
  rw [finiteNormQuotientLift_finiteNormClass]
  rfl

namespace DegreeData

/-- Abelianized reciprocity evaluates a Frobenius class as the norm of a prime element. -/
private theorem abelianizedReciprocity_frobenius_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
        (Additive.ofMul (Abelianization.of (D.frobeniusRestriction KR L hLK σ))) =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  exact (D.transferNormNaturalityAbelianizedReciprocity_of A v hAxiom K L hLK
    (D.frobeniusRestriction (K.toFiniteResidueAbstractField D) L hLK σ)).trans
      (D.finiteReciprocityHom_apply_eq_primeNormClass A v hAxiom K L hLK
        (Additive.ofMul (D.frobeniusRestriction
          (K.toFiniteResidueAbstractField D) L hLK σ)) σ rfl π hπ)

/-- An equality of underlying subgroup values yields the corresponding mapped sum. -/
private theorem map_eq_sum_of_coe_eq
    {B C : Type*} [AddCommGroup B] [AddCommMonoid C]
    {H : AddSubgroup B} {ι : Type*} [Fintype ι]
    (g : H →+ C) (x : H) (f : ι → H) (h : (x : B) = ∑ i, (f i : B)) :
    g x = ∑ i, g (f i) := by
  have hsub : x = ∑ i, f i :=
    Subtype.ext (h.trans (map_sum H.subtype f Finset.univ).symm)
  rw [hsub, map_sum]

/-- transfer--norm naturality on one Frobenius generator.  The proof follows: transfer is
expanded over double cosets, the finite reciprocity equivalence
evaluates every positive Frobenius factor, and the resulting prime norms
are identified by `transferNormNaturalityNorm_eq_sum_transferNorms`. -/
theorem transferNormNaturality_generator_square
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup F.base.field L (hL.trans F.below)).Normal]
    [hLbasefinite : Finite (F.base.field.toSubgroup ⧸
      extensionSubgroup F.base.field L (hL.trans F.below))]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (extensionSubgroup F.base.field L
          (hL.trans F.below)).Normal
        exact hLnormal)) :
    letI : (extensionSubgroup F.field.field L hL).Normal :=
      transferNormNaturality_intermediateExtension_normal
        F.base.field F.field.field L hL F.below
    letI : Finite
        (F.field.field.toSubgroup ⧸
          extensionSubgroup F.field.field L hL) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          F.base.field F.field.field L hL F.below)
        (transferNormNaturalityIntermediateInclusion_injective
          F.base.field F.field.field L hL F.below)
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            F.base.field F.field.field L hL F.below
            (Abelianization.of
              (D.frobeniusRestriction
                (F.base.toFiniteResidueAbstractField D) L
                (hL.trans F.below) σ)))) =
      transferNormNaturalityNormQuotientInclusion A
        F.base.field F.field.field L hL F.below
        (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.base L (hL.trans F.below)
          (Additive.ofMul
            (Abelianization.of
              (D.frobeniusRestriction
                (F.base.toFiniteResidueAbstractField D) L
                (hL.trans F.below) σ)))) := by
  let hL'normal : (extensionSubgroup F.field.field L hL).Normal :=
    transferNormNaturality_intermediateExtension_normal
      F.base.field F.field.field L hL F.below
  let hL'finite : Finite
      (F.field.field.toSubgroup ⧸
        extensionSubgroup F.field.field L hL) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        F.base.field F.field.field L hL F.below)
      (transferNormNaturalityIntermediateInclusion_injective
        F.base.field F.field.field L hL F.below)
  let E := F.toFiniteResidueAbstractExtension D
  let hLnormalE :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal :=
    hLnormal
  let hL'normalE : (extensionSubgroup E.field.field L hL).Normal := hL'normal
  let hLbasefiniteE : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field L (hL.trans E.below)) :=
    hLbasefinite
  let hL'finiteE : Finite (E.field.field.toSubgroup ⧸
      extensionSubgroup E.field.field L hL) :=
    hL'finite
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let hSKF : S.toSubgroup ≤ F.base.field.toSubgroup := hSK
  let : Finite (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field S hSK) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  let hSbasefiniteF : Finite (F.base.field.toSubgroup ⧸
      extensionSubgroup F.base.field S hSKF) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  let Sfinite : FiniteAbstractField G := {
    field := S
    finite := D.frobeniusFixedField_absoluteFinite F.base L (hL.trans F.below) σ }
  let π : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sfinite
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
      E L hL
  let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
    ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
      (hL.trans E.below)) ⧸ H))
  let : Fintype Ω := Fintype.ofFinite _
  let β (q : Ω) := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let tK (q : Ω) : E.base.field.toSubgroup := Quotient.out q.out.out
  let C (q : Ω) := conjugateClosedSubgroup S (tK q).1
  let Sβ (q : Ω) := D.frobeniusFixedField E.field L hL (β q)
  let hSβK' (q : Ω) :=
    D.frobeniusFixedField_le E.field L hL (β q)
  let hSβK'F (q : Ω) : (Sβ q).toSubgroup ≤ F.field.field.toSubgroup := hSβK' q
  let hSβC (q : Ω) : (Sβ q).toSubgroup ≤ (C q).toSubgroup :=
    D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  let πβ (q : Ω) : ambientFixedAddSubgroup A (Sβ q) :=
    fixedFieldInclusion A (C q) (Sβ q) (hSβC q)
      (conjugateFixedElement A S (tK q).1 π)
  let (q : Ω) : Finite
      (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field (Sβ q) (hSβK' q)) :=
    D.frobeniusFixedField_finite E.field L hL (β q)
  let (q : Ω) : Finite
      (F.field.field.toSubgroup ⧸
        extensionSubgroup F.field.field (Sβ q) (hSβK'F q)) := by
    change Finite
      (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field (Sβ q) (hSβK' q))
    infer_instance
  let (q : Ω) : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) (Sβ q) (le_baseField (Sβ q))) :=
    D.frobeniusFixedField_absoluteFinite F.field L hL (β q)
  let Sβfinite (q : Ω) : FiniteAbstractField G := {
    field := Sβ q
    finite := inferInstance }
  have hPrime (q : Ω) : v.IsPrimeElement (Sβfinite q) (πβ q) :=
    D.transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime
      A v F L hL σ q π
        (v.chosenPrimeElement_isPrime Sfinite)
  let M := extensionSubgroup E.base.field E.field.field E.below
  let ΩN := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK))
  let orbitEquiv : Ω ≃ ΩN :=
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  let : Fintype ΩN := Fintype.ofFinite _
  let f : ΩN → A.V := fun qN =>
    let q := orbitEquiv.symm qN
    ((relativeNorm A E.field.field (Sβ q) (hSβK' q) (πβ q) :
      ambientFixedAddSubgroup A E.field.field) : A.V)
  have hNorm0 := D.transferNormNaturalityNorm_eq_sum_transferNorms
    A F L hL σ π
  have hNorm :
      ((fixedFieldInclusion A E.base.field E.field.field E.below
          (relativeNorm A E.base.field S hSK π) :
            ambientFixedAddSubgroup A E.field.field) : A.V) =
        ∑ q : Ω, ((relativeNorm A E.field.field
          (Sβ q) (hSβK' q) (πβ q) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
    calc
      _ = ∑ qN : ΩN, f qN := by
        simpa only [f, orbitEquiv, Sβ, hSβK', πβ, C, tK, β, S,
          hSK, E] using hNorm0
      _ = ∑ q : Ω, f (orbitEquiv q) :=
        (orbitEquiv.sum_comp f).symm
      _ = ∑ q : Ω, ((relativeNorm A E.field.field
          (Sβ q) (hSβK' q) (πβ q) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
        apply Fintype.sum_congr
        intro q
        change ((relativeNorm A E.field.field
            (Sβ (orbitEquiv.symm (orbitEquiv q)))
            (hSβK' (orbitEquiv.symm (orbitEquiv q)))
            (πβ (orbitEquiv.symm (orbitEquiv q))) :
              ambientFixedAddSubgroup A E.field.field) : A.V) = _
        rw [orbitEquiv.symm_apply_apply]
  have hTransfer := D.transferNormNaturalityTransfer_frobenius_product
    E L hL σ
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            E.base.field E.field.field L hL E.below
            (Abelianization.of
              (D.frobeniusRestriction E.base L
                (hL.trans E.below) σ)))) = _
  rw [hTransfer]
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (∑ q : Ω, Additive.ofMul
          (Abelianization.of
            (D.frobeniusRestriction E.field L hL (β q)))) = _
  rw [map_sum]
  have hLeft :
      (∑ q : Ω,
        D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.field L hL
            (Additive.ofMul
              (Abelianization.of
                (D.frobeniusRestriction E.field L hL (β q))))) =
      ∑ q : Ω, finiteNormClass A F.field.field L hL
          (relativeNorm A F.field.field (Sβ q) (hSβK'F q) (πβ q)) := by
    apply Fintype.sum_congr
    intro q
    exact abelianizedReciprocity_frobenius_eq_primeNormClass D A v hAxiom
      F.field L hL (β q) (πβ q) (by
        simpa [Sβfinite, Sβ, E,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using hPrime q)
  rw [hLeft]
  have hBase := abelianizedReciprocity_frobenius_eq_primeNormClass D A v hAxiom
    F.base L (hL.trans F.below) σ π (v.chosenPrimeElement_isPrime Sfinite)
  have hRight := (congrArg
    (transferNormNaturalityNormQuotientInclusion A
      F.base.field F.field.field L hL F.below) hBase).trans
    (transferNormNaturality_normQuotientInclusion_finiteNormClass
      A F.base.field F.field.field L hL F.below
      (relativeNorm A F.base.field S hSKF π))
  have hNormClasses := map_eq_sum_of_coe_eq
    (finiteNormClassHom A F.field.field L hL) _
    (fun q : Ω => relativeNorm A F.field.field (Sβ q) (hSβK'F q) (πβ q)) hNorm
  exact hNormClasses.symm.trans hRight.symm

/-- Transfer--norm naturality.  For a finite Galois extension
`L | K` and an intermediate field `K'`, reciprocity commutes with transfer:
`r_{L/K'} ∘ Ver = inclusion ∘ r_{L/K}`. -/
theorem transferNormNaturality
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup F.base.field L (hL.trans F.below)).Normal]
    [hLbasefinite : Finite (F.base.field.toSubgroup ⧸
      extensionSubgroup F.base.field L (hL.trans F.below))] :
    letI : (extensionSubgroup F.field.field L hL).Normal :=
      transferNormNaturality_intermediateExtension_normal
        F.base.field F.field.field L hL F.below
    letI : Finite
        (F.field.field.toSubgroup ⧸
          extensionSubgroup F.field.field L hL) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          F.base.field F.field.field L hL F.below)
        (transferNormNaturalityIntermediateInclusion_injective
          F.base.field F.field.field L hL F.below)
    (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.field L hL).comp
      (MonoidHom.toAdditive
        (transferNormNaturalityTransfer
          F.base.field F.field.field L hL F.below)) =
      (transferNormNaturalityNormQuotientInclusion A
        F.base.field F.field.field L hL F.below).comp
        (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.base L (hL.trans F.below)) := by
  let hL'normal : (extensionSubgroup F.field.field L hL).Normal :=
    transferNormNaturality_intermediateExtension_normal
      F.base.field F.field.field L hL F.below
  let : Finite
      (F.field.field.toSubgroup ⧸ extensionSubgroup F.field.field L hL) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        F.base.field F.field.field L hL F.below)
      (transferNormNaturalityIntermediateInclusion_injective
        F.base.field F.field.field L hL F.below)
  apply AddMonoidHom.ext
  intro x
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            F.base.field F.field.field L hL F.below x.toMul)) =
    transferNormNaturalityNormQuotientInclusion A
      F.base.field F.field.field L hL F.below
      (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.base L (hL.trans F.below) (Additive.ofMul x.toMul))
  refine QuotientGroup.induction_on x.toMul ?_
  intro q
  obtain ⟨σ, hσ⟩ := D.frobeniusRestriction_surjective
    (F.base.toFiniteResidueAbstractField D) L (hL.trans F.below) q
  rw [← hσ]
  exact D.transferNormNaturality_generator_square
    A v hAxiom F L hL σ

end DegreeData

end Representation

end

end ClassFormation
