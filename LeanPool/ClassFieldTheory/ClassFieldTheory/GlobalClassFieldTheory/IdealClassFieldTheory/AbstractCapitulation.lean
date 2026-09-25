/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
public import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.Transfer.Witt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
/-!
# Transfer input for the principal ideal theorem

The Galois correspondence realizes a subgroup `S ≤ Gal(M / K)` as an
intermediate field.  The transfer construction independently realizes
`Gal(M / M^S)` as a subgroup of `Gal(M / K)`.  The first theorem below
identifies these two actual subgroups.

For `S` equal to the commutator subgroup, this identification puts the
transfer used by reciprocity in exactly the form covered by Witt's transfer
theorem.  Consequently that transfer is trivial.  No class-field
realization or norm-subgroup equality is assumed here.
-/

@[expose] public section

noncomputable section

universe u

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable {K : ClosedSubgroup G}

/-- The subgroup used by transfer for the intermediate field cut out by
`S` is exactly `S`, not merely an abstractly isomorphic copy. -/
theorem transferIntermediateSubgroup_eq_galoisCorrespondenceSubgroup
    (M : FiniteGaloisSubextension K)
    (S : Subgroup M.extensionQuotient) :
    transferNormNaturalityIntermediateSubgroup
        K (M.intermediateField S) M.field
        (M.field_le_intermediateField S)
        (M.intermediateField_le_base S) =
      S := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro m
    rw [transferNormNaturalityIntermediateInclusion_mk]
    apply (M.mem_intermediateSubgroup_iff S _).1
    rw [← M.extensionSubgroup_intermediateField_eq S]
    change (m : G) ∈ M.intermediateField S
    exact m.property
  · intro hq
    obtain ⟨k, rfl⟩ := M.extensionQuotientMk_surjective q
    have hk :
        k ∈ M.intermediateSubgroup S :=
      (M.mem_intermediateSubgroup_iff S k).2 hq
    let m : (M.intermediateField S).toSubgroup :=
      ⟨k.1, ⟨k, hk, rfl⟩⟩
    refine ⟨QuotientGroup.mk m, ?_⟩
    rw [transferNormNaturalityIntermediateInclusion_mk]
    exact
      congrArg
        (fun z : K.toSubgroup =>
          (QuotientGroup.mk z : M.extensionQuotient))
        (Subtype.ext (by rfl))

/-- For the maximal abelian intermediate field of `M / K`, the transfer
appearing in transfer--norm naturality is trivial.  This is the precise
group-theoretic input needed for principalization. -/
theorem commutatorIntermediateTransfer_eq_one
    (M : FiniteGaloisSubextension K) :
    let S := commutator M.extensionQuotient
    letI : (extensionSubgroup (M.intermediateField S) M.field
        (M.field_le_intermediateField S)).Normal :=
      M.extensionSubgroup_over_intermediate_normal S
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K M.field M.below) :=
      M.finite
    transferNormNaturalityTransfer
        K (M.intermediateField S) M.field
        (M.field_le_intermediateField S)
        (M.intermediateField_le_base S) =
      1 := by
  dsimp only
  let S := commutator M.extensionQuotient
  let hLM := M.field_le_intermediateField S
  let hMK := M.intermediateField_le_base S
  let : (extensionSubgroup (M.intermediateField S) M.field hLM).Normal :=
    M.extensionSubgroup_over_intermediate_normal S
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K M.field (hLM.trans hMK)) :=
    M.finite
  let H :=
    transferNormNaturalityIntermediateSubgroup
      K (M.intermediateField S) M.field hLM hMK
  let e :=
    transferNormNaturalityIntermediateQuotientEquiv
      K (M.intermediateField S) M.field hLM hMK
  have hH : H = S := by
    exact transferIntermediateSubgroup_eq_galoisCorrespondenceSubgroup M S
  let hSFiniteIndex : S.FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  let _ : S.FiniteIndex := hSFiniteIndex
  let hHFiniteIndex : H.FiniteIndex :=
    hH.symm ▸ hSFiniteIndex
  let _ : H.FiniteIndex := hHFiniteIndex
  let c : H ≃* S :=
    MulEquiv.subgroupCongr hH
  change
    e.symm.abelianizationCongr.toMonoidHom.comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →*
              Abelianization H))) =
      1
  have hresult :
      e.symm.abelianizationCongr.toMonoidHom.comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →* Abelianization H))) =
        1 := by
    have hcongr :
        c.abelianizationCongr.toMonoidHom.comp
            (Abelianization.lift
              (MonoidHom.transfer
                (Abelianization.of : H →* Abelianization H))) =
          Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : S →* Abelianization S)) := by
      exact @abelianization_transfer_congr_subgroup
        M.extensionQuotient inferInstance H S hH
        hHFiniteIndex hSFiniteIndex
    apply MonoidHom.ext
    intro a
    change
      e.symm.abelianizationCongr
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →*
                Abelianization H)) a) =
        1
    rw [← abelianizationCongr_symm]
    apply e.abelianizationCongr.injective
    simp only [e.abelianizationCongr.apply_symm_apply, map_one]
    apply c.abelianizationCongr.injective
    simp only [map_one]
    calc
      c.abelianizationCongr
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →*
                Abelianization H)) a) =
        Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of :
                S →* Abelianization S)) a := by
          change
            c.abelianizationCongr.toMonoidHom
                (Abelianization.lift
                  (MonoidHom.transfer
                    (Abelianization.of : H →*
                      Abelianization H)) a) =
              Abelianization.lift
                (MonoidHom.transfer
                  (Abelianization.of :
                    S →* Abelianization S)) a
          exact DFunLike.congr_fun hcongr a
      _ =
          GroupTheory.Transfer.Witt.commutatorTransfer
            (G := M.extensionQuotient) a := rfl
      _ = 1 := by
        rw [
          GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization]
        rfl
  exact hresult

section AbstractCapitulation

variable {Γ : IntegralRepGroupType}
  [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  [TotallyDisconnectedSpace Γ]

/-- The fixed-field inclusion from a base field to the intermediate field
cut out by the commutator vanishes on the corresponding finite norm
quotients.  This is the capitulation statement supplied by reciprocity and
Witt transfer, before specializing the class formation to ideles. -/
theorem intermediateNormQuotientInclusion_commutator_eq_zero
    (D : DegreeData Γ) (A : Rep ℤ Γ)
    (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField Γ)
    (M : FiniteGaloisSubextension K.field) :
    let S := commutator M.extensionQuotient
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field M.field M.below) :=
      M.finite
    letI : Finite
        ((M.intermediateField S).toSubgroup ⧸
          extensionSubgroup (M.intermediateField S) M.field
            (M.field_le_intermediateField S)) :=
      M.extension_over_intermediate_finite S
    M.intermediateNormQuotientInclusion A S = 0 := by
  dsimp only
  let S := commutator M.extensionQuotient
  let hLM := M.field_le_intermediateField S
  let hMK := M.intermediateField_le_base S
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below) :=
    M.finite
  let : (extensionSubgroup K.field M.field M.below).Normal :=
    M.normal
  let : Finite
      ((M.intermediateField S).toSubgroup ⧸
        extensionSubgroup (M.intermediateField S) M.field hLM) :=
    M.extension_over_intermediate_finite S
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (M.intermediateField S) hMK) :=
    M.intermediateField_finite S
  let :
      (extensionSubgroup (M.intermediateField S) M.field hLM).Normal :=
    M.extensionSubgroup_over_intermediate_normal S
  let T : FiniteAbstractFieldExtension Γ :=
    FiniteAbstractFieldExtension.ofInclusion
      (M.intermediateField S) K hMK
  let : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field M.field (hLM.trans T.below)) := by
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below)
    exact M.finite
  let : (extensionSubgroup T.field.field M.field hLM).Normal := by
    change (extensionSubgroup (M.intermediateField S) M.field hLM).Normal
    exact M.extensionSubgroup_over_intermediate_normal S
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨M.field, hLM.trans T.below, inferInstance, inferInstance⟩
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field M.field hLM) := by
    change Finite
      ((M.intermediateField S).toSubgroup ⧸
        extensionSubgroup (M.intermediateField S) M.field hLM)
    exact M.extension_over_intermediate_finite S
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨M.field, hLM, inferInstance, inferInstance⟩
  have hnatural :=
    D.normResidueNaturality_transfer_inclusion
      A v hcf T M.field hLM
  have htransfer :
      transferNormNaturalityTransfer
          K.field (M.intermediateField S) M.field hLM hMK =
        1 :=
    commutatorIntermediateTransfer_eq_one M
  apply AddMonoidHom.ext
  intro a
  apply (D.normResidueSymbol A v hcf T.field E').injective
  have hnatural_a :
    D.normResidueSymbol A v hcf T.field E'
        (M.intermediateNormQuotientInclusion A S a) =
      MonoidHom.toAdditive
          (transferNormNaturalityTransfer
            K.field (M.intermediateField S) M.field hLM hMK)
        (D.normResidueSymbol A v hcf T.base E a) := by
    have hnatural_a_raw := (DFunLike.congr_fun hnatural a).symm
    change
      D.normResidueSymbol A v hcf T.field E'
          (M.intermediateNormQuotientInclusion A S a) =
        MonoidHom.toAdditive
            (transferNormNaturalityTransfer
              K.field (M.intermediateField S) M.field hLM hMK)
          (D.normResidueSymbol A v hcf T.base E a)
      at hnatural_a_raw
    exact hnatural_a_raw
  rw [hnatural_a, htransfer]
  change 0 = D.normResidueSymbol A v hcf T.field E' 0
  rw [map_zero]

end AbstractCapitulation

end IdealClassFieldTheory
end GlobalClassFieldTheory
