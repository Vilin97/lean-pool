/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import LeanPool.GrothendieckVanishing.PresheafFilteredColimitCore

/-!
# Degree-one and higher filtered-colimit comparisons

The degree-`1` and higher comparison arguments showing that sheaf cohomology commutes
with filtered colimits on Noetherian spaces, building on the presheaf-boundary and
successor-stage infrastructure in `PresheafFilteredColimitCore`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- The global-sections functor used in the degree-`1` filtered-colimit boundary
construction. -/
private noncomputable def sheafH_filtered_colimit_h1_sectionsFunctor
    {X : TopCat.{u}} :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

section FilteredColimitH1

variable {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The stagewise top-sections map from the injective replacement to its quotient in the
degree-`1` filtered-colimit comparison. -/
private noncomputable def sheafH_filtered_colimit_h1_gTopNat :
    (sheafHFilteredColimitSuccInj Y' ⋙ sheafH_filtered_colimit_h1_sectionsFunctor) ⟶
      (sheafHFilteredColimitSuccQuotient Y' ⋙ sheafH_filtered_colimit_h1_sectionsFunctor) :=
  { app := fun j ↦
      ((cokernel.π ((sheafHFilteredColimitSuccEta Y').app j)).hom.app (op ⊤))
    naturality := fun j j' f ↦ by
      have hπ :
          cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
              (sheafHFilteredColimitSuccQuotient Y').map f =
            ((sheafHFilteredColimitSuccInj Y').map f) ≫
              cokernel.π ((sheafHFilteredColimitSuccEta Y').app j') := by
        dsimp [sheafHFilteredColimitSuccQuotient]
        exact cokernel.π_desc _ _ _
      exact congrArg
        (fun α :
          ((sheafHFilteredColimitSuccInj Y').obj j) ⟶
            (sheafHFilteredColimitSuccQuotient Y').obj j' =>
          α.hom.app (op ⊤)) hπ.symm }

omit [IsFiltered J'] [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)] in
private theorem sheafH_filtered_colimit_succ_Inj_obj_injective (j : J') :
    letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      Limits.HasZeroObject.zero' (TopCat.Sheaf AddCommGrpCat.{u} X)
    Injective ((sheafHFilteredColimitSuccInj Y').obj j) := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    Limits.HasZeroObject.zero' (TopCat.Sheaf AddCommGrpCat.{u} X)
  change
    Injective
      (CategoryTheory.IsGrothendieckAbelian.monoMapFactorizationDataRlp
        (0 : Y'.obj j ⟶ 0)).Z
  infer_instance

/-- The functor of stagewise cokernels of the top-sections maps used in the degree-`1`
filtered-colimit boundary construction. -/
private noncomputable def sheafH_filtered_colimit_h1_cokernelFunctor :
    J' ⥤ AddCommGrpCat.{u} :=
  { obj := fun j ↦ cokernel ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
    map := fun {j j'} f ↦
      cokernel.map
        ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
        ((sheafH_filtered_colimit_h1_gTopNat Y').app j')
        (((sheafHFilteredColimitSuccInj Y').map f).hom.app (op ⊤))
        (((sheafHFilteredColimitSuccQuotient Y').map f).hom.app (op ⊤))
        (by
          simpa [sheafH_filtered_colimit_h1_sectionsFunctor] using
            ((sheafH_filtered_colimit_h1_gTopNat Y').naturality f).symm)
    map_id := fun j ↦ by
      apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
      rw [cokernel.π_desc]
      rw [show (sheafHFilteredColimitSuccQuotient Y').map (𝟙 j) =
          𝟙 ((sheafHFilteredColimitSuccQuotient Y').obj j) by
        simp [sheafHFilteredColimitSuccQuotient, cokernel.map]
      ]
      exact Category.id_comp _
    map_comp := fun {j j' j''} f g ↦ by
      apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
      rw [cokernel.π_desc, ← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
      rw [show (sheafHFilteredColimitSuccQuotient Y').map (f ≫ g) =
          (sheafHFilteredColimitSuccQuotient Y').map f ≫
            (sheafHFilteredColimitSuccQuotient Y').map g by
        simp [sheafHFilteredColimitSuccQuotient, cokernel.map, Functor.map_comp]
      ]
      change (((sheafHFilteredColimitSuccQuotient Y').map f).hom.app (op ⊤) ≫
          ((sheafHFilteredColimitSuccQuotient Y').map g).hom.app (op ⊤)) ≫
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j'') = _
      rfl }

/-- Evaluation at each diagram object identifies the stagewise cokernel functor with the
cokernel of `sheafH_filtered_colimit_h1_gTopNat`. -/
private noncomputable def sheafH_filtered_colimit_h1_cokernelFunctorIso :
    sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅
      cokernel (sheafH_filtered_colimit_h1_gTopNat Y') :=
  NatIso.ofComponents
    (fun j ↦
      (PreservesCokernel.iso
        ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j)
        (sheafH_filtered_colimit_h1_gTopNat Y')).symm)
    (fun {j j'} f ↦ by
      let alpha := sheafH_filtered_colimit_h1_gTopNat Y'
      let ev := CategoryTheory.evaluation J' AddCommGrpCat.{u}
      let e_j := PreservesCokernel.iso (ev.obj j) alpha
      let e_j' := PreservesCokernel.iso (ev.obj j') alpha
      apply (cancel_epi (cokernel.π (alpha.app j))).mp
      have hπj :
          cokernel.π (alpha.app j) ≫ e_j.inv = (cokernel.π alpha).app j := by
        symm
        exact (Iso.eq_comp_inv e_j).2 (by
          change (ev.obj j).map (cokernel.π alpha) ≫ e_j.hom =
            cokernel.π ((ev.obj j).map alpha)
          exact PreservesCokernel.π_iso_hom (ev.obj j) alpha)
      have hπj' :
          cokernel.π (alpha.app j') ≫ e_j'.inv = (cokernel.π alpha).app j' := by
        symm
        exact (Iso.eq_comp_inv e_j').2 (by
          change (ev.obj j').map (cokernel.π alpha) ≫ e_j'.hom =
            cokernel.π ((ev.obj j').map alpha)
          exact PreservesCokernel.π_iso_hom (ev.obj j') alpha)
      change cokernel.π (alpha.app j) ≫
          (sheafH_filtered_colimit_h1_cokernelFunctor Y').map f ≫ e_j'.inv =
        cokernel.π (alpha.app j) ≫ e_j.inv ≫ (cokernel alpha).map f
      dsimp [sheafH_filtered_colimit_h1_cokernelFunctor]
      rw [← Category.assoc, cokernel.π_desc]
      change ((sheafHFilteredColimitSuccQuotient Y').map f).hom.app (op ⊤) ≫
          (cokernel.π (alpha.app j') ≫ e_j'.inv) =
        (cokernel.π (alpha.app j) ≫ e_j.inv) ≫ (cokernel alpha).map f
      exact
        (congrArg
          (fun t ↦ ((sheafHFilteredColimitSuccQuotient Y').map f).hom.app (op ⊤) ≫ t)
          hπj').trans
        (((cokernel.π alpha).naturality f).trans
          (congrArg (fun t ↦ t ≫ (cokernel alpha).map f) hπj).symm))

/-- The stagewise identification of `H¹` with the cokernel of top sections for the
injective-replacement short exact sequence used in the filtered-colimit comparison. -/
private noncomputable def sheafH_filtered_colimit_h1_stageNatIso
    (h_mid : ∀ j, Subsingleton (Sheaf.H ((sheafHFilteredColimitSuccInj Y').obj j) 1)) :
    sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅
      Y' ⋙ sheafCohomologyFunctor X 1 :=
  NatIso.ofComponents
    (fun j ↦ by
      change cokernel ((cokernel.π ((sheafHFilteredColimitSuccEta Y').app j)).hom.app
        (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H (Y'.obj j) 1)
      exact sheafH1CokernelIsoOfSubsingletonMiddle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) (h_mid j))
    (fun {j j'} f ↦ by
      ext y
      let φ := sheafHFilteredColimitSuccStageMapHom (Y' := Y') f
      change AddCommGrpCat.Hom.hom
          (cokernel.map
              ((cokernel.π ((sheafHFilteredColimitSuccEta Y').app j)).hom.app (op ⊤))
              ((cokernel.π ((sheafHFilteredColimitSuccEta Y').app j')).hom.app (op ⊤))
              (φ.τ₂.hom.app (op ⊤)) (φ.τ₃.hom.app (op ⊤))
              (congrArg (fun β => β.hom.app (op ⊤)) φ.comm₂₃.symm) ≫
            (sheafH1CokernelIsoOfSubsingletonMiddle
              (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j') (h_mid j')).hom)
            y =
        AddCommGrpCat.Hom.hom
          ((sheafH1CokernelIsoOfSubsingletonMiddle
              (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) (h_mid j)).hom ≫
            (sheafCohomologyFunctor X 1).map φ.τ₁) y
      exact congrArg (fun m ↦ AddCommGrpCat.Hom.hom m y)
        (sheafH1_cokernel_iso_of_subsingleton_middle_natural
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          φ (h_mid j) (h_mid j')))

variable (c' : Cocone Y') (hc' : IsColimit c')

private theorem sheafH_filtered_colimit_h1_boundary_square
    (hc_sections_inj : IsColimit ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).mapCocone
      (sheafHFilteredColimitSuccInjCocone Y')))
    (hc_sections_q : IsColimit ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).mapCocone
      (sheafHFilteredColimitSuccQuotientCocone Y' c' hc'))) :
    (colim (J := J') (C := AddCommGrpCat.{u})).map
        (sheafH_filtered_colimit_h1_gTopNat Y') ≫
      ((colimit.isColimit (sheafHFilteredColimitSuccQuotient Y' ⋙
          sheafH_filtered_colimit_h1_sectionsFunctor (X := X))).coconePointUniqueUpToIso
        hc_sections_q).hom =
    ((colimit.isColimit (sheafHFilteredColimitSuccInj Y' ⋙
          sheafH_filtered_colimit_h1_sectionsFunctor (X := X))).coconePointUniqueUpToIso
        hc_sections_inj).hom ≫
      (sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).map
        (cokernel.π (sheafHFilteredColimitSuccIota Y' c' hc')) := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Y' c' hc'
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  let eInj := (colimit.isColimit
    (sheafHFilteredColimitSuccInj Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso
      hc_sections_inj
  let eQ := (colimit.isColimit
    (sheafHFilteredColimitSuccQuotient Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso
      hc_sections_q
  change
    (colim (J := J') (C := AddCommGrpCat.{u})).map
        (sheafH_filtered_colimit_h1_gTopNat Y') ≫ eQ.hom =
      eInj.hom ≫ sectionsFunctor.map (cokernel.π ι')
  apply colimit.hom_ext
  intro j
  erw [ι_colimMap_assoc]
  have heQ :
      colimit.ι (sheafHFilteredColimitSuccQuotient Y' ⋙ sectionsFunctor) j ≫
          eQ.hom =
        (sectionsFunctor.mapCocone qCocone).ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (sheafHFilteredColimitSuccQuotient Y' ⋙ sectionsFunctor))
      hc_sections_q j
  have heInj :
      colimit.ι (sheafHFilteredColimitSuccInj Y' ⋙ sectionsFunctor) j ≫
          eInj.hom =
        (sectionsFunctor.mapCocone (sheafHFilteredColimitSuccInjCocone Y')).ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (sheafHFilteredColimitSuccInj Y' ⋙ sectionsFunctor))
      hc_sections_inj j
  have hπ :
      cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ qCocone.ι.app j =
        (sheafHFilteredColimitSuccInjCocone Y').ι.app j ≫ cokernel.π ι' :=
    cokernel.π_desc _ _ _
  have hπ_top :
      (sheafH_filtered_colimit_h1_gTopNat Y').app j ≫
          (sectionsFunctor.mapCocone qCocone).ι.app j =
        (sectionsFunctor.mapCocone (sheafHFilteredColimitSuccInjCocone Y')).ι.app j ≫
          sectionsFunctor.map (cokernel.π ι') := by
    change ((cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
        qCocone.ι.app j).hom.app (op ⊤)) =
      (((sheafHFilteredColimitSuccInjCocone Y').ι.app j ≫
        cokernel.π ι').hom.app (op ⊤))
    exact congrArg
      (fun β : ((sheafHFilteredColimitSuccInj Y').obj j) ⟶ qCocone.pt =>
        β.hom.app (op ⊤))
      hπ
  exact
    (congrArg (fun t ↦ (sheafH_filtered_colimit_h1_gTopNat Y').app j ≫ t) heQ).trans
      (hπ_top.trans
        (congrArg (fun t ↦ t ≫ sectionsFunctor.map (cokernel.π ι')) heInj).symm)

private noncomputable def sheafH_filtered_colimit_h1_global_cokernel_iso
    (h_colim : Subsingleton (Sheaf.H (sheafHFilteredColimitSuccInjCocone Y').pt 1)) :
    cokernel ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).map
      (cokernel.π (sheafHFilteredColimitSuccIota Y' c' hc'))) ≅
        AddCommGrpCat.of (Sheaf.H c'.pt 1) := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Y' c' hc'
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  change cokernel (sectionsFunctor.map (cokernel.π ι')) ≅
    AddCommGrpCat.of (Sheaf.H c'.pt 1)
  change cokernel ((sheafHFilteredColimitSuccShortComplex Y' c' hc').g.hom.app (op ⊤)) ≅
    AddCommGrpCat.of (Sheaf.H (sheafHFilteredColimitSuccShortComplex Y' c' hc').X₁ 1)
  exact sheafH1CokernelIsoOfSubsingletonMiddle
    (sheafH_filtered_colimit_succ_shortExact Y' c' hc') h_colim

end FilteredColimitH1

section FilteredColimitComparison

variable {X : TopCat.{u}} [NoetherianSpace X]
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable (csh : Cocone Ysh) (hcsh : IsColimit csh)
include hcsh

/-- The degree-`1` filtered-colimit comparison isomorphism, obtained by identifying `H¹`
with the cokernel of top sections for the injective-replacement short exact sequence. -/
private noncomputable def sheafH_filtered_colimit_comparison_one_iso :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 1) ≅
      AddCommGrpCat.of (Sheaf.H csh.pt 1) := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafHFilteredColimitSuccInj Ysh
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafHFilteredColimitSuccIota Ysh csh hcsh
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have hInj (j) : Injective (Inj.obj j) :=
    sheafH_filtered_colimit_succ_Inj_obj_injective (Y' := Ysh) j
  have h_mid (j) : Subsingleton (Sheaf.H (Inj.obj j) 1) :=
    @sheafH_subsingleton_of_injective
      (Opens X) _ (Opens.grothendieckTopology X) _ _ (Inj.obj j) (hInj j) 0
  have h_colim :=
    sheafH_filtered_colimit_succ_inj_subsingleton (X := X) (Y' := Ysh) 0 hInj
  haveI : CreatesColimit Inj toPsh := createsFilteredColimit Inj
  haveI hPresInj : PreservesColimit Inj toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Inj toPsh
  have hc_psh_inj : IsColimit (toPsh.mapCocone (colimit.cocone Inj)) :=
    (hPresInj.preserves (colimit.isColimit Inj)).some
  have hc_sections_inj :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI : CreatesColimit (sheafHFilteredColimitSuccQuotient Ysh) toPsh :=
    createsFilteredColimit (sheafHFilteredColimitSuccQuotient Ysh)
  haveI hPresQ : PreservesColimit (sheafHFilteredColimitSuccQuotient Ysh) toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit
      (sheafHFilteredColimitSuccQuotient Ysh) toPsh
  have hc_psh_q :
      IsColimit
        (toPsh.mapCocone (sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh)) :=
    (hPresQ.preserves
      (sheafHFilteredColimitSuccQuotientCoconeIsColimit Ysh csh hcsh)).some
  have hc_sections_q :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_q
  let eInj :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :=
    (colimit.isColimit (sheafHFilteredColimitSuccQuotient Ysh ⋙
      sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let globalIso := by
    simpa [sectionsFunctor, ι'] using
      (sheafH_filtered_colimit_h1_global_cokernel_iso (Y' := Ysh) (c' := csh) (hc' := hcsh) h_colim)
  exact
    (HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid)).symm ≪≫
      HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh) ≪≫
      PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u}))
        (sheafH_filtered_colimit_h1_gTopNat Ysh) ≪≫
      (cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Ysh))
        (sectionsFunctor.map (cokernel.π ι')) eInj eQ (by
          change colim.map (sheafH_filtered_colimit_h1_gTopNat Ysh) ≫ eQ.hom =
            eInj.hom ≫ sectionsFunctor.map (cokernel.π ι')
          exact sheafH_filtered_colimit_h1_boundary_square Ysh csh hcsh
            hc_sections_inj hc_sections_q)) ≪≫
      globalIso

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_hom :
    (sheafH_filtered_colimit_comparison_one_iso
      (Ysh := Ysh) (csh := csh) (hcsh := hcsh)).hom =
      sheafHFilteredColimitComparison Ysh 1 csh := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafHFilteredColimitSuccInj Ysh
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let evTop := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafHFilteredColimitSuccIota Ysh csh hcsh
  have hInj (j) : Injective (Inj.obj j) :=
    sheafH_filtered_colimit_succ_Inj_obj_injective (Y' := Ysh) j
  have h_mid (j) : Subsingleton (Sheaf.H (Inj.obj j) 1) :=
    @sheafH_subsingleton_of_injective
      (Opens X) _ (Opens.grothendieckTopology X) _ _ (Inj.obj j) (hInj j) 0
  have h_colim := sheafH_filtered_colimit_succ_inj_subsingleton (Y' := Ysh) 0 hInj
  haveI : CreatesColimit Inj toPsh := createsFilteredColimit Inj
  haveI hPresInj : PreservesColimit Inj toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Inj toPsh
  have hc_psh_inj : IsColimit (toPsh.mapCocone (colimit.cocone Inj)) :=
    (hPresInj.preserves (colimit.isColimit Inj)).some
  have hc_sections_inj :=
    isColimitOfPreserves evTop hc_psh_inj
  haveI : CreatesColimit (sheafHFilteredColimitSuccQuotient Ysh) toPsh :=
    createsFilteredColimit (sheafHFilteredColimitSuccQuotient Ysh)
  haveI hPresQ : PreservesColimit (sheafHFilteredColimitSuccQuotient Ysh) toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit
      (sheafHFilteredColimitSuccQuotient Ysh) toPsh
  have hc_psh_q :
      IsColimit
        (toPsh.mapCocone (sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh)) :=
    (hPresQ.preserves
      (sheafHFilteredColimitSuccQuotientCoconeIsColimit Ysh csh hcsh)).some
  have hc_sections_q :=
    isColimitOfPreserves evTop hc_psh_q
  let eInj :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :=
    (colimit.isColimit (sheafHFilteredColimitSuccQuotient Ysh ⋙
      sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let α := sheafH_filtered_colimit_h1_gTopNat Ysh
  let mapIso := cokernel.mapIso (f := (colim (C := AddCommGrpCat.{u})).map α)
    (sectionsFunctor.map (cokernel.π ι')) eInj eQ
      (sheafH_filtered_colimit_h1_boundary_square Ysh csh hcsh hc_sections_inj hc_sections_q)
  let globalIso := sheafH_filtered_colimit_h1_global_cokernel_iso Ysh csh hcsh h_colim
  dsimp [sheafH_filtered_colimit_comparison_one_iso]
  refine colimit.hom_ext (fun j ↦ ?_)
  let stageHom := sheafHFilteredColimitSuccStageHom Ysh csh hcsh j
  let appTop {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) := f.hom.app (op ⊤)
  let stageCokMap :=
    cokernel.map (α.app j) (sectionsFunctor.map (cokernel.π ι'))
      (appTop stageHom.τ₂) (appTop stageHom.τ₃) (congrArg appTop stageHom.comm₂₃.symm)
  let cokIso := sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh
  let stageNat := sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid
  have hnat : stageCokMap ≫ globalIso.hom =
      stageNat.hom.app j ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by
    change stageCokMap ≫ globalIso.hom =
      (sheafH1CokernelIsoOfSubsingletonMiddle
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) (h_mid j)).hom ≫
        (sheafCohomologyFunctor X 1).map (csh.ι.app j)
    exact sheafH1_cokernel_iso_of_subsingleton_middle_natural
      (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j)
      (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh) stageHom (h_mid j) h_colim
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [HasColimit.isoOfNatIso_ι_inv_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    colimit_ι_sheafH_filtered_colimit_comparison]
  have hright :
      stageNat.inv.app j ≫ (stageCokMap ≫ globalIso.hom) =
        (sheafCohomologyFunctor X 1).map (csh.ι.app j) :=
    (congrArg (fun f ↦ stageNat.inv.app j ≫ f) hnat).trans
      (Iso.inv_hom_id_app_assoc stageNat j
        ((sheafCohomologyFunctor X 1).map (csh.ι.app j)))
  have hleft :
      (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid).inv.app j ≫
          cokIso.hom.app j ≫ colimit.ι (cokernel α) j ≫
            (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
              mapIso.hom ≫ globalIso.hom =
        (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid).inv.app j ≫
          stageCokMap ≫ globalIso.hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid).inv.app j ≫
            t ≫ globalIso.hom)
        (show cokIso.hom.app j ≫ colimit.ι (cokernel α) j ≫
            (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
              mapIso.hom = stageCokMap from by
      apply (cancel_epi (cokernel.π (α.app j))).mp
      change (cokernel.π (α.app j) ≫ cokIso.hom.app j) ≫
          colimit.ι (cokernel α) j ≫
            (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
              mapIso.hom =
        cokernel.π (α.app j) ≫ stageCokMap
      have hπIso :
          cokernel.π (α.app j) ≫ cokIso.hom.app j = (cokernel.π α).app j := by
        symm
        exact (Iso.eq_comp_inv _).2 <| by
          change ((evaluation J' AddCommGrpCat.{u}).obj j).map (cokernel.π α) ≫
              (PreservesCokernel.iso ((evaluation J' AddCommGrpCat.{u}).obj j) α).hom =
            cokernel.π (((evaluation J' AddCommGrpCat.{u}).obj j).map α)
          exact PreservesCokernel.π_iso_hom
            ((evaluation J' AddCommGrpCat.{u}).obj j) α
      rw [hπIso]
      calc
        (cokernel.π α).app j ≫ colimit.ι (cokernel α) j ≫
            (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
              mapIso.hom =
          colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
            colim.map (cokernel.π α) ≫
              (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
                mapIso.hom := by
            erw [← colimit.ι_map_assoc]
            rfl
        _ = cokernel.π (α.app j) ≫ stageCokMap := by
          trans colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
            (cokernel.π (colim.map α) ≫ mapIso.hom)
          · erw [PreservesCokernel.π_iso_hom_assoc]
            rfl
          · have hmap :
                colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                    (cokernel.π (colim.map α) ≫ mapIso.hom) =
                  colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                    (eQ.hom ≫
                      cokernel.π (sectionsFunctor.map (cokernel.π ι'))) := by
                congr 1
                rw [cokernel.mapIso_hom]
                exact cokernel.π_desc _ _ _
            have hstage :
                colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                    (eQ.hom ≫
                      cokernel.π (sectionsFunctor.map (cokernel.π ι'))) =
                  appTop stageHom.τ₃ ≫
                    cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
                have hstageTop :
                    colimit.ι
                        (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                      eQ.hom =
                    appTop stageHom.τ₃ := by
                  change colimit.ι
                        (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                      eQ.hom =
                    ((sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh).ι.app j).hom.app
                      (op ⊤)
                  exact IsColimit.comp_coconePointUniqueUpToIso_hom
                    (colimit.isColimit
                      (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor))
                    hc_sections_q j
                change (colimit.ι
                      (sheafHFilteredColimitSuccQuotient Ysh ⋙ sectionsFunctor) j ≫
                    eQ.hom) ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) =
                  appTop stageHom.τ₃ ≫
                    cokernel.π (sectionsFunctor.map (cokernel.π ι'))
                exact
                  congrArg
                    (fun t ↦ t ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')))
                    hstageTop
            have hdesc :
                appTop stageHom.τ₃ ≫
                    cokernel.π (sectionsFunctor.map (cokernel.π ι')) =
                  cokernel.π (α.app j) ≫ stageCokMap :=
                (cokernel.π_desc _ _ _).symm
            exact hmap.trans (hstage.trans hdesc))
  change (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid).inv.app j ≫
      cokIso.hom.app j ≫ colimit.ι (cokernel α) j ≫
        (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫
          mapIso.hom ≫ globalIso.hom =
    (sheafCohomologyFunctor X 1).map (csh.ι.app j)
  exact hleft.trans hright

/-- The degree-`0` comparison up to identifying `H⁰` with global sections. -/
private noncomputable def sheafH_filtered_colimit_zero_sections_iso :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 0) ≅
      (sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).obj csh.pt := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let h0Iso :
      Ysh ⋙ sheafCohomologyFunctor X 0 ≅ Ysh ⋙ sectionsFunctor :=
    Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  haveI : CreatesColimit Ysh toPsh :=
    createsFilteredColimit Ysh
  haveI hPres : PreservesColimit Ysh toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Ysh toPsh
  have hc_psh : IsColimit (toPsh.mapCocone csh) :=
    (hPres.preserves hcsh).some
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
  exact
    HasColimit.isoOfNatIso h0Iso ≪≫
      (colimit.isColimit (Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections

/-- The degree-`0` filtered-colimit comparison isomorphism, obtained from global sections. -/
private noncomputable def sheafH_filtered_colimit_comparison_zero_iso :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 0) ≅ AddCommGrpCat.of (Sheaf.H csh.pt 0) :=
  sheafH_filtered_colimit_zero_sections_iso (Ysh := Ysh) csh hcsh ≪≫
    ((sheafH0EquivSections csh.pt).toAddCommGrpIso).symm

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_hom :
    (sheafH_filtered_colimit_comparison_zero_iso
      (Ysh := Ysh) (csh := csh) (hcsh := hcsh)).hom =
      sheafHFilteredColimitComparison Ysh 0 csh := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  haveI : CreatesColimit Ysh toPsh :=
    createsFilteredColimit Ysh
  haveI hPres : PreservesColimit Ysh toPsh :=
    preservesColimit_of_createsColimit_and_hasColimit Ysh toPsh
  have hc_psh : IsColimit (toPsh.mapCocone csh) :=
    (hPres.preserves hcsh).some
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
  apply colimit.hom_ext
  intro j
  simp only [sheafH_filtered_colimit_comparison_zero_iso,
    sheafH_filtered_colimit_zero_sections_iso, Iso.trans_hom, Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  let h0Iso :=
    Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))
  let h0Symm :
      sectionsFunctor.obj csh.pt ⟶ AddCommGrpCat.of (Sheaf.H csh.pt 0) :=
    ((sheafH0EquivSections csh.pt).toAddCommGrpIso).symm.hom
  let e :=
    (colimit.isColimit (Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections
  have hsections :
      colimit.ι (Ysh ⋙ sectionsFunctor) j ≫ e.hom ≫ h0Symm =
        sectionsFunctor.map (csh.ι.app j) ≫ h0Symm :=
    colimit.comp_coconePointUniqueUpToIso_hom_assoc hc_sections j h0Symm
  have hleft :
      h0Iso.hom.app j ≫ colimit.ι (Ysh ⋙ sectionsFunctor) j ≫ e.hom ≫ h0Symm =
        h0Iso.hom.app j ≫ sectionsFunctor.map (csh.ι.app j) ≫ h0Symm :=
    congrArg (fun t ↦ h0Iso.hom.app j ≫ t) hsections
  have hright :
      h0Iso.hom.app j ≫ sectionsFunctor.map (csh.ι.app j) ≫ h0Symm =
        (sheafCohomologyFunctor X 0).map (csh.ι.app j) := by
    ext x
    change (sheafH0EquivSections csh.pt).symm
        (ConcreteCategory.hom ((csh.ι.app j).hom.app (op ⊤))
          (sheafH0EquivSections (Ysh.obj j) x)) =
      ConcreteCategory.hom ((sheafCohomologyFunctor X 0).map (csh.ι.app j)) x
    apply (sheafH0EquivSections csh.pt).injective
    rw [AddEquiv.apply_symm_apply]
    change ConcreteCategory.hom ((csh.ι.app j).hom.app (op ⊤))
        (sheafH0EquivSections (Ysh.obj j) x) =
      sheafH0EquivSections csh.pt
        (x.comp (Ext.mk₀ (csh.ι.app j)) (add_zero 0))
    exact
      (sheafH0EquivSections_natural (f := csh.ι.app j) (x := x)).symm
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  change h0Iso.hom.app j ≫ colimit.ι (Ysh ⋙ sectionsFunctor) j ≫ e.hom ≫ h0Symm =
    (sheafCohomologyFunctor X 0).map (csh.ι.app j)
  exact hleft.trans hright

private theorem sheafH_filtered_colimit_comparison_isIso_zero :
    IsIso (sheafHFilteredColimitComparison Ysh 0 csh) := by
  rw [← sheafH_filtered_colimit_comparison_zero_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_one :
    IsIso (sheafHFilteredColimitComparison Ysh 1 csh) := by
  rw [← sheafH_filtered_colimit_comparison_one_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_succ_succ
    (m : ℕ)
    (ih :
      ∀ {J'' : Type u} [SmallCategory J''] [IsFiltered J'']
        (Ysh : J'' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
        (csh : Cocone Ysh) (_ : IsColimit csh),
        IsIso (sheafHFilteredColimitComparison Ysh (m + 1) csh)) :
    IsIso (sheafHFilteredColimitComparison Ysh (m + 1 + 1) csh) := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafHFilteredColimitSuccInj Ysh
  let injCocone := sheafHFilteredColimitSuccInjCocone Ysh
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh
  haveI :
      IsIso
        (sheafHFilteredColimitComparison
          (sheafHFilteredColimitSuccQuotient Ysh) (m + 1) qCocone) :=
    ih
      (Ysh := sheafHFilteredColimitSuccQuotient Ysh) (csh := qCocone)
      (sheafHFilteredColimitSuccQuotientCoconeIsColimit Ysh csh hcsh)
  have hInj (j) : Injective (Inj.obj j) :=
    sheafH_filtered_colimit_succ_Inj_obj_injective (Y' := Ysh) j
  have h_mid (r) (j) : Subsingleton (Sheaf.H (Inj.obj j) (r + 1)) :=
    @sheafH_subsingleton_of_injective
      (Opens X) _ (Opens.grothendieckTopology X) _ _ (Inj.obj j) (hInj j) r
  have h_colim (r) : Subsingleton (Sheaf.H injCocone.pt (r + 1)) := by
    simpa [injCocone] using sheafH_filtered_colimit_succ_inj_subsingleton (Y' := Ysh) r hInj
  let domainIso :=
    sheafHFilteredColimitSuccShiftDomainIso Ysh (m + 1) (h_mid m) (h_mid (m + 1))
  let codomainIso :=
    sheafHFilteredColimitSuccShiftCodomainIso
      Ysh csh hcsh (m + 1) (h_colim m) (h_colim (m + 1))
  exact IsIso.of_isIso_fac_left (by
    simpa [domainIso, codomainIso, qCocone] using
      sheafH_filtered_colimit_comparison_succ_compatibility
        (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (n := m + 1)
        (h_mid m) (h_mid (m + 1)) (h_colim m) (h_colim (m + 1)))

end FilteredColimitComparison

private theorem sheafH_filtered_colimit_comparison_isIso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (n : ℕ) :
    IsIso (sheafHFilteredColimitComparison Ysh n csh) := by
  let P : ℕ → Prop := fun n ↦
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (csh : Cocone Ysh) (hcsh : IsColimit csh),
      IsIso (sheafHFilteredColimitComparison Ysh n csh)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro J' _ _ Ysh csh hcsh
        exact sheafH_filtered_colimit_comparison_isIso_zero Ysh csh hcsh
    | succ n ih =>
        cases n with
        | zero =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_one Ysh csh hcsh
        | succ m =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_succ_succ
              (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (m := m) ih
  exact hP n Ysh csh hcsh

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces:
    the canonical comparison `colim H^n(F_j) ≅ H^n(colim F_j)` is an isomorphism. -/
noncomputable def sheafHPreservesFilteredColimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ) :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ≅ AddCommGrpCat.of (Sheaf.H c'.pt n) := by
  haveI : IsIso (sheafHFilteredColimitComparison Y' n c') :=
    sheafH_filtered_colimit_comparison_isIso Y' c' hc' n
  exact asIso (sheafHFilteredColimitComparison Y' n c')
