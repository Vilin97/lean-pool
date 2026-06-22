/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import Mathlib.Topology.NoetherianSpace
import LeanPool.GrothendieckVanishing.PresheafFilteredColimitGeneral
import LeanPool.GrothendieckVanishing.ClosedImmersionCohomology

/-!
# Noetherian filtered-colimit infrastructure for sheaf cohomology

Building blocks for the proof that sheaf cohomology commutes with filtered colimits on
Noetherian spaces:

* creation of filtered colimits by `sheafToPresheaf` (`createsFilteredColimit`);
* flasqueness of filtered colimits of flasque sheaves (`isFlasque_filtered_colimit`);
* successor-stage dimension shifts and presheaf-boundary comparison maps used in the
  degree-`n+1` colimit comparison.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- On a Noetherian space, a filtered colimit cocone of presheaves is a sheaf if all
    diagram objects are sheaves. Proof: compactness reduces the sheaf condition to finite
    covers, then filtered colimit merging passes from per-piece data to glued data. -/
theorem isSheaf_of_isColimit_of_isSheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    (c : Cocone P) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (↑(iSup U) : Set X)).elim_finite_subcover
    (fun i ↦ ↑(U i)) (fun i ↦ (U i).isOpen) (by simp [Opens.coe_iSup])
  have hsup_le : iSup U ≤ ⨆ i ∈ t, U i := by
    rw [SetLike.le_def]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hi, hxi⟩⟩
  exact colimit_existsUnique_gluing_of_compatible_finite_subcover
    P hP hc U sf hcompat hsup_le

/-- On a Noetherian space, `sheafToPresheaf` creates filtered colimits of sheaves by
    applying `isSheaf_of_isColimit_of_isSheaf` to the underlying presheaf diagram. -/
@[implicit_reducible]
noncomputable def createsFilteredColimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    CreatesColimit Y' (sheafToPresheaf _ _) :=
  Sheaf.createsColimitOfIsSheaf Y' (fun c hc ↦
    isSheaf_of_isColimit_of_isSheaf
      (P := Y' ⋙ sheafToPresheaf _ _)
      (hP := fun j ↦ (Y'.obj j).property)
      (c := c) (hc := hc))

/-! ### Filtered colimits of flasque sheaves

On Noetherian spaces, `sheafToPresheaf` creates filtered colimits, so restrictions of
filtered colimits are colimits of restrictions. Filtered colimits in `AddCommGrpCat`
preserve surjections, hence stagewise flasque sheaves have flasque colimit. -/

/-- Filtered colimits of stagewise flasque sheaves on Noetherian spaces are flasque. -/
theorem isFlasque_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (hFlasque : ∀ j, IsFlasqueSheaf (F.obj j))
    {c : Cocone F} (hc : IsColimit c) :
    IsFlasqueSheaf c.pt := by
  let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  haveI : CreatesColimit F G :=
    createsFilteredColimit F
  haveI : PreservesColimit F G :=
    preservesColimit_of_createsColimit_and_hasColimit F G
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro b
  have hc_presheaf : IsColimit (G.mapCocone c) :=
    isColimitOfPreserves G hc
  have hc_U := isColimitOfPreserves
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
    hc_presheaf
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ hc_U b
  obtain ⟨a₀, ha₀⟩ :=
    (AddCommGrpCat.epi_iff_surjective _).mp ((hFlasque j₀) i) b₀
  refine ⟨ConcreteCategory.hom ((c.ι.app j₀).hom.app (op V)) a₀, ?_⟩
  rw [show ConcreteCategory.hom (c.pt.obj.map i.op)
      (ConcreteCategory.hom ((c.ι.app j₀).hom.app (op V)) a₀) =
    ConcreteCategory.hom ((c.ι.app j₀).hom.app (op U))
      (ConcreteCategory.hom ((F.obj j₀).obj.map i.op) a₀) from
    congrFun (congrArg DFunLike.coe
      (congrArg ConcreteCategory.hom ((c.ι.app j₀).hom.naturality i.op).symm)) a₀]
  rw [ha₀]
  exact hb₀

/-! ### Sheaf cohomology and filtered colimits

The formal comparison map
`sheafHFilteredColimitComparison : colim H^n(F_j) ⟶ H^n(colim F_j)`
is defined for any small diagram and cocone by `colimit.desc`.

The genuinely geometric input starts afterwards:
- `sheafHPreservesFilteredColimits`: the filtered-colimit comparison isomorphism
  for a sheaf diagram and a colimit cocone. -/

section SheafHFilteredColimitSucc

variable {X : TopCat.{u}}
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The arrow diagram used in the successor-step dimension-shift construction. -/
noncomputable def sheafHFilteredColimitSuccToArrow :
    J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  { obj := fun j ↦ Arrow.mk (0 : Y'.obj j ⟶ 0)
    map := fun f ↦ Arrow.homMk (Y'.map f) (𝟙 0) (by
      change Y'.map f ≫ (0 : Y'.obj _ ⟶ 0) = (0 : Y'.obj _ ⟶ 0) ≫ 𝟙 0
      rw [zero_comp, comp_zero])
    map_id := fun j ↦ by ext <;> aesop_cat
    map_comp := fun f g ↦ by ext <;> aesop_cat }

/-- Objectwise injective envelopes coming from functorial factorization of `0 : Y_j ⟶ 0`. -/
noncomputable def sheafHFilteredColimitSuccInj :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafHFilteredColimitSuccToArrow Y' ⋙
    (MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp).Z

/-- The natural monomorphism from the original diagram into the injective replacement. -/
noncomputable def sheafHFilteredColimitSuccEta :
    Y' ⟶ sheafHFilteredColimitSuccInj Y' :=
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  { app := fun j ↦ ffData.i.app ((sheafHFilteredColimitSuccToArrow Y').obj j)
    naturality := fun _ _ f ↦
      ffData.i.naturality ((sheafHFilteredColimitSuccToArrow Y').map f) }

omit [IsFiltered J'] in
theorem sheafH_filtered_colimit_succ_eta_mono (j : J') :
    Mono ((sheafHFilteredColimitSuccEta Y').app j) := by
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  exact ffData.hi ((sheafHFilteredColimitSuccToArrow Y').obj j)

/-- The colimit cocone of the injective replacement diagram. -/
noncomputable def sheafHFilteredColimitSuccInjCocone :
    Cocone (sheafHFilteredColimitSuccInj Y') :=
  colimit.cocone (sheafHFilteredColimitSuccInj Y')

/-- The cocone obtained by composing the original cocone maps with the injective
replacement. -/
noncomputable def sheafHFilteredColimitSuccIotaCocone : Cocone Y' :=
  Cocone.mk (sheafHFilteredColimitSuccInjCocone Y').pt
    { app := fun j ↦
        (sheafHFilteredColimitSuccEta Y').app j ≫
          (sheafHFilteredColimitSuccInjCocone Y').ι.app j
      naturality := fun j j' f ↦ by
        rw [← Category.assoc, (sheafHFilteredColimitSuccEta Y').naturality f]
        exact congrArg (fun t ↦ (sheafHFilteredColimitSuccEta Y').app j ≫ t)
          ((sheafHFilteredColimitSuccInjCocone Y').w f) }

/-- The induced map from the colimit of the original diagram to the colimit of its injective
replacement. -/
noncomputable def sheafHFilteredColimitSuccIota
    (c' : Cocone Y') (hc' : IsColimit c') :
    c'.pt ⟶ (sheafHFilteredColimitSuccInjCocone Y').pt :=
  hc'.desc (sheafHFilteredColimitSuccIotaCocone Y')

theorem sheafH_filtered_colimit_succ_iota_fac
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    c'.ι.app j ≫ sheafHFilteredColimitSuccIota Y' c' hc' =
      (sheafHFilteredColimitSuccEta Y').app j ≫
        (sheafHFilteredColimitSuccInjCocone Y').ι.app j :=
  hc'.fac (sheafHFilteredColimitSuccIotaCocone Y') j

noncomputable instance sheafH_filtered_colimit_succ_iota_mono
    (c' : Cocone Y') (hc' : IsColimit c') :
    Mono (sheafHFilteredColimitSuccIota Y' c' hc') := by
  haveI : ∀ j, Mono ((sheafHFilteredColimitSuccEta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y')
  haveI : Mono (sheafHFilteredColimitSuccEta Y') := NatTrans.mono_of_mono_app _
  exact colim.map_mono' (sheafHFilteredColimitSuccEta Y') hc'
    (colimit.isColimit (sheafHFilteredColimitSuccInj Y'))
    (sheafHFilteredColimitSuccIota Y' c' hc')
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc')

/-- The short exact sequence on colimit objects obtained from the injective replacement. -/
noncomputable def sheafHFilteredColimitSuccShortComplex
    (c' : Cocone Y') (hc' : IsColimit c') :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')

theorem sheafH_filtered_colimit_succ_shortExact
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafHFilteredColimitSuccShortComplex Y' c' hc').ShortExact := by
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  change (ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι')) inferInstance inferInstance

/-- The quotient diagram obtained by objectwise cokernels of the injective replacement maps. -/
noncomputable def sheafHFilteredColimitSuccQuotient :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  { obj := fun j ↦ cokernel ((sheafHFilteredColimitSuccEta Y').app j)
    map := fun {j j'} f ↦
      cokernel.map _ _
        (Y'.map f) ((sheafHFilteredColimitSuccInj Y').map f)
        ((sheafHFilteredColimitSuccEta Y').naturality f).symm
    map_id := fun j ↦ by aesop_cat
    map_comp := fun {j j' j''} f g ↦ by ext; simp [cokernel.map, Functor.map_comp] }

/-- The quotient cocone on the cokernel diagram induced by the colimit short exact sequence. -/
noncomputable def sheafHFilteredColimitSuccQuotientCocone
    (c' : Cocone Y') (hc' : IsColimit c') :
    Cocone (sheafHFilteredColimitSuccQuotient Y') :=
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  let S := sheafHFilteredColimitSuccShortComplex Y' c' hc'
  Cocone.mk S.X₃
    { app := fun j ↦
        cokernel.map ((sheafHFilteredColimitSuccEta Y').app j) ι'
          (c'.ι.app j) ((sheafHFilteredColimitSuccInjCocone Y').ι.app j)
          (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j).symm
      naturality := fun j j' f ↦ by
        apply (cancel_epi (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j))).mp
        conv_lhs =>
          simp [sheafHFilteredColimitSuccQuotient, cokernel.map, Category.assoc]
        conv_rhs =>
          simp [sheafHFilteredColimitSuccQuotient, cokernel.map, Category.assoc]
        change
          (sheafHFilteredColimitSuccInj Y').map f ≫
              (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j') ≫
                cokernel.desc ((sheafHFilteredColimitSuccEta Y').app j')
                  (((sheafHFilteredColimitSuccInjCocone Y').ι.app j') ≫
                    cokernel.π ι') _) =
            cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
              cokernel.desc ((sheafHFilteredColimitSuccEta Y').app j)
                (((sheafHFilteredColimitSuccInjCocone Y').ι.app j) ≫
                  cokernel.π ι') _
        rw [cokernel.π_desc]
        rw [cokernel.π_desc]
        exact congrArg (fun t ↦ t ≫ cokernel.π ι')
          ((sheafHFilteredColimitSuccInjCocone Y').w f) }

private noncomputable def sheafH_filtered_colimit_succ_liftedCocone
    (s : Cocone (sheafHFilteredColimitSuccQuotient Y')) :
    Cocone (sheafHFilteredColimitSuccInj Y') :=
  Cocone.mk s.pt
    { app := fun j ↦
        cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j
      naturality := fun j j' a ↦ by
        have hdesc :
            cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
                (sheafHFilteredColimitSuccQuotient Y').map a =
            (sheafHFilteredColimitSuccInj Y').map a ≫
                cokernel.π ((sheafHFilteredColimitSuccEta Y').app j') := by
          simp [sheafHFilteredColimitSuccQuotient]
        rw [← Category.assoc, ← hdesc]
        exact congrArg (fun t ↦
          cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ t) (s.w a) }

omit [IsFiltered J'] in
@[simp]
private theorem sheafH_filtered_colimit_succ_liftedCocone_ι_app
    (s : Cocone (sheafHFilteredColimitSuccQuotient Y')) (j : J') :
    (sheafH_filtered_colimit_succ_liftedCocone Y' s).ι.app j =
      cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j := rfl

/-- The quotient cocone obtained from the stagewise injective replacements is colimiting. -/
noncomputable def sheafHFilteredColimitSuccQuotientCoconeIsColimit
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsColimit (sheafHFilteredColimitSuccQuotientCocone Y' c' hc') := by
  let Inj := sheafHFilteredColimitSuccInj Y'
  let injCocone := sheafHFilteredColimitSuccInjCocone Y'
  let qCocone := sheafHFilteredColimitSuccQuotientCocone Y' c' hc'
  let ι' := sheafHFilteredColimitSuccIota Y' c' hc'
  let injColim := colimit.isColimit Inj
  have hπ (j) : cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ qCocone.ι.app j =
      injCocone.ι.app j ≫ cokernel.π ι' := cokernel.π_desc _ _ _
  exact
  { desc := fun s ↦
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      cokernel.desc ι' (injColim.desc lifted) (hc'.hom_ext fun j ↦ by
        have hfac_lifted :
            injCocone.ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j := by
          simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
            sheafHFilteredColimitSuccInjCocone] using injColim.fac lifted j
        change c'.ι.app j ≫ sheafHFilteredColimitSuccIota Y' c' hc' ≫
            injColim.desc lifted = c'.ι.app j ≫ 0
        rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j]
        have hzero :
            (sheafHFilteredColimitSuccEta Y').app j ≫
                ((sheafHFilteredColimitSuccInjCocone Y').ι.app j ≫
                  injColim.desc lifted) =
              c'.ι.app j ≫ 0 := by
          rw [hfac_lifted]
          change
            (((sheafHFilteredColimitSuccEta Y').app j ≫
                cokernel.π ((sheafHFilteredColimitSuccEta Y').app j)) ≫
              s.ι.app j) = c'.ι.app j ≫ 0
          rw [cokernel.condition, zero_comp, comp_zero]
        exact hzero)
    fac := fun s j ↦ (cancel_epi (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j))).mp (by
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      have hfac_lifted :
          injCocone.ι.app j ≫ injColim.desc lifted =
            cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j := by
        simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
          sheafHFilteredColimitSuccInjCocone] using injColim.fac lifted j
      have hι : ι' ≫ injColim.desc lifted = 0 :=
        hc'.hom_ext fun k ↦ by
          have hfac_lifted_k :
              injCocone.ι.app k ≫ injColim.desc lifted =
                cokernel.π ((sheafHFilteredColimitSuccEta Y').app k) ≫ s.ι.app k := by
            simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
              sheafHFilteredColimitSuccInjCocone] using injColim.fac lifted k
          change c'.ι.app k ≫ sheafHFilteredColimitSuccIota Y' c' hc' ≫
              injColim.desc lifted = c'.ι.app k ≫ 0
          rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' k]
          have hzero :
              (sheafHFilteredColimitSuccEta Y').app k ≫
                  ((sheafHFilteredColimitSuccInjCocone Y').ι.app k ≫
                    injColim.desc lifted) =
                c'.ι.app k ≫ 0 := by
            rw [hfac_lifted_k]
            change
              (((sheafHFilteredColimitSuccEta Y').app k ≫
                  cokernel.π ((sheafHFilteredColimitSuccEta Y').app k)) ≫
                s.ι.app k) = c'.ι.app k ≫ 0
            rw [cokernel.condition, zero_comp, comp_zero]
          exact hzero
      change (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
          qCocone.ι.app j) ≫ cokernel.desc ι' (injColim.desc lifted) _ =
        cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j
      rw [hπ j]
      change (injCocone.ι.app j ≫ cokernel.π ι') ≫
          cokernel.desc ι' (injColim.desc lifted) hι =
        cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j
      have hdesc :
          cokernel.π ι' ≫ cokernel.desc ι' (injColim.desc lifted) hι =
            injColim.desc lifted := by
        rw [cokernel.π_desc]
      exact (congrArg (fun t ↦ injCocone.ι.app j ≫ t) hdesc).trans hfac_lifted)
    uniq := fun s m hm ↦ (cancel_epi (cokernel.π ι')).mp (by
      rw [cokernel.π_desc]
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      exact injColim.hom_ext fun j ↦ by
        have hπ' :
            (colimit.cocone Inj).ι.app j ≫ cokernel.π ι' =
              cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ qCocone.ι.app j := by
          change injCocone.ι.app j ≫ cokernel.π ι' =
            cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ qCocone.ι.app j
          exact (hπ j).symm
        have hfac_lifted' :
            (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ s.ι.app j := by
          simpa [lifted] using injColim.fac lifted j
        change ((colimit.cocone Inj).ι.app j ≫ cokernel.π ι') ≫ m =
          (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted
        rw [hπ']
        have hmq : qCocone.ι.app j ≫ m = s.ι.app j := by
          simpa [qCocone] using hm j
        have htarget :
            cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫
                (qCocone.ι.app j ≫ m) =
              (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted :=
          (congrArg
            (fun t ↦ cokernel.π ((sheafHFilteredColimitSuccEta Y').app j) ≫ t)
            hmq).trans hfac_lifted'.symm
        exact htarget) }

omit [IsFiltered J'] in
theorem sheafH_filtered_colimit_succ_stage_shortExact (j : J') :
    (ShortComplex.mk ((sheafHFilteredColimitSuccEta Y').app j)
      (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j))
      (cokernel.condition ((sheafHFilteredColimitSuccEta Y').app j))).ShortExact := by
  haveI : Mono ((sheafHFilteredColimitSuccEta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y') j
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel ((sheafHFilteredColimitSuccEta Y').app j)))
    inferInstance inferInstance

/-- The morphism between stagewise short exact sequences induced by a transition map in the
    filtered diagram. -/
noncomputable def sheafHFilteredColimitSuccStageMapHom
    {j j' : J'} (f : j ⟶ j') :
    ShortComplex.mk ((sheafHFilteredColimitSuccEta Y').app j)
        (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j))
        (cokernel.condition ((sheafHFilteredColimitSuccEta Y').app j)) ⟶
      ShortComplex.mk ((sheafHFilteredColimitSuccEta Y').app j')
        (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j'))
        (cokernel.condition ((sheafHFilteredColimitSuccEta Y').app j')) :=
  ShortComplex.homMk
    (Y'.map f)
    ((sheafHFilteredColimitSuccInj Y').map f)
    ((sheafHFilteredColimitSuccQuotient Y').map f)
    ((sheafHFilteredColimitSuccEta Y').naturality f)
    (cokernel.π_desc _ _ _).symm

/-- The morphism from the stagewise short exact sequence to the colimit short exact sequence. -/
noncomputable def sheafHFilteredColimitSuccStageHom
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    ShortComplex.mk ((sheafHFilteredColimitSuccEta Y').app j)
        (cokernel.π ((sheafHFilteredColimitSuccEta Y').app j))
        (cokernel.condition ((sheafHFilteredColimitSuccEta Y').app j)) ⟶
      sheafHFilteredColimitSuccShortComplex Y' c' hc' :=
  ShortComplex.homMk
    (c'.ι.app j)
    ((sheafHFilteredColimitSuccInjCocone Y').ι.app j)
    ((sheafHFilteredColimitSuccQuotientCocone Y' c' hc').ι.app j)
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j)
    (cokernel.π_desc _ _ _).symm

/-- The stagewise dimension-shift natural isomorphism between the quotient diagram in degree
    `n` and the original diagram in degree `n + 1`. -/
noncomputable def sheafHFilteredColimitSuccShiftNatIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafHFilteredColimitSuccInj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafHFilteredColimitSuccInj Y').obj j) (n + 1))) :
    sheafHFilteredColimitSuccQuotient Y' ⋙ sheafCohomologyFunctor X n ≅
      Y' ⋙ sheafCohomologyFunctor X (n + 1) :=
  NatIso.ofComponents
    (fun j ↦
      sheafHSuccIsoOfSubsingletonMiddle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) n
        (h_mid_n j) (h_mid_succ j))
    (fun {j j'} f ↦ by
      ext y
      let φ := sheafHFilteredColimitSuccStageMapHom (Y' := Y') f
      change AddCommGrpCat.Hom.hom
          ((sheafCohomologyFunctor X n).map φ.τ₃ ≫
            (sheafHSuccIsoOfSubsingletonMiddle
              (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j') n
              (h_mid_n j') (h_mid_succ j')).hom) y =
        AddCommGrpCat.Hom.hom
          ((sheafHSuccIsoOfSubsingletonMiddle
              (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) n
              (h_mid_n j) (h_mid_succ j)).hom ≫
            (sheafCohomologyFunctor X (n + 1)).map φ.τ₁) y
      exact congrArg (fun m ↦ AddCommGrpCat.Hom.hom m y)
        ((sheafH_succ_iso_of_subsingleton_middle_natural
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          φ n (h_mid_n j) (h_mid_succ j) (h_mid_n j') (h_mid_succ j')).symm))

/-- The induced colimit isomorphism from the successor-step stagewise dimension shift. -/
noncomputable def sheafHFilteredColimitSuccShiftDomainIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafHFilteredColimitSuccInj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafHFilteredColimitSuccInj Y').obj j) (n + 1))) :
    colimit (sheafHFilteredColimitSuccQuotient Y' ⋙ sheafCohomologyFunctor X n) ≅
      colimit (Y' ⋙ sheafCohomologyFunctor X (n + 1)) :=
  HasColimit.isoOfNatIso (sheafHFilteredColimitSuccShiftNatIso Y' n h_mid_n h_mid_succ)

/-- The colimit-level dimension-shift isomorphism for the short exact sequence obtained from
    the injective replacement of the filtered colimit cocone. -/
noncomputable def sheafHFilteredColimitSuccShiftCodomainIso
    (c' : Cocone Y') (hc' : IsColimit c') (n : ℕ)
    (h_colim_n :
      Subsingleton (Sheaf.H (sheafHFilteredColimitSuccInjCocone Y').pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H (sheafHFilteredColimitSuccInjCocone Y').pt (n + 1))) :
    AddCommGrpCat.of
        (Sheaf.H (sheafHFilteredColimitSuccQuotientCocone Y' c' hc').pt n) ≅
      AddCommGrpCat.of (Sheaf.H c'.pt (n + 1)) :=
  sheafHSuccIsoOfSubsingletonMiddle
    (sheafH_filtered_colimit_succ_shortExact Y' c' hc') n h_colim_n h_colim_succ

/-- The filtered-colimit successor-step vanishing lemma for the injective replacement:
the middle term of the induced short exact sequence has trivial cohomology in degree `n + 1`. -/
theorem sheafH_filtered_colimit_succ_inj_subsingleton
    [NoetherianSpace X] (n : ℕ)
    (hInj : ∀ j, Injective ((sheafHFilteredColimitSuccInj Y').obj j)) :
    Subsingleton (Sheaf.H (sheafHFilteredColimitSuccInjCocone Y').pt (n + 1)) := by
  let Inj := sheafHFilteredColimitSuccInj Y'
  let injCocone := sheafHFilteredColimitSuccInjCocone Y'
  have hFlasque : IsFlasqueSheaf injCocone.pt := fun i ↦ by
    simpa [Inj, injCocone] using
      (isFlasque_filtered_colimit
        (F := Inj)
        (hFlasque := fun j ↦ by
          letI : Injective (Inj.obj j) := hInj j
          exact fun {_ _} i ↦ (isFlasque_of_injective (Inj.obj j)) i)
        (c := injCocone)
        (hc := colimit.isColimit Inj)) i
  simpa [injCocone] using
    (sheafH_subsingleton_of_flasque X injCocone.pt hFlasque n)

end SheafHFilteredColimitSucc

/-- The canonical comparison morphism `colim H^n(F_j) ⟶ H^n(colim F_j)` induced by a cocone. -/
noncomputable def sheafHFilteredColimitComparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ⟶ AddCommGrpCat.of (Sheaf.H c'.pt n) :=
  colimit.desc _ ((sheafCohomologyFunctor X n).mapCocone c')

@[simp] theorem colimit_ι_sheafH_filtered_colimit_comparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (j : J') :
    colimit.ι (Y' ⋙ sheafCohomologyFunctor X n) j ≫
        sheafHFilteredColimitComparison Y' n c' =
      (sheafCohomologyFunctor X n).map (c'.ι.app j) :=
  colimit.ι_desc ((sheafCohomologyFunctor X n).mapCocone c') j

/-- Successor-step compatibility for the filtered-colimit comparison map: whenever the
associated sheaf diagram and its colimit have vanishing injective-replacement cohomology in
degrees `n` and `n + 1`, the degree-`n + 1` comparison is conjugate to the degree-`n`
comparison for the quotient diagram. -/
theorem sheafH_filtered_colimit_comparison_succ_compatibility
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (n : ℕ)
    (h_mid_n : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafHFilteredColimitSuccInj Ysh).obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafHFilteredColimitSuccInj Ysh).obj j) (n + 1)))
    (h_colim_n :
      Subsingleton (Sheaf.H
        (sheafHFilteredColimitSuccInjCocone Ysh).pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H
        (sheafHFilteredColimitSuccInjCocone Ysh).pt (n + 1))) :
    (sheafHFilteredColimitSuccShiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafHFilteredColimitComparison Ysh (n + 1) csh =
      sheafHFilteredColimitComparison (sheafHFilteredColimitSuccQuotient Ysh) n
        (sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh) ≫
      (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom := by
  apply colimit.hom_ext
  intro j
  rw [show (sheafHFilteredColimitSuccShiftDomainIso Ysh n h_mid_n h_mid_succ).hom =
      (HasColimit.isoOfNatIso (sheafHFilteredColimitSuccShiftNatIso Ysh n
        h_mid_n h_mid_succ)).hom from rfl]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  rw [show
      colimit.ι (sheafHFilteredColimitSuccQuotient Ysh ⋙ sheafCohomologyFunctor X n) j ≫
          sheafHFilteredColimitComparison (sheafHFilteredColimitSuccQuotient Ysh) n
            (sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh) ≫
        (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
        ((sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh).ι.app j) ≫
      (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom from by
    rw [← Category.assoc]
    rw [colimit_ι_sheafH_filtered_colimit_comparison]
    rfl]
  change
    (sheafHSuccIsoOfSubsingletonMiddle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) n
        (h_mid_n j) (h_mid_succ j)).hom ≫
      (sheafCohomologyFunctor X (n + 1)).map (csh.ι.app j) =
    (sheafCohomologyFunctor X n).map
        ((sheafHFilteredColimitSuccQuotientCocone Ysh csh hcsh).ι.app j) ≫
      (sheafHFilteredColimitSuccShiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom
  let φ := sheafHFilteredColimitSuccStageHom Ysh csh hcsh j
  change
    (sheafHSuccIsoOfSubsingletonMiddle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) n
        (h_mid_n j) (h_mid_succ j)).hom ≫
      (sheafCohomologyFunctor X (n + 1)).map φ.τ₁ =
    (sheafCohomologyFunctor X n).map φ.τ₃ ≫
      (sheafHSuccIsoOfSubsingletonMiddle
        (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh) n
        h_colim_n h_colim_succ).hom
  exact sheafH_succ_iso_of_subsingleton_middle_natural
    (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j)
    (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
    φ n (h_mid_n j) (h_mid_succ j) h_colim_n h_colim_succ
