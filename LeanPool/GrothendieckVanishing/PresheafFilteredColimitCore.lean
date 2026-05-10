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
  have hPres : PreservesColimit F G :=
    preservesColimit_of_createsColimit_and_hasColimit F G
  letI : PreservesColimit F G := hPres
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
`sheafH_filtered_colimit_comparison : colim H^n(F_j) ⟶ H^n(colim F_j)`
is defined for any small diagram and cocone by `colimit.desc`.

The genuinely geometric input starts afterwards:
- `sheafH_preserves_filtered_colimits`: the filtered-colimit comparison isomorphism
  for a sheaf diagram and a colimit cocone. -/

section SheafHFilteredColimitSucc

variable {X : TopCat.{u}}
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The arrow diagram used in the successor-step dimension-shift construction. -/
noncomputable def sheafH_filtered_colimit_succ_toArrow :
    J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  { obj := fun j ↦ Arrow.mk (0 : Y'.obj j ⟶ 0)
    map := fun f ↦ Arrow.homMk (Y'.map f) (𝟙 0) (by simp)
    map_id := fun j ↦ by ext <;> simp
    map_comp := fun f g ↦ by ext <;> simp }

/-- Objectwise injective envelopes coming from functorial factorization of `0 : Y_j ⟶ 0`. -/
noncomputable def sheafH_filtered_colimit_succ_Inj :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafH_filtered_colimit_succ_toArrow Y' ⋙
    (MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp).Z

/-- The natural monomorphism from the original diagram into the injective replacement. -/
noncomputable def sheafH_filtered_colimit_succ_eta :
    Y' ⟶ sheafH_filtered_colimit_succ_Inj Y' :=
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  { app := fun j ↦ ffData.i.app ((sheafH_filtered_colimit_succ_toArrow Y').obj j)
    naturality := fun _ _ f ↦
      ffData.i.naturality ((sheafH_filtered_colimit_succ_toArrow Y').map f) }

omit [IsFiltered J'] in
theorem sheafH_filtered_colimit_succ_eta_mono (j : J') :
    Mono ((sheafH_filtered_colimit_succ_eta Y').app j) := by
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  exact ffData.hi ((sheafH_filtered_colimit_succ_toArrow Y').obj j)

/-- The colimit cocone of the injective replacement diagram. -/
noncomputable def sheafH_filtered_colimit_succ_injCocone :
    Cocone (sheafH_filtered_colimit_succ_Inj Y') :=
  colimit.cocone (sheafH_filtered_colimit_succ_Inj Y')

/-- The cocone obtained by composing the original cocone maps with the injective
replacement. -/
noncomputable def sheafH_filtered_colimit_succ_iotaCocone : Cocone Y' :=
  Cocone.mk (sheafH_filtered_colimit_succ_injCocone Y').pt
    { app := fun j ↦
        (sheafH_filtered_colimit_succ_eta Y').app j ≫
          (sheafH_filtered_colimit_succ_injCocone Y').ι.app j
      naturality := fun j j' f ↦ by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          ← (sheafH_filtered_colimit_succ_injCocone Y').w f, ← Category.assoc,
          (sheafH_filtered_colimit_succ_eta Y').naturality f] }

/-- The induced map from the colimit of the original diagram to the colimit of its injective
replacement. -/
noncomputable def sheafH_filtered_colimit_succ_iota
    (c' : Cocone Y') (hc' : IsColimit c') :
    c'.pt ⟶ (sheafH_filtered_colimit_succ_injCocone Y').pt :=
  hc'.desc (sheafH_filtered_colimit_succ_iotaCocone Y')

theorem sheafH_filtered_colimit_succ_iota_fac
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    c'.ι.app j ≫ sheafH_filtered_colimit_succ_iota Y' c' hc' =
      (sheafH_filtered_colimit_succ_eta Y').app j ≫
        (sheafH_filtered_colimit_succ_injCocone Y').ι.app j :=
  hc'.fac (sheafH_filtered_colimit_succ_iotaCocone Y') j

noncomputable instance sheafH_filtered_colimit_succ_iota_mono
    (c' : Cocone Y') (hc' : IsColimit c') :
    Mono (sheafH_filtered_colimit_succ_iota Y' c' hc') := by
  haveI : ∀ j, Mono ((sheafH_filtered_colimit_succ_eta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y')
  haveI : Mono (sheafH_filtered_colimit_succ_eta Y') := NatTrans.mono_of_mono_app _
  exact colim.map_mono' (sheafH_filtered_colimit_succ_eta Y') hc'
    (colimit.isColimit (sheafH_filtered_colimit_succ_Inj Y'))
    (sheafH_filtered_colimit_succ_iota Y' c' hc')
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc')

/-- The short exact sequence on colimit objects obtained from the injective replacement. -/
noncomputable def sheafH_filtered_colimit_succ_shortComplex
    (c' : Cocone Y') (hc' : IsColimit c') :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')

theorem sheafH_filtered_colimit_succ_shortExact
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_succ_shortComplex Y' c' hc').ShortExact := by
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  change (ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι')) inferInstance inferInstance

/-- The quotient diagram obtained by objectwise cokernels of the injective replacement maps. -/
noncomputable def sheafH_filtered_colimit_succ_quotient :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  { obj := fun j ↦ cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)
    map := fun {j j'} f ↦
      cokernel.map _ _
        (Y'.map f) ((sheafH_filtered_colimit_succ_Inj Y').map f)
        ((sheafH_filtered_colimit_succ_eta Y').naturality f).symm
    map_id := fun j ↦ by ext; simp [cokernel.map]
    map_comp := fun {j j' j''} f g ↦ by ext; simp [cokernel.map, Functor.map_comp] }

/-- The quotient cocone on the cokernel diagram induced by the colimit short exact sequence. -/
noncomputable def sheafH_filtered_colimit_succ_quotientCocone
    (c' : Cocone Y') (hc' : IsColimit c') :
    Cocone (sheafH_filtered_colimit_succ_quotient Y') :=
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  let S := sheafH_filtered_colimit_succ_shortComplex Y' c' hc'
  Cocone.mk S.X₃
    { app := fun j ↦
        cokernel.map ((sheafH_filtered_colimit_succ_eta Y').app j) ι'
          (c'.ι.app j) ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j)
          (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j).symm
      naturality := fun j j' f ↦ by
        apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))).mp
        conv_lhs =>
          simp [sheafH_filtered_colimit_succ_quotient, cokernel.map, Category.assoc]
        conv_rhs =>
          simp [sheafH_filtered_colimit_succ_quotient, cokernel.map, Category.assoc]
        change
          (sheafH_filtered_colimit_succ_Inj Y').map f ≫
              (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                cokernel.desc ((sheafH_filtered_colimit_succ_eta Y').app j')
                  (((sheafH_filtered_colimit_succ_injCocone Y').ι.app j') ≫
                    cokernel.π ι') _) =
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
              cokernel.desc ((sheafH_filtered_colimit_succ_eta Y').app j)
                (((sheafH_filtered_colimit_succ_injCocone Y').ι.app j) ≫
                  cokernel.π ι') _
        rw [cokernel.π_desc]
        rw [cokernel.π_desc]
        exact congrArg (fun t ↦ t ≫ cokernel.π ι')
          ((sheafH_filtered_colimit_succ_injCocone Y').w f) }

private noncomputable def sheafH_filtered_colimit_succ_liftedCocone
    (s : Cocone (sheafH_filtered_colimit_succ_quotient Y')) :
    Cocone (sheafH_filtered_colimit_succ_Inj Y') :=
  Cocone.mk s.pt
    { app := fun j ↦
        cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
      naturality := fun j j' a ↦ by
        dsimp
        have hdesc :
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                (sheafH_filtered_colimit_succ_quotient Y').map a =
            (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
          simp [sheafH_filtered_colimit_succ_quotient]
        rw [← Category.assoc, ← hdesc]
        exact congrArg (fun t ↦
          cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ t) (s.w a) }

omit [IsFiltered J'] in
@[simp]
private theorem sheafH_filtered_colimit_succ_liftedCocone_ι_app
    (s : Cocone (sheafH_filtered_colimit_succ_quotient Y')) (j : J') :
    (sheafH_filtered_colimit_succ_liftedCocone Y' s).ι.app j =
      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := rfl

/-- The quotient cocone obtained from the stagewise injective replacements is colimiting. -/
noncomputable def sheafH_filtered_colimit_succ_quotientCocone_isColimit
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsColimit (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc') := by
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let injCocone := sheafH_filtered_colimit_succ_injCocone Y'
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  let injColim := colimit.isColimit Inj
  have hπ (j) : cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j =
      injCocone.ι.app j ≫ cokernel.π ι' := cokernel.π_desc _ _ _
  exact
  { desc := fun s ↦
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      cokernel.desc ι' (injColim.desc lifted) (hc'.hom_ext fun j ↦ by
        have hfac_lifted :
            injCocone.ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
          simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
            sheafH_filtered_colimit_succ_injCocone] using injColim.fac lifted j
        change c'.ι.app j ≫ sheafH_filtered_colimit_succ_iota Y' c' hc' ≫
            injColim.desc lifted = c'.ι.app j ≫ 0
        rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j]
        have hzero :
            (sheafH_filtered_colimit_succ_eta Y').app j ≫
                ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j ≫
                  injColim.desc lifted) =
              c'.ι.app j ≫ 0 := by
          rw [hfac_lifted]
          change
            (((sheafH_filtered_colimit_succ_eta Y').app j ≫
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)) ≫
              s.ι.app j) = c'.ι.app j ≫ 0
          rw [cokernel.condition, zero_comp]
          rw [comp_zero]
        simpa [Category.assoc] using hzero)
    fac := fun s j ↦ (cancel_epi (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))).mp (by
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      have hfac_lifted :
          injCocone.ι.app j ≫ injColim.desc lifted =
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
        simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
          sheafH_filtered_colimit_succ_injCocone] using injColim.fac lifted j
      have hι : ι' ≫ injColim.desc lifted = 0 := by
        exact hc'.hom_ext fun k ↦ by
          have hfac_lifted_k :
              injCocone.ι.app k ≫ injColim.desc lifted =
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app k) ≫ s.ι.app k := by
            simpa [lifted, sheafH_filtered_colimit_succ_liftedCocone, injCocone,
              sheafH_filtered_colimit_succ_injCocone] using injColim.fac lifted k
          change c'.ι.app k ≫ sheafH_filtered_colimit_succ_iota Y' c' hc' ≫
              injColim.desc lifted = c'.ι.app k ≫ 0
          rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' k]
          have hzero :
              (sheafH_filtered_colimit_succ_eta Y').app k ≫
                  ((sheafH_filtered_colimit_succ_injCocone Y').ι.app k ≫
                    injColim.desc lifted) =
                c'.ι.app k ≫ 0 := by
            rw [hfac_lifted_k]
            change
              (((sheafH_filtered_colimit_succ_eta Y').app k ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app k)) ≫
                s.ι.app k) = c'.ι.app k ≫ 0
            rw [cokernel.condition, zero_comp]
            rw [comp_zero]
          simpa [Category.assoc] using hzero
      change (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
          qCocone.ι.app j) ≫ cokernel.desc ι' (injColim.desc lifted) _ =
        cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
      rw [hπ j]
      change (injCocone.ι.app j ≫ cokernel.π ι') ≫
          cokernel.desc ι' (injColim.desc lifted) hι =
        cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
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
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j := by
          simpa [injCocone] using (hπ j).symm
        have hfac_lifted' :
            (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
          simpa [lifted] using injColim.fac lifted j
        change ((colimit.cocone Inj).ι.app j ≫ cokernel.π ι') ≫ m =
          (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted
        rw [hπ']
        have hmq : qCocone.ι.app j ≫ m = s.ι.app j := by
          simpa [qCocone] using hm j
        have htarget :
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                (qCocone.ι.app j ≫ m) =
              (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted := by
          simpa [Category.assoc] using
            (congrArg
              (fun t ↦ cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ t)
              hmq).trans hfac_lifted'.symm
        simpa [Category.assoc] using htarget) }

omit [IsFiltered J'] in
theorem sheafH_filtered_colimit_succ_stage_shortExact (j : J') :
    (ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
      (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
      (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j))).ShortExact := by
  haveI : Mono ((sheafH_filtered_colimit_succ_eta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y') j
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel ((sheafH_filtered_colimit_succ_eta Y').app j)))
    inferInstance inferInstance

/-- The morphism between stagewise short exact sequences induced by a transition map in the
    filtered diagram. -/
noncomputable def sheafH_filtered_colimit_succ_stage_map_hom
    {j j' : J'} (f : j ⟶ j') :
    ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)) ⟶
      ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j')
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j'))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j')) :=
  ShortComplex.homMk
    (Y'.map f)
    ((sheafH_filtered_colimit_succ_Inj Y').map f)
    ((sheafH_filtered_colimit_succ_quotient Y').map f)
    ((sheafH_filtered_colimit_succ_eta Y').naturality f)
    (cokernel.π_desc _ _ _).symm

/-- The morphism from the stagewise short exact sequence to the colimit short exact sequence. -/
noncomputable def sheafH_filtered_colimit_succ_stage_hom
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)) ⟶
      sheafH_filtered_colimit_succ_shortComplex Y' c' hc' :=
  ShortComplex.homMk
    (c'.ι.app j)
    ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j)
    ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j)
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j)
    (cokernel.π_desc _ _ _).symm

/-- The stagewise dimension-shift natural isomorphism between the quotient diagram in degree
    `n` and the original diagram in degree `n + 1`. -/
noncomputable def sheafH_filtered_colimit_succ_shiftNatIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) (n + 1))) :
    sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n ≅
      Y' ⋙ sheafCohomologyFunctor X (n + 1) :=
  NatIso.ofComponents
    (fun j ↦
      sheafH_succ_iso_of_subsingleton_middle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) n
        (h_mid_n j) (h_mid_succ j))
    (fun {j j'} f ↦ by
      ext y
      simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m y)
        ((sheafH_succ_iso_of_subsingleton_middle_natural
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          (sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f)
          n (h_mid_n j) (h_mid_succ j) (h_mid_n j') (h_mid_succ j')).symm))

/-- The induced colimit isomorphism from the successor-step stagewise dimension shift. -/
noncomputable def sheafH_filtered_colimit_succ_shiftDomainIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) (n + 1))) :
    colimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n) ≅
      colimit (Y' ⋙ sheafCohomologyFunctor X (n + 1)) :=
  HasColimit.isoOfNatIso (sheafH_filtered_colimit_succ_shiftNatIso Y' n h_mid_n h_mid_succ)

/-- The colimit-level dimension-shift isomorphism for the short exact sequence obtained from
    the injective replacement of the filtered colimit cocone. -/
noncomputable def sheafH_filtered_colimit_succ_shiftCodomainIso
    (c' : Cocone Y') (hc' : IsColimit c') (n : ℕ)
    (h_colim_n :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt (n + 1))) :
    AddCommGrpCat.of
        (Sheaf.H (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').pt n) ≅
      AddCommGrpCat.of (Sheaf.H c'.pt (n + 1)) :=
  sheafH_succ_iso_of_subsingleton_middle
    (sheafH_filtered_colimit_succ_shortExact Y' c' hc') n h_colim_n h_colim_succ

/-- The filtered-colimit successor-step vanishing lemma for the injective replacement:
the middle term of the induced short exact sequence has trivial cohomology in degree `n + 1`. -/
theorem sheafH_filtered_colimit_succ_inj_subsingleton
    [NoetherianSpace X] (n : ℕ)
    (hInj : ∀ j, Injective ((sheafH_filtered_colimit_succ_Inj Y').obj j)) :
    Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt (n + 1)) := by
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let injCocone := sheafH_filtered_colimit_succ_injCocone Y'
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
noncomputable def sheafH_filtered_colimit_comparison
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
        sheafH_filtered_colimit_comparison Y' n c' =
      (sheafCohomologyFunctor X n).map (c'.ι.app j) := by
  exact colimit.ι_desc ((sheafCohomologyFunctor X n).mapCocone c') j

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
        ((sheafH_filtered_colimit_succ_Inj Ysh).obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafH_filtered_colimit_succ_Inj Ysh).obj j) (n + 1)))
    (h_colim_n :
      Subsingleton (Sheaf.H
        (sheafH_filtered_colimit_succ_injCocone Ysh).pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H
        (sheafH_filtered_colimit_succ_injCocone Ysh).pt (n + 1))) :
    (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafH_filtered_colimit_comparison Ysh (n + 1) csh =
      sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
        (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom := by
  apply colimit.hom_ext
  intro j
  rw [show (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom =
      (HasColimit.isoOfNatIso (sheafH_filtered_colimit_succ_shiftNatIso Ysh n
        h_mid_n h_mid_succ)).hom from rfl]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  rw [show
      colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sheafCohomologyFunctor X n) j ≫
          sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
            (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
        ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom from by
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫ (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
            h_colim_n h_colim_succ).hom)
        (colimit_ι_sheafH_filtered_colimit_comparison
          (X := X) (Y' := sheafH_filtered_colimit_succ_quotient Ysh) (n := n)
          (c' := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) j)]
  change
    (sheafH_succ_iso_of_subsingleton_middle
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) n
        (h_mid_n j) (h_mid_succ j)).hom ≫
      (sheafCohomologyFunctor X (n + 1)).map (csh.ι.app j) =
    (sheafCohomologyFunctor X n).map
        ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom
  simpa [sheafH_filtered_colimit_succ_shiftNatIso,
    sheafH_filtered_colimit_succ_shiftCodomainIso] using
    (sheafH_succ_iso_of_subsingleton_middle_natural
      (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j)
      (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
      (sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j)
      n (h_mid_n j) (h_mid_succ j) h_colim_n h_colim_succ)
