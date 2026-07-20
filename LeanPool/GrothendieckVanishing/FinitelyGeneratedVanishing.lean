/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import LeanPool.GrothendieckVanishing.PresheafFilteredColimit
import LeanPool.GrothendieckVanishing.ClosedImmersionCohomology
import LeanPool.GrothendieckVanishing.GeneratedSubsheaf

/-!
# Finitely generated vanishing reduction

On a Noetherian space, every sheaf is the filtered colimit of its finitely generated
subsheaves, and sheaf cohomology commutes with filtered colimits. Combining the two
reduces vanishing of `Hⁿ` for arbitrary sheaves to vanishing for finitely generated ones.
This file packages that reduction; together with the Noetherian-shrinking step, it
underlies the irreducible positive-dimensional case of Grothendieck vanishing.

## Main definitions

* `finsetGenFunctor` — the filtered diagram of finitely generated subsheaves.
* `finsetGenCocone`, `finsetGenCoconeIsColimit` — exhibits `K` as the colimit.

## Main results

* `cohomology_vanishing_of_finitelyGenerated_vanishing` — vanishing for f.g. subsheaves
  propagates to the whole sheaf via the filtered-colimit comparison.
* `finsetGeneratedSheaf_vanishing` — `Finset.induction` reducing vanishing for finitely
  generated subsheaves to vanishing for the epi-images of `zeroOutsideInt V`.
* `directLimit_cohomology_vanishing` — composes both above into the headline reduction.

The `isFlasque_filtered_colimit` and `sheafHPreservesFilteredColimits` building blocks
live in the `PresheafFilteredColimit` modules.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram

variable {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
    Finset
        (TopCat.Presheaf.SectionIndex K) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Presheaf.finsetGeneratedSheaf hK S
  map h := TopCat.Presheaf.finsetImageInclGen hK h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S))).1
    rw [TopCat.Presheaf.finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃))).1
    rw [Category.assoc, TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    { app := fun S ↦ Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S)
      naturality := fun S S' h ↦ by
        change TopCat.Presheaf.finsetImageInclGen hK h.le ≫
            Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S') =
          Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S) ≫
            𝟙 (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
        rw [TopCat.Presheaf.finsetImageInclGen_comp_ι]
        exact (Category.comp_id _).symm }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCoconeIsColimit :
    IsColimit (finsetGenCocone hK) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  haveI hd_mono : Mono d := by
    haveI : IsConnected
        (Finset (TopCat.Presheaf.SectionIndex K)) := IsFiltered.isConnected _
    haveI : ∀ j, Mono ((finsetGenCocone hK).ι.app j) := fun j ↦
      show Mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK j)) from inferInstance
    haveI := NatTrans.mono_of_mono_app (finsetGenCocone hK).ι
    exact colim.map_mono' (finsetGenCocone hK).ι (colimit.isColimit _)
      (isColimitConstCocone _ _) d (fun j ↦ by
        change colimit.ι (finsetGenFunctor hK) j ≫
            colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK) =
          (finsetGenCocone hK).ι.app j
        exact colimit.ι_desc (finsetGenCocone hK) j)
  -- desc is epi: allSectionMap K factors through desc
  haveI hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Presheaf.SectionIndex K ↦ TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ ↦
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = TopCat.Presheaf.allSectionMap hK := by
      ext σ
      dsimp only [g, d]
      rw [← Category.assoc, Sigma.ι_desc]
      calc
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
            factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
              colimit.ι (finsetGenFunctor hK) {σ} ≫ d =
          (Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
              TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
              factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ})) ≫
            (colimit.ι (finsetGenFunctor hK) {σ} ≫ d) := by
            rw [Category.assoc]
        _ = Sigma.ι (fun σ ↦ TopCat.Sheaf.zeroOutsideInt σ.fst) σ ≫
              TopCat.Presheaf.allSectionMap hK := by
          rw [show d = colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK) from rfl]
          simp_rw [Category.assoc]
          erw [colimit.ι_desc]
          simp [finsetGenCocone, TopCat.Presheaf.allSectionMap,
            TopCat.Presheaf.finsetGeneratorMap, TopCat.Sheaf.familyMap,
            Sigma.ι_desc]
    exact @epi_of_epi_fac _ _ _ _ _ g d (TopCat.Presheaf.allSectionMap hK)
      (TopCat.Presheaf.allSectionMap_epi (F := K) hK) hfac
  -- mono + epi → iso in abelian category
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor hK)).desc (finsetGenCocone hK)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor hK)).ofPointIso

end FilteredDiagram

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Uses the filtered-colimit comparison isomorphism
    for the diagram of finitely generated subsheaves and transports zero across it. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hfg : ∀ (S : Finset
        (TopCat.Presheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    haveI : Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := hfg S
    change IsZero
      (AddCommGrpCat.of (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m))
    exact AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  have hZeroTarget :
      IsZero (AddCommGrpCat.of
        (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) := by
    change IsZero (AddCommGrpCat.of (Sheaf.H (finsetGenCocone hK).pt m))
    exact IsZero.of_iso hZeroColim
      (sheafHPreservesFilteredColimits
        (Y' := finsetGenFunctor hK)
        (c' := finsetGenCocone hK)
        (hc' := finsetGenCoconeIsColimit hK)
        m).symm
  simpa using AddCommGrpCat.subsingleton_of_isZero hZeroTarget

section FinsetGenerated

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m))
    (S : Finset
      (TopCat.Presheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := by
  classical
  suffices h : ∀ (T : Finset (TopCat.Presheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK T) m) from h S
  intro T; induction T using Finset.induction with
  | empty =>
    exact sheafH_subsingleton_of_isZero
      (IsZero.of_iso (isZero_zero _) (imageZero' (by
        ext ⟨σ, hσ⟩
        simp at hσ))) m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let f := TopCat.Presheaf.finsetImageInclGen hK h_sub
    let qIns := factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
    let qS := factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK S')
    let g : TopCat.Sheaf.zeroOutsideInt σ₀.1 ⟶ cokernel f :=
      Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫ qIns ≫ cokernel.π f
    haveI : Epi g := by
      refine epi_of_epi_fac
        (f := Sigma.desc fun σ ↦ if h : σ.1 = σ₀ then eqToHom (by rw [h]) else 0)
        (h := qIns ≫ cokernel.π f) ?_
      ext ⟨σ, hσ⟩
      by_cases h : σ = σ₀
      · subst h
        rw [← Category.assoc, Sigma.ι_desc]
        simp [g]
      · rw [← Category.assoc, Sigma.ι_desc, dif_neg h, zero_comp]
        have hfacBase :
            TopCat.Presheaf.finsetCoproductInclGen h_sub ≫ qIns = qS ≫ f := by
          simp [qIns, qS, f, TopCat.Presheaf.finsetImageInclGen]
        have hfac' :=
          congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ S'} ↦ TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫ e ≫ cokernel.π f) hfacBase
        have hzero_rhs :
            Sigma.ι
                (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ TopCat.Sheaf.zeroOutsideInt σ.1.1)
                ⟨σ, hσ⟩ ≫ qIns ≫ cokernel.π f = 0 := by
          simpa [TopCat.Presheaf.finsetCoproductInclGen, Category.assoc, h,
            cokernel.condition, Sigma.ι_desc_assoc, Sigma.ι_desc] using hfac'
        exact hzero_rhs.symm
    exact subsingleton_sheafH_of_shortExact_middle f m ih <|
      hzero (cokernel f).property g.hom
        ((TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance)

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ ↦ finsetGeneratedSheaf_vanishing hK m hzero S)
