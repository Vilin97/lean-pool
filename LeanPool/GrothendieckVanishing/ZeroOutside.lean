/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import LeanPool.GrothendieckVanishing.CohomologyAPI

/-!
# Extension-by-zero presheaf and sheaf machinery

The "extension by zero" of a presheaf `F` along the inclusion of an open `U`. The
construction `zeroOutside U F` agrees with `F` on opens `W ≤ U` and is the zero object
elsewhere. Sheafified, with `F = constZ` (the constant presheaf with value `ULift ℤ`), this
yields `zeroOutsideInt U`, which serves as the canonical generator family for the
finitely-generated subsheaf reduction in the Grothendieck vanishing proof.

## Main definitions

* `TopCat.Presheaf.zeroOutside` — the extension-by-zero presheaf.
* `TopCat.Presheaf.constZ` — the constant presheaf `ULift ℤ`.
* `TopCat.Sheaf.zeroOutsideInt` — sheafified extension-by-zero of `constZ` on `U`.
* `TopCat.Sheaf.zeroOutsideInt.sHom` — section-to-morphism construction.
* `TopCat.Sheaf.zeroOutsideInt.generator` — canonical generator of
  `(constZ.zeroOutside U).obj (op U)`.

## Main results

* `zeroOutside_openHom_stalk_surj`, `sheafifyMap_zeroOutside_openHom_stalk_surj` — stalk
  surjectivity for the open-inclusion morphisms (and their sheafifications) at points of
  the support.
* `stalk_zeroOutsideInt_zero_outside` — stalks of `zeroOutsideInt U` vanish off `U`.
* `isZero_zeroOutsideInt_bot` — `zeroOutsideInt ⊥` is the zero sheaf.
* `stalk_zeroOutsideInt_eq_zsmul_generator` — stalks on `U` are integer multiples of the
  canonical germ.
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace TopCat

namespace Presheaf

open ZeroObject ConcreteCategory

variable {C : Type*} [Category C] [HasZeroObject C] {X : TopCat.{u}}
    (U : Opens X) (F : Presheaf C X)

open Classical in
/-- Presheaf that agrees with `F` on opens contained in `U` and is zero outside `U`. -/
def zeroOutside : Presheaf C X where
  obj W := if (unop W) ≤ U then F.obj W else 0
  map {W Y} i :=
    if h : (unop W) ≤ U then
      eqToHom (by grind) ≫ F.map i ≫ eqToHom (by rw [if_pos (le_trans (leOfHom i.unop) h)])
    else ((if_neg h).symm.ndrec (isZero_zero C)).to_ _
  map_id W := by
    split_ifs with h
    · simp
    · apply IsZero.to_eq
  map_comp {W Y Z} iWY iYZ := by
    split_ifs with h
    · have : unop Y ≤ U := le_trans (leOfHom iWY.unop) h
      have : unop Z ≤ U := le_trans (leOfHom iYZ.unop) this
      simp_all
    · apply IsZero.to_eq

variable {U F}

lemma zeroOutside_isZero {W : Opens X} (h : ¬ W ≤ U) :
    IsZero ((zeroOutside U F).obj (op W)) := by
  simp [zeroOutside, h, isZero_zero C]

lemma zeroOutside_le {W : Opens X} (h : W ≤ U) :
    (zeroOutside U F).obj (op W) = F.obj (op W) := by
  simp [zeroOutside, h]

/-- `zeroOutside ⊤ F ≅ F`: zero-outside on the whole space is the identity. -/
def zeroOutsideTopIso : zeroOutside (⊤ : Opens X) F ≅ F :=
  NatIso.ofComponents
    (fun W ↦ eqToIso (zeroOutside_le (le_top : unop W ≤ ⊤)))
    (fun {W Y} i ↦ by simp [zeroOutside, le_top])

variable {V : Opens X} (h : V ≤ U)

open Classical in
/-- The canonical inclusion `zeroOutside V F ⟶ zeroOutside U F` for `V ≤ U`. -/
def zeroOutsideOpenHom : zeroOutside V F ⟶ zeroOutside U F where
  app W := if hW : (unop W) ≤ V then
      eqToHom (by rw [zeroOutside_le hW, zeroOutside_le (le_trans hW h)])
    else (zeroOutside_isZero (F := F) hW).to_ _
  naturality {W Y} i := by
    by_cases hWV : (unop W) ≤ V
    · have hYV : unop Y ≤ V := le_trans (leOfHom i.unop) hWV
      have hYU : unop Y ≤ U := le_trans hYV h
      have hWU : unop W ≤ U := le_trans hWV h
      simp [zeroOutside, hWV, hYV, hWU, hYU]
    · apply (zeroOutside_isZero (F := F) hWV).eq_of_src

/-- The canonical inclusion of zero-outside presheaves is a monomorphism. -/
instance zeroOutside_hom_mono [HasPullbacks C] : Mono (zeroOutsideOpenHom (F := F) h) := by
  change @Mono ((Opens X)ᵒᵖ ⥤ C) _ (zeroOutside V F) (zeroOutside U F) (zeroOutsideOpenHom h)
  rw [NatTrans.mono_iff_mono_app]
  intro W; by_cases hWV : (unop W) ≤ V
  · have hWU : unop W ≤ U := le_trans hWV h
    simp [zeroOutsideOpenHom, hWV, IsIso.mono_of_iso]
  · simp [zeroOutsideOpenHom, hWV, zeroOutside_isZero (F := F) hWV, IsZero.mono]

/-- The presheaf stalk map of `zeroOutsideOpenHom h` at `x ∈ V` is surjective:
    any germ in the larger zero-outside presheaf can be lifted by restricting to `W ∩ V ≤ V`
    where the presheaf map is `eqToHom` (identity). -/
theorem _root_.zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} {F : TopCat.Presheaf AddCommGrpCat.{u} X}
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (TopCat.Presheaf.zeroOutsideOpenHom (F := F) h))) := by
  intro g
  obtain ⟨W, hxW, s, rfl⟩ := (F.zeroOutside U).exists_germ_eq g
  set WV := W ⊓ V
  have hWV_le_V : WV ≤ V := inf_le_right
  have hWV_le_W : WV ≤ W := inf_le_left
  have hxWV : x ∈ WV := ⟨hxW, hx⟩
  have happ_iso : IsIso ((TopCat.Presheaf.zeroOutsideOpenHom (F := F) h).app (op WV)) := by
    simp only [TopCat.Presheaf.zeroOutsideOpenHom, hWV_le_V, ↓reduceDIte]
    infer_instance
  let s_res := ConcreteCategory.hom ((F.zeroOutside U).map (homOfLE hWV_le_W).op) s
  have h_bij := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.zeroOutsideOpenHom (F := F) h).app (op WV))
  obtain ⟨t, ht⟩ := h_bij.2 s_res
  refine ⟨(F.zeroOutside V).germ WV x hxWV t, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change (F.zeroOutside U).germ WV x hxWV
      ((TopCat.Presheaf.zeroOutsideOpenHom (F := F) h).app (op WV) t) =
    (F.zeroOutside U).germ W x hxW s
  rw [ht]
  simp only [s_res]
  convert ((F.zeroOutside U).germ_res_apply (homOfLE hWV_le_W) x hxWV s) using 1

/-- The sheaf stalk map of `sheafifyMap (zeroOutsideOpenHom h)` at `x ∈ V` is surjective.
    Transfers presheaf stalk surjectivity via `toSheafify_naturality` and
    the fact that `stalk(toSheafify)` is an isomorphism. -/
theorem _root_.sheafifyMap_zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (sheafifyMap (Opens.grothendieckTopology (T := X))
          (TopCat.Presheaf.zeroOutsideOpenHom (F := F) h)))) := by
  let J := Opens.grothendieckTopology (T := X)
  let φ := TopCat.Presheaf.zeroOutsideOpenHom (F := F) h
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let ηV := CategoryTheory.toSheafify J (F.zeroOutside V)
  let ηU := CategoryTheory.toSheafify J (F.zeroOutside U)
  have hnat : T.map φ ≫ T.map ηU =
      T.map ηV ≫ T.map (CategoryTheory.sheafifyMap J φ) := by
    dsimp [ηV, ηU]
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg (fun α ↦ T.map α) (CategoryTheory.toSheafify_naturality J φ)
  haveI : IsIso (T.map ηV) :=
    stalkFunctor_map_iso_toSheafify _ x
  haveI : IsIso (T.map ηU) :=
    stalkFunctor_map_iso_toSheafify _ x
  intro g
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map ηU)).2 g
  obtain ⟨p, hp⟩ := zeroOutside_openHom_stalk_surj h x hx q
  exact ⟨ConcreteCategory.hom (T.map ηV) p, by
    change ConcreteCategory.hom (T.map (CategoryTheory.sheafifyMap J φ))
        (ConcreteCategory.hom (T.map ηV) p) = _
    rw [← ConcreteCategory.comp_apply, hnat.symm, ConcreteCategory.comp_apply, hp]⟩

open AddCommGrpCat

/-- The constant presheaf with value `ULift ℤ`. -/
abbrev constZ {X : TopCat.{u}} : Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

namespace zeroOutside

variable {X : TopCat.{u}} (U : Opens X)

/-- Distinguished integer generator of `constZ.zeroOutside U` over `U`. -/
def generator : (constZ.zeroOutside U).obj (op U) :=
  (eqToHom (by simp [zeroOutside, constZ]) :
      AddCommGrpCat.of (ULift ℤ) ⟶ (constZ.zeroOutside U).obj (op U)) 1

variable {U}

open Classical in
/-- Morphism from `constZ.zeroOutside U` determined by a section over `U`. -/
def sHom {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    constZ.zeroOutside U ⟶ F where
  app {W} :=
    if h : (unop W) ≤ U then
      eqToHom (by simp_all [zeroOutside, constZ]) ≫
        AddCommGrpCat.ofHom (uliftZMultiplesHom (F.obj W) (F.map (homOfLE h).op s))
    else 0
  naturality {W Y} i := by
    by_cases hWU : (unop W) ≤ U
    · have hYU : (unop Y) ≤ U := le_trans (leOfHom i.unop) hWU
      apply AddCommGrpCat.hom_ext
      ext z
      have hmap :
          F.map (homOfLE hYU).op s = F.map i (F.map (homOfLE hWU).op s) := by
        simpa [Functor.map_comp_apply] using
          (congrArg (fun j ↦ F.map j s) (Subsingleton.elim ((homOfLE hWU).op ≫ i)
            (homOfLE hYU).op)).symm
      have hObjW : (zeroOutside U constZ).obj W = AddCommGrpCat.of (ULift ℤ) := by
        simp [zeroOutside, hWU, constZ]
      let w : ULift ℤ :=
        (AddCommGrpCat.Hom.hom (eqToHom hObjW) z)
      have hz : (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) w = z := by
        simp [w, ← ConcreteCategory.comp_apply, eqToHom_trans]
      rw [← hz]
      conv_lhs => simp [zeroOutside, hWU, hYU, w, hmap, constZ]
      conv_rhs => simp [zeroOutside, hWU, hYU, w, hmap, constZ]
      exact (map_zsmul (AddCommGrpCat.Hom.hom (F.map i)) _ _).symm
    · apply (zeroOutside_isZero (F := constZ) hWU).eq_of_src

theorem sHom_app_generator {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (sHom s).app (op U) (generator U) = s := by
  have hObjU : (zeroOutside U constZ).obj (op U) = AddCommGrpCat.of (ULift ℤ) := by
    simp [zeroOutside, constZ]
  have h1 :
      (AddCommGrpCat.Hom.hom (eqToHom hObjU))
          ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ)) = (1 : ULift ℤ) := by
    simp [← comp_apply, eqToHom_trans]
  have hgen : generator U =
      (eqToHom hObjU.symm :
        AddCommGrpCat.of (ULift ℤ) ⟶ (zeroOutside U constZ).obj (op U)) (1 : ULift ℤ) := by
    simp [generator]
  rw [hgen]
  classical
  rw [show (sHom s).app (op U) = if h : U ≤ U then
      eqToHom (by simp_all [zeroOutside, constZ]) ≫
        AddCommGrpCat.ofHom
          (uliftZMultiplesHom (F.obj (op U)) (F.map (homOfLE h).op s))
    else 0 from rfl]
  rw [dif_pos le_rfl]
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  change (((AddCommGrpCat.Hom.hom (eqToHom hObjU))
      ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ))).down : ℤ) •
        ((ConcreteCategory.hom (F.map (homOfLE (le_rfl : U ≤ U)).op)) s) = s
  rw [show (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (op U) from Subsingleton.elim _ _]
  rw [F.map_id]
  rw [congrArg ULift.down h1]
  simp

/-- The restriction of the distinguished generator of `constZ.zeroOutside V` to a smaller open
`W ≤ V` corresponds to `1 : ULift ℤ` under the canonical identification with `ULift ℤ`. -/
theorem resGen_eqToHom_eq_one
    {X : TopCat.{u}} (V : Opens X) {W : Opens X} (hWV : W ≤ V)
    (hObjW : (constZ.zeroOutside V).obj (op W) = AddCommGrpCat.of (ULift ℤ)) :
      (AddCommGrpCat.Hom.hom (eqToHom hObjW))
        (ConcreteCategory.hom ((constZ.zeroOutside V).map (homOfLE hWV).op)
          (generator V)) = (1 : ULift ℤ) := by
  unfold generator
  have hmap : (constZ.zeroOutside V).map (homOfLE hWV).op =
      eqToHom (by simp [TopCat.Presheaf.zeroOutside, constZ, hWV]) := by
    dsimp [TopCat.Presheaf.zeroOutside, constZ]
    rw [dif_pos (le_rfl : V ≤ V)]
    change eqToHom _ ≫ eqToHom
      (rfl : AddCommGrpCat.of (ULift ℤ) = AddCommGrpCat.of (ULift ℤ)) ≫
      eqToHom _ = eqToHom _
    rw [eqToHom_trans_assoc]
    simp [eqToHom_trans]
  rw [hmap]
  simp [← ConcreteCategory.comp_apply, eqToHom_trans]

/-- At a point inside the support open, every stalk element of the presheaf `constZ.zeroOutside V`
is an integer multiple of the germ of the distinguished generator over `V`. -/
theorem presheaf_stalk_zeroOutside_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (constZ.zeroOutside V)) :
    ∃ n : ℤ,
      a = n • ((constZ.zeroOutside V).germ V x hx (generator V)) := by
  obtain ⟨W, hxW, s, rfl⟩ := (constZ.zeroOutside V).exists_germ_eq a
  by_cases hWV : W ≤ V
  · have hObjW : (TopCat.Presheaf.zeroOutside V constZ).obj (op W) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [TopCat.Presheaf.zeroOutside, hWV, constZ]
    let w : ULift ℤ := (AddCommGrpCat.Hom.hom (eqToHom hObjW)) s
    let genW : (constZ.zeroOutside V).obj (op W) :=
      ConcreteCategory.hom ((constZ.zeroOutside V).map (homOfLE hWV).op) (generator V)
    have hgenW_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) genW = (1 : ULift ℤ) :=
      resGen_eqToHom_eq_one V hWV hObjW
    have hinj : Function.Injective (AddCommGrpCat.Hom.hom (eqToHom hObjW)) :=
      (ConcreteCategory.bijective_of_isIso (eqToHom hObjW)).1
    have hs_zsmul : s = w.down • genW := by
      apply hinj
      rw [map_zsmul, hgenW_val]
      change w = w.down • (1 : ULift ℤ)
      ext
      simp
    refine ⟨w.down, ?_⟩
    rw [hs_zsmul, map_zsmul (ConcreteCategory.hom ((constZ.zeroOutside V).germ W x hxW))]
    congr 1
    exact TopCat.Presheaf.germ_res_apply (constZ.zeroOutside V)
      (homOfLE hWV) x hxW (generator V)
  · have hIsZero := TopCat.Presheaf.zeroOutside_isZero (F := constZ) hWV
    haveI := AddCommGrpCat.subsingleton_of_isZero hIsZero
    exact ⟨0, by simp [Subsingleton.eq_zero s, map_zero]⟩

end zeroOutside

end Presheaf

namespace Sheaf

open Presheaf

/-- Sheafification of the integer-valued zero-outside presheaf. -/
def zeroOutsideInt {X : TopCat.{u}} (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj (Presheaf.constZ.zeroOutside U)

namespace zeroOutsideInt

variable {X : TopCat.{u}} (U : Opens X)

/-- Distinguished generator section of `zeroOutsideInt U` over `U`. -/
def generator : (zeroOutsideInt U).presheaf.obj (op U) :=
  (toSheafify _ (Presheaf.constZ.zeroOutside U)).app (op U) (Presheaf.zeroOutside.generator U)

variable {U}

/-- The canonical morphism `zeroOutsideInt V ⟶ zeroOutsideInt U` for `V ≤ U`. -/
@[simps]
def openHom {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    zeroOutsideInt V ⟶ zeroOutsideInt U where
  hom := sheafifyMap _ (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h)

instance {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) : Mono (openHom h) := by
  let J := Opens.grothendieckTopology (T := X)
  haveI : @Mono ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) _
      (Presheaf.constZ.zeroOutside V) (Presheaf.constZ.zeroOutside U)
      (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h) := by
    change Mono (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h)
    infer_instance
  change Mono ((presheafToSheaf J AddCommGrpCat).map
    (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h))
  apply Functor.map_mono

/-- Presheaf morphism out of `zeroOutsideInt U` induced by a section of a sheaf over `U`. -/
abbrev sHomVal {X : TopCat.{u}} {U : Opens X} {F : Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (s : F.obj (op U)) : (zeroOutsideInt U).obj ⟶ F :=
  sheafifyLift _ (Presheaf.zeroOutside.sHom s) hF

/-- Sheaf morphism out of `zeroOutsideInt U` induced by a section of `F` over `U`. -/
def sHom {X : TopCat.{u}} {U : Opens X} {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) : zeroOutsideInt U ⟶ F where
  hom := sHomVal F.property s

theorem sHomVal_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (s : F.obj (op U)) :
    (sHomVal hF s).app (op U) (generator U) = s := by
  delta generator
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, toSheafify_sheafifyLift]
  exact Presheaf.zeroOutside.sHom_app_generator s

theorem sHom_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (s : F.presheaf.obj (op U)) :
    (sHom s).hom.app (op U) (generator U) = s :=
  sHomVal_app_generator F.property s

theorem openHom_val_app_generator {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    (openHom h).hom.app (op V) (generator V) =
    (zeroOutsideInt U).obj.map (homOfLE h).op (generator U) := by
  delta generator
  have hpresheaf :
      (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h).app (op V)
          (Presheaf.zeroOutside.generator V) =
        (Presheaf.constZ.zeroOutside U).map (homOfLE h).op
          (Presheaf.zeroOutside.generator U) := by
    have hObjV : (Presheaf.constZ.zeroOutside U).obj (op V) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [Presheaf.zeroOutside, Presheaf.constZ, h]
    have hObjSource : (Presheaf.constZ.zeroOutside V).obj (op V) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [Presheaf.zeroOutside, Presheaf.constZ]
    apply (ConcreteCategory.bijective_of_isIso (eqToHom hObjV)).1
    have hright := Presheaf.zeroOutside.resGen_eqToHom_eq_one U h hObjV
    rw [hright]
    have hopen : (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h).app (op V) =
        eqToHom (by rw [hObjSource, hObjV]) := by
      simp [Presheaf.zeroOutsideOpenHom]
    rw [hopen]
    unfold Presheaf.zeroOutside.generator
    simp [← ConcreteCategory.comp_apply, eqToHom_trans]
  erw [openHom_hom,
    ← ConcreteCategory.comp_apply
      ((CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside V)).app (op V))
      ((CategoryTheory.sheafifyMap _ (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h)).app
        (op V)),
    ← NatTrans.comp_app (CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside V))
      (CategoryTheory.sheafifyMap _ (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h)),
    ← CategoryTheory.toSheafify_naturality _
      (Presheaf.zeroOutsideOpenHom (F := Presheaf.constZ) h),
    NatTrans.comp_app, ConcreteCategory.comp_apply,
    ← (CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside U)).naturality_apply
      (homOfLE h).op (Presheaf.zeroOutside.generator U)]
  exact congrArg
    (fun s ↦ (ConcreteCategory.hom
      ((CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside U)).app (op V))) s)
    hpresheaf

end zeroOutsideInt

open zeroOutsideInt

/-- Stalks of `zeroOutsideInt V` vanish outside `V`. -/
theorem _root_.stalk_zeroOutsideInt_zero_outside
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∉ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).obj) : a = 0 := by
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := P.exists_germ_eq q
  haveI := AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Presheaf.zeroOutside_isZero (F := TopCat.Presheaf.constZ) (fun h ↦ hx (h hxW)))
  rw [show s = 0 from Subsingleton.eq_zero s, map_zero]
  exact map_zero (ConcreteCategory.hom (T.map (toSheafify J P)))

/-- `zeroOutsideInt ⊥` is the zero sheaf (all stalks vanish). -/
theorem _root_.isZero_zeroOutsideInt_bot (X : TopCat.{u}) :
    IsZero (TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)) := by
  let F := TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)
  change IsZero F
  exact sheaf_isZero_of_zero_stalks X F.property (fun x a ↦
    stalk_zeroOutsideInt_zero_outside ⊥ x (Opens.mem_bot.not.mpr (fun h ↦ h.elim)) a)

/-- At a point inside the support open, every stalk element of `zeroOutsideInt V` is an integer
    multiple of the germ of the distinguished generator over `V`. -/
theorem _root_.stalk_zeroOutsideInt_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (TopCat.Sheaf.zeroOutsideInt V).obj) :
    ∃ n : ℤ,
      a = n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V)) := by
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨n, hn⟩ :=
    TopCat.Presheaf.zeroOutside.presheaf_stalk_zeroOutside_eq_zsmul_generator V x hx q
  refine ⟨n, ?_⟩
  rw [hn]
  change (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (n • _) = _
  rw [map_zsmul]
  congr 1
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
    (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)

/-- The map `n ↦ n • gen` from `ℤ` into `stalk(zeroOutsideInt V, x)` is injective
    for `x ∈ V`. -/
theorem _root_.zsmul_generator_injective
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Injective (fun (n : ℤ) ↦
      n • ((TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V))) := by
  intro n m h
  let P := TopCat.Presheaf.constZ.zeroOutside V
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (T.map (toSheafify J P)) := stalkFunctor_map_iso_toSheafify P x
  have hbij := ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))
  have hgen_eq : ConcreteCategory.hom (T.map (toSheafify J P))
      (P.germ V x hx (TopCat.Presheaf.zeroOutside.generator V)) =
      (TopCat.Sheaf.zeroOutsideInt V).presheaf.germ V x hx
        (TopCat.Sheaf.zeroOutsideInt.generator V) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
      (toSheafify J P) (TopCat.Presheaf.zeroOutside.generator V)
  set gen_P := TopCat.Presheaf.zeroOutside.generator V
  have h' : P.germ V x hx (n • gen_P) = P.germ V x hx (m • gen_P) := by
    rw [map_zsmul, map_zsmul]
    apply hbij.1
    change (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (n • P.germ V x hx gen_P) =
      (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (m • P.germ V x hx gen_P)
    calc
      (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (n • P.germ V x hx gen_P)
          = n • (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (P.germ V x hx gen_P) :=
            map_zsmul (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) n _
      _ = m • (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (P.germ V x hx gen_P) := by
            rwa [hgen_eq]
      _ = (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) (m • P.germ V x hx gen_P) :=
            (map_zsmul (AddCommGrpCat.Hom.hom (T.map (toSheafify J P))) m _).symm
  obtain ⟨W, hxW, iU, iV, hEq⟩ := P.germ_eq x hx hx _ _ h'
  rw [Subsingleton.elim iU iV, map_zsmul, map_zsmul] at hEq
  have hWV : W ≤ V := leOfHom iV
  rw [Subsingleton.elim iV (homOfLE hWV)] at hEq
  have hObjW : P.obj (op W) = AddCommGrpCat.of (ULift ℤ) := by
    simp [P, TopCat.Presheaf.zeroOutside, hWV, TopCat.Presheaf.constZ]
  set resGen := ConcreteCategory.hom (P.map (homOfLE hWV).op) gen_P
  have hresGen_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) resGen = (1 : ULift ℤ) :=
    TopCat.Presheaf.zeroOutside.resGen_eqToHom_eq_one V hWV hObjW
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  simpa using congrArg ULift.down hEq_ULift

end Sheaf

end TopCat
