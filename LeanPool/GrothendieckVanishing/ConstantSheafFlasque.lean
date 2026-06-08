/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import LeanPool.GrothendieckVanishing.ClosedImmersionCohomology
import LeanPool.GrothendieckVanishing.TopologicalKrullDim
import LeanPool.GrothendieckVanishing.ZeroOutside

/-!
# Flasqueness of the constant sheaf on an irreducible space

On an irreducible topological space, the constant sheaf with values in any object of
`AddCommGrpCat` is flasque. The proof descends from the explicit `+`-construction:
the presheaf-level surjectivity lemmas `toPlus_surjective_of_const` and
`toPlus_surjective_of_firstPlus` combine via a section-by-section gluing argument that
relies crucially on `nonempty_preirreducible_inter` for irreducible spaces.

## Main results

* `sheafify_const_flasque_of_irreducible`
* `presheafToSheaf_const_flasque_of_irreducible`
* `constantSheaf_flasque_of_irreducible`
* `isFlasqueSheaf_zeroOutsideInt_top`
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite GrothendieckTopology GrothendieckTopology.Plus

theorem toPlus_injective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty)
    (a b : ((Functor.const (Opens X)ᵒᵖ).obj A).obj (op U))
    (h : ConcreteCategory.hom
        (((Opens.grothendieckTopology X).toPlus
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U)) a =
      ConcreteCategory.hom
        (((Opens.grothendieckTopology X).toPlus
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U)) b) :
    a = b := by
  rw [toPlus_eq_mk, toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, _, _, heq⟩ := h
  obtain ⟨p, hp⟩ := hU
  obtain ⟨V, f, hf, _⟩ := W.2 p hp
  change (ConcreteCategory.hom (𝟙 A)) a = (ConcreteCategory.hom (𝟙 A)) b
  exact congr_fun (congr_arg Subtype.val heq) (⟨V, f, hf⟩ : W.Arrow)

theorem toPlus_surjective_of_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective
      (ConcreteCategory.hom
        (((Opens.grothendieckTopology X).toPlus
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U))) := by
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨V₀, f₀, hf₀, hx₀mem⟩ := S.2 x₀ hx₀
  let I₀ : S.Arrow := ⟨V₀, f₀, hf₀⟩
  have hI₀ : (I₀.Y : Set X).Nonempty := ⟨x₀, hx₀mem⟩
  refine ⟨x I₀, ?_⟩
  have hxmk : x = Meq.mk S (x I₀) := Meq.ext _ _ fun I ↦ by
    change (ConcreteCategory.hom (𝟙 A)) (x I) = (ConcreteCategory.hom (𝟙 A)) (x I₀)
    exact x.condition (Cover.Relation.mk' (fst := I) (snd := I₀)
      ⟨I.Y ⊓ I₀.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩)
  rw [hx, hxmk, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  change (AddMonoidHom.id A) ((AddMonoidHom.id A) (x I₀)) =
    (AddMonoidHom.id A) (x I₀)
  rfl

theorem toPlus_naturality_const
    {X : Type u} [TopologicalSpace X] {A : AddCommGrpCat.{u}}
    {U V : Opens X} (i : U ⟶ V)
    (a : ((Functor.const (Opens X)ᵒᵖ).obj A).obj (op V)) :
    ConcreteCategory.hom
        (((Opens.grothendieckTopology X).toPlus
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U)) a =
      ConcreteCategory.hom
        (((Opens.grothendieckTopology X).plusObj
          ((Functor.const (Opens X)ᵒᵖ).obj A)).map i.op)
        (ConcreteCategory.hom
          (((Opens.grothendieckTopology X).toPlus
            ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op V)) a) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  have nat := ((Opens.grothendieckTopology X).toPlus P).naturality i.op
  calc ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus P).app (op U)) a
      = ConcreteCategory.hom (P.map i.op ≫
          ((Opens.grothendieckTopology X).toPlus P).app (op U)) a := by
        rw [show P.map i.op = 𝟙 _ by
          ext x
          change (ConcreteCategory.hom (𝟙 A)) x = x
          rfl]
        rfl
    _ = ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus P).app (op V) ≫
          ((Opens.grothendieckTopology X).plusObj P).map i.op) a := by rw [nat]
    _ = _ := ConcreteCategory.comp_apply _ _ _

theorem toPlus_surjective_of_firstPlus
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X] {A : AddCommGrpCat.{u}}
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ConcreteCategory.hom
      (((Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          ((Functor.const (Opens X)ᵒᵖ).obj A))).app (op U))) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  intro y; obtain ⟨S, x, hx⟩ := exists_rep y
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨V₀, f₀, hf₀, hx₀mem⟩ := S.2 x₀ hx₀
  let I₀ : S.Arrow := ⟨V₀, f₀, hf₀⟩
  have hI₀ : (I₀.Y : Set X).Nonempty := ⟨x₀, hx₀mem⟩
  obtain ⟨a, ha⟩ := toPlus_surjective_of_const I₀.Y hI₀ (x I₀)
  use ConcreteCategory.hom (((Opens.grothendieckTopology X).toPlus P).app (op U)) a
  rw [hx, toPlus_eq_mk, eq_mk_iff_exists]
  refine ⟨S, homOfLE le_top, 𝟙 S, ?_⟩
  apply Meq.ext; intro I
  simp only [Meq.refine, Meq.mk]
  by_cases hI : (I.Y : Set X).Nonempty
  · symm
    obtain ⟨b, hb⟩ := toPlus_surjective_of_const I.Y hI (x I)
    have hcond := x.condition (Cover.Relation.mk' (fst := I₀) (snd := I)
      ⟨I₀.Y ⊓ I.Y, homOfLE inf_le_left, homOfLE inf_le_right, Subsingleton.elim _ _⟩)
    change ConcreteCategory.hom (((Opens.grothendieckTopology X).plusObj P).map
        (homOfLE inf_le_left).op) (x I₀) =
      ConcreteCategory.hom (((Opens.grothendieckTopology X).plusObj P).map
        (homOfLE inf_le_right).op) (x I) at hcond
    rw [← ha, ← hb, ← toPlus_naturality_const (homOfLE inf_le_left) a,
      ← toPlus_naturality_const (homOfLE inf_le_right) b] at hcond
    have hab : a = b := toPlus_injective_of_const (I₀.Y ⊓ I.Y)
      (nonempty_preirreducible_inter I₀.Y.isOpen I.Y.isOpen hI₀ hI) a b hcond
    simpa [← hb, ← hab] using toPlus_naturality_const I.f a
  · have hIbot : I.Y = ⊥ := Opens.ext (by simpa [Set.not_nonempty_iff_eq_empty] using hI)
    have hcov : (⊥ : Sieve (⊥ : Opens X)) ∈ (Opens.grothendieckTopology X) ⊥ :=
      fun _ hp ↦ (Opens.mem_bot.mp hp).elim
    exact @Subsingleton.elim _ (hIbot ▸ ⟨fun x y ↦
      Plus.sep _ ⟨⊥, hcov⟩ x y fun ⟨_, _, hf⟩ ↦ absurd hf id⟩) _ _

/-- On an irreducible space, the sheafification of the constant presheaf is flasque. -/
theorem sheafify_const_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] (A : AddCommGrpCat.{u}) :
    IsFlasqueSheaf (⟨(Opens.grothendieckTopology X).sheafify ((Functor.const (Opens X)ᵒᵖ).obj A),
      (Opens.grothendieckTopology X).sheafify_isSheaf ((Functor.const (Opens X)ᵒᵖ).obj A)⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  intro U V i
  by_cases hU : (U : Set X) = ∅
  · have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    haveI : Subsingleton (ToType (((Opens.grothendieckTopology X).sheafify P).obj (op ⊥))) :=
      AddCommGrpCat.subsingleton_of_isZero
        (TopCat.Sheaf.isTerminalOfEmpty
          ⟨_, (Opens.grothendieckTopology X).sheafify_isSheaf P⟩).isZero
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hUne : (U : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr hU
    have hfac : ((Opens.grothendieckTopology X).toSheafify P).app (op V) ≫
        ((Opens.grothendieckTopology X).sheafify P).map i.op =
        ((Opens.grothendieckTopology X).toSheafify P).app (op U) := by
      rw [← (((Opens.grothendieckTopology X).toSheafify P).naturality i.op)]
      change 𝟙 A ≫ ((Opens.grothendieckTopology X).toSheafify P).app (op U) =
        ((Opens.grothendieckTopology X).toSheafify P).app (op U)
      rw [Category.id_comp]
    have hToSheafify : ((Opens.grothendieckTopology X).toSheafify P).app (op U) =
        ((Opens.grothendieckTopology X).toPlus P).app (op U) ≫
          ((Opens.grothendieckTopology X).toPlus
            ((Opens.grothendieckTopology X).plusObj P)).app (op U) := by
      simp only [GrothendieckTopology.toSheafify,
        (Opens.grothendieckTopology X).plusMap_toPlus, NatTrans.comp_app]
      rfl
    have hEpiToSheafify : Epi (((Opens.grothendieckTopology X).toSheafify P).app (op U)) := by
      apply ConcreteCategory.epi_of_surjective
      rw [hToSheafify]
      intro y
      obtain ⟨z, hz⟩ := toPlus_surjective_of_firstPlus (X := X) U hUne y
      obtain ⟨a, ha⟩ := toPlus_surjective_of_const (X := X) U hUne z
      exact ⟨a, by
        change ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toPlus
              ((Opens.grothendieckTopology X).plusObj P)).app (op U))
            (ConcreteCategory.hom
              (((Opens.grothendieckTopology X).toPlus P).app (op U)) a) = y
        rw [ha]
        exact hz⟩
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hEpiToSheafify hfac

/-- On an irreducible space, the presheaf-to-sheaf image of the constant presheaf is flasque. -/
theorem presheafToSheaf_const_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X] (A : AddCommGrpCat.{u}) :
    IsFlasqueSheaf
      (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((Functor.const (Opens X)ᵒᵖ).obj A))) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  intro U V i
  let e := plusPlusIsoSheafify (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) (P := P)
  haveI : Epi (((Opens.grothendieckTopology X).sheafify P).map i.op) := by
    simpa using sheafify_const_flasque_of_irreducible (X := X) A (U := U) (V := V) i
  haveI : Epi (e.hom.app (op V) ≫
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) P).map i.op) := by
    rw [← e.hom.naturality i.op]; infer_instance
  exact epi_of_epi (e.hom.app (op V))
    ((CategoryTheory.sheafify (Opens.grothendieckTopology X) P).map i.op)

theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) :
    IsFlasqueSheaf (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A)) := by
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  intro U V i
  change Epi ((((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    P).obj).map i.op)
  exact presheafToSheaf_const_flasque_of_irreducible (X := X) A (U := U) (V := V) i

/-- `zeroOutsideInt ⊤` is flasque on an irreducible space: it is the sheafification of
    `constZ.zeroOutside ⊤ ≅ constZ` (via `zeroOutsideTopIso`), and the constant sheaf
    on an irreducible space is flasque (`constantSheaf_flasque_of_irreducible`). -/
theorem isFlasqueSheaf_zeroOutsideInt_top (X : TopCat.{u}) [IrreducibleSpace X] :
    IsFlasqueSheaf (TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)) := by
  intro U W i
  let J := Opens.grothendieckTopology (T := X)
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj A
  let e :=
    (presheafToSheaf J AddCommGrpCat.{u}).mapIso
      (TopCat.Presheaf.zeroOutsideTopIso (F := TopCat.Presheaf.constZ))
  let eP := (sheafToPresheaf J AddCommGrpCat.{u}).mapIso e
  have hconst : Epi (((presheafToSheaf J AddCommGrpCat.{u}).obj P).obj.map i.op) :=
    presheafToSheaf_const_flasque_of_irreducible X A (U := U) (V := W) i
  have hconst' : Epi
      (((sheafToPresheaf J AddCommGrpCat.{u}).obj
        ((presheafToSheaf J AddCommGrpCat.{u}).obj TopCat.Presheaf.constZ)).map i.op) := by
    change Epi (((presheafToSheaf J AddCommGrpCat.{u}).obj P).obj.map i.op)
    exact hconst
  haveI : IsIso (eP.hom.app (op U)) := CategoryTheory.NatIso.hom_app_isIso eP (op U)
  haveI : IsIso (eP.hom.app (op W)) := CategoryTheory.NatIso.hom_app_isIso eP (op W)
  have hepiComp : Epi
      (eP.hom.app (op W) ≫
        ((sheafToPresheaf J AddCommGrpCat.{u}).obj
          ((presheafToSheaf J AddCommGrpCat.{u}).obj TopCat.Presheaf.constZ)).map i.op) :=
    epi_comp' inferInstance hconst'
  have hcomp : Epi (((TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X)).obj.map i.op) ≫
      eP.hom.app (op U)) := by
    change Epi
      (((sheafToPresheaf J AddCommGrpCat.{u}).obj
          ((presheafToSheaf J AddCommGrpCat.{u}).obj
            (TopCat.Presheaf.zeroOutside ⊤ TopCat.Presheaf.constZ))).map i.op ≫
        eP.hom.app (op U))
    rw [eP.hom.naturality i.op]
    exact hepiComp
  change Epi
    (((sheafToPresheaf J AddCommGrpCat.{u}).obj
        ((presheafToSheaf J AddCommGrpCat.{u}).obj
          (TopCat.Presheaf.zeroOutside ⊤ TopCat.Presheaf.constZ))).map i.op)
  exact (epi_comp_iff_of_isIso
    (((sheafToPresheaf J AddCommGrpCat.{u}).obj
        ((presheafToSheaf J AddCommGrpCat.{u}).obj
          (TopCat.Presheaf.zeroOutside ⊤ TopCat.Presheaf.constZ))).map i.op)
    (eP.hom.app (op U))).mp hcomp
