/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import Mathlib.CategoryTheory.Action
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Tactic

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

namespace MarshallHall

universe u

/-!
## The labelled Schreier graph and its spanning-tree basis

The action groupoid is equipped with the smaller generating quiver whose edges
are labelled by the original free generators.  This is the finite graph that
the core construction uses; the generic Nielsen--Schreier instance instead
uses the whole free group as a generator synonym.
-/

abbrev CoverVertex (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :=
  ActionCategory (FreeGroup α) A

instance coverQuiver (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    Quiver (CoverVertex α A) where
  Hom x y := {e : α // FreeGroup.of e • x.back = y.back}

/-! The action groupoid is free for this explicit labelled generating quiver. -/

@[reducible] def freeActionGroupoidIsFree (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    IsFreeGroupoid (ActionCategory (FreeGroup α) A) where
  quiverGenerators :=
    ⟨fun a b => {e : α // FreeGroup.of e • a.back = b.back}⟩
  of := fun (e : Subtype _) => ⟨FreeGroup.of e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : α → (A → X) ⋊[mulAutArrow] FreeGroup α := fun e =>
      ⟨fun b => @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, FreeGroup.of e⟩
    let F' : FreeGroup α →* (A → X) ⋊[mulAutArrow] FreeGroup α :=
      FreeGroup.lift f'
    refine ⟨ActionCategory.uncurry F' ?_, ?_, ?_⟩
    · suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id _ by
        exact DFunLike.ext_iff.mp this
      apply FreeGroup.ext_hom
      intro e
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : FreeGroup.of e • a = b⟩
      change (F' (FreeGroup.of _)).left _ = _
      rw [FreeGroup.lift_apply_of]
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have hEF : ActionCategory.curry E = F' := by
        apply FreeGroup.ext_hom
        intro e
        ext b
        · simp only [ActionCategory.curry_apply_left]
          change E.map (ActionCategory.homOfPair b (FreeGroup.of e)) =
            (FreeGroup.lift f' (FreeGroup.of e)).left b
          rw [FreeGroup.lift_apply_of]
          change E.map (ActionCategory.homOfPair b (FreeGroup.of e)) =
            @f (((FreeGroup.of e)⁻¹ • b : A) : ActionCategory (FreeGroup α) A)
              (b : ActionCategory (FreeGroup α) A)
              ⟨e, smul_inv_smul (FreeGroup.of e) b⟩
          have h := hE
            (((FreeGroup.of e)⁻¹ • b : A) : ActionCategory (FreeGroup α) A)
            (b : ActionCategory (FreeGroup α) A)
            (⟨e, smul_inv_smul (FreeGroup.of e) b⟩)
          rw [← h]
          congr 1
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intros
        simp only [← hEF, ActionCategory.uncurry_map, ActionCategory.curry_apply_left,
          ActionCategory.coe_back, ActionCategory.homOfPair.val]
        rfl

/-!
The basis is indexed by the actual labelled edges outside the chosen tree.
The proof is the same unique-lift argument as Mathlib's spanning-tree theorem,
but keeps the edge type explicit for later core-support statements.
-/

noncomputable def spanningTreeBasis {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)
      (End (show G from root T)) := by
  classical
  let X : Set _ := (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  apply FreeGroupBasis.ofUniqueLift X
    (fun e => IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom))
  intro Y _ f
  let f' : Labelling (IsFreeGroupoid.Generators G) Y := fun a b e =>
    if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · suffices ∀ {x y} (q : x ⟶ y),
        F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : Y) by
      rintro ⟨⟨a, b, e⟩, h⟩
      simp only [Functor.mapEnd, DFunLike.coe, this, hF']
      exact dif_neg h
    intro x y q
    suffices ∀ {a} (p : Path (root T) a), F'.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 by
      simp only [this, IsFreeGroupoid.SpanningTree.treeHom, comp_as_mul, inv_as_inv,
        IsFreeGroupoid.SpanningTree.loopOfHom, inv_one, mul_one, one_mul, Functor.map_inv,
        Functor.map_comp]
    intro a p
    induction p with
    | nil =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath]
        simpa only [id_as_one] using! F'.map_id _
    | cons p e ih =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dif_pos (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dif_pos (Or.inr eT)
  · intro E hE
    ext x
    suffices (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
      simpa only [IsFreeGroupoid.SpanningTree.loopOfHom,
        IsFreeGroupoid.SpanningTree.functorOfMonoidHom, IsIso.inv_id,
        IsFreeGroupoid.SpanningTree.treeHom_root, Category.id_comp, Category.comp_id] using! this
    congr
    apply uF'
    intro a b e
    change E (IsFreeGroupoid.SpanningTree.loopOfHom T _) = dite _ _ _
    split_ifs with h
    · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e h]
      change E (1 : End (show G from root T)) = 1
      exact E.map_one
    · exact hE ⟨⟨a, b, e⟩, h⟩

theorem spanningTreeBasis_apply {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    [Arborescence T]
    (e : ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G)))) :
    (spanningTreeBasis T) e = IsFreeGroupoid.SpanningTree.loopOfHom T
      (IsFreeGroupoid.of e.val.hom) := by
  unfold spanningTreeBasis
  dsimp [FreeGroupBasis.ofUniqueLift, FreeGroupBasis.ofLift, FreeGroupBasis.instFunLike]
  change FreeGroup.lift
      (fun e => IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom))
      (FreeGroup.of e) = _
  simp

end MarshallHall
