/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Mathlib.CategoryTheory.Action
public import Mathlib.Combinatorics.Quiver.Covering
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import LeanPool.FiniteGraphFundamentalGroup.Proof

/-! The Schreier graph of a free-group action. Its vertices are action points,
and a generator-labelled edge follows the corresponding left action. The
subgroup application uses the action on cosets.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

/-- The Schreier vertices, represented as objects of the action groupoid. -/
abbrev CoverVertex (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :=
  ActionCategory (FreeGroup α) A

instance coverQuiver (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    Quiver (CoverVertex α A) where
  Hom x y := {e : α // FreeGroup.of e • x.back = y.back}

/-- The one-vertex quiver whose loops will be labeled by the generator type. -/
inductive Rose (α : Type u) : Type u where
  | point : Rose α

instance roseQuiver (α : Type u) : Quiver (Rose α) where
  Hom _ _ := α

/-- Project the Schreier quiver to the rose by retaining each edge's generator label. -/
def coverProjection (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    CoverVertex α A ⥤q Rose α where
  obj _ := Rose.point
  map e := e.val

/-- Outgoing Schreier edges are in bijection with the generator loops of the rose. -/
def coverStarEquiv (α : Type u) (A : Type u) [MulAction (FreeGroup α) A]
    (x : CoverVertex α A) :
    Quiver.Star x ≃ Quiver.Star (Rose.point : Rose α) where
  toFun f := ⟨Rose.point, f.2.val⟩
  invFun e :=
    ⟨((FreeGroup.of e.2 • x.back : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hy :
        ((FreeGroup.of e.val • x.back : A) : CoverVertex α A) = y := by
      apply (ActionCategory.objEquiv (FreeGroup α) A).symm.injective
      exact e.property
    apply Sigma.subtype_ext hy
    rfl
  right_inv := by
    rintro ⟨_, e⟩
    rfl

/-- Incoming Schreier edges are in bijection with the generator loops of the rose. -/
def coverCostarEquiv (α : Type u) (A : Type u) [MulAction (FreeGroup α) A]
    (x : CoverVertex α A) :
    Quiver.Costar x ≃ Quiver.Costar (Rose.point : Rose α) where
  toFun f := ⟨Rose.point, f.2.val⟩
  invFun e :=
    ⟨(((FreeGroup.of e.2)⁻¹ • x.back : A) : CoverVertex α A),
      ⟨e.2, by simp⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hy :
        (((FreeGroup.of e.val)⁻¹ • x.back : A) : CoverVertex α A) = y := by
      have heq : (FreeGroup.of e.val)⁻¹ • x.back = y.back :=
        inv_smul_eq_iff.mpr e.property.symm
      apply (ActionCategory.objEquiv (FreeGroup α) A).symm.injective
      exact heq
    apply Sigma.subtype_ext hy
    rfl
  right_inv := by
    rintro ⟨_, e⟩
    rfl

theorem coverProjection_isCovering (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    (coverProjection α A).IsCovering := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · let e := coverStarEquiv α A x
    have he : (coverProjection α A).star x =
        (e : Quiver.Star x → Quiver.Star (Rose.point : Rose α)) := by
      funext f
      rcases f with ⟨y, f⟩
      rfl
    rw [he]
    exact e.bijective
  · let e := coverCostarEquiv α A x
    have he : (coverProjection α A).costar x =
        (e : Quiver.Costar x → Quiver.Costar (Rose.point : Rose α)) := by
      funext f
      rcases f with ⟨y, f⟩
      rfl
    rw [he]
    exact e.bijective

/-! The action groupoid admits a smaller, explicit generating quiver when the
acting free group is presented as `FreeGroup α`.  Mathlib's general
Nielsen--Schreier instance uses an abstract chosen basis; this version keeps
the original generator type visible for the cardinality computation. -/

/-- Present the free-group action groupoid by its Schreier quiver of generator edges. -/
@[reducible] def freeActionGroupoidIsFree (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    IsFreeGroupoid (ActionCategory (FreeGroup α) A) where
  quiverGenerators :=
    ⟨fun a b => {e : α // FreeGroup.of e • a.back = b.back}⟩
  of := fun (e : Subtype _) => ⟨FreeGroup.of e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : α → (A → X) ⋊[mulAutArrow] FreeGroup α := fun e =>
      ⟨fun b => @f (((FreeGroup.of e)⁻¹ • b : A) : ActionCategory (FreeGroup α) A) (b :
        ActionCategory (FreeGroup α) A) ⟨e, smul_inv_smul _ b⟩, FreeGroup.of e⟩
    let F' : FreeGroup α →* (A → X) ⋊[mulAutArrow] FreeGroup α :=
      FreeGroup.lift f'
    refine ⟨ActionCategory.uncurry F' ?_, ?_, ?_⟩
    · suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id _ by
        exact DFunLike.ext_iff.mp this
      apply FreeGroup.ext_hom
      intro e
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      rfl
    · intro a b e
      induction a with | mk a
      induction b with | mk b
      cases e using Subtype.casesOn with | mk e h
      change A at a b
      change FreeGroup.of e • a = b at h
      change (F' (FreeGroup.of _)).left _ = _
      rw [FreeGroup.lift_apply_of]
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have hEF : ActionCategory.curry E = F' := by
        apply FreeGroup.ext_hom
        intro e
        ext b
        · change E.map (ActionCategory.homOfPair b (FreeGroup.of e)) =
            (FreeGroup.lift f' (FreeGroup.of e)).left b
          rw [FreeGroup.lift_apply_of]
          convert! hE _ _ _
          rfl
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intro t g
        apply heq_of_eq
        change E.map (ActionCategory.homOfPair t g) = (F' g).left t
        rw [← hEF]
        rfl

end GraphCoveringTheory
