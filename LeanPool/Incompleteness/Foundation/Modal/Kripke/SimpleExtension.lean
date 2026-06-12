/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Tree
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Preservation
import Mathlib.Data.Finite.Sum

/-! # SimpleExtension -/


namespace LO
namespace Modal
namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FiniteTransitiveTree.SimpleExtension (F : FiniteTransitiveTree) :
    Kripke.FiniteTransitiveTree where
  World := Unit ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inl _, .inr _ => True
    | _ , _ => False
  root := .inl ()
  root_rooted := by
    intro w;
    match w with
    | .inl _ => simp;
    | .inr x => simp []
  rel_assymetric := by
    intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    constructor
    intro x y z hxy hyz;
    match x, y, z with
    | .inl _, .inr _, .inr _ => simp;
    | .inr x, .inr y, .inr z => exact F.rel_transitive.trans _ _ _ hxy hyz;
/-- Imported declaration from the Incompleteness formalization. -/
postfix:max "↧" => FiniteTransitiveTree.SimpleExtension


namespace FiniteTransitiveTree
namespace SimpleExtension

variable {T : FiniteTransitiveTree} {x y : T.World}

instance : Coe (T.World) (T↧.World) := ⟨Sum.inr⟩

@[simp] lemma root_not_original : (Sum.inr x) ≠ T↧.root := by simp [SimpleExtension]

lemma root_eq : (Sum.inl ()) = T↧.root := by simp [SimpleExtension];

lemma forth (h : x ≺ y) : T↧.Rel x y := by simpa [SimpleExtension];

/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism : T.toFrame →ₚ (T↧.toFrame) where
  toFun x := x
  forth := forth
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', SimpleExtension] at h;
    | .inr y => exact ⟨y, rfl, h⟩;

lemma through_original_root {x : T↧.World} (h : T↧.root ≺ x) :
    x = T.root ∨ (Sum.inr T.root ≺ x) := by
  match x with
  | .inl x =>
    have := T↧.rel_irreflexive.irrefl _ h;
    contradiction;
  | .inr x =>
    by_cases h : x = T.root;
    · subst h; left; tauto;
    · right; exact FiniteTransitiveTree.SimpleExtension.forth <| T.root_rooted x h;

end SimpleExtension
end FiniteTransitiveTree


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteTransitiveTreeModel.SimpleExtension (M :
    FiniteTransitiveTreeModel) :
    Kripke.FiniteTransitiveTreeModel where
  toFiniteTransitiveTree := M.toFiniteTransitiveTree↧
  Val x a :=
    match x with
    | .inl _ => M.Val M.root a
    | .inr x => M.Val x a
/-- Imported declaration from the Incompleteness formalization. -/
postfix:max "↧" => FiniteTransitiveTreeModel.SimpleExtension


namespace FiniteTransitiveTreeModel
namespace SimpleExtension

variable {M : FiniteTransitiveTreeModel}

instance : Coe (M.World) (M↧.World) := ⟨Sum.inr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism :
    M.toModel →ₚ (M↧.toModel) :=
  Model.PseudoEpimorphism.ofAtomic (FiniteTransitiveTree.SimpleExtension.pMorphism) <| by
  simp [FiniteTransitiveTree.SimpleExtension.pMorphism];

lemma modal_equivalence_original_world {x : M.toModel.World} :
    ModalEquivalent (M₁ := M.toModel) (M₂ := (M↧).toModel) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence pMorphism;

end SimpleExtension
end FiniteTransitiveTreeModel


end Kripke
end Modal
end LO
