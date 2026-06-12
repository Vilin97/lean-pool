/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.Chain
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Preservation
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # Tree -/


namespace LO
namespace Modal


/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.FiniteTransitiveTree extends Kripke.FiniteFrame,
  Kripke.RootedFrame where
  rel_assymetric : Assymetric Rel
  rel_transitive : IsTrans World Rel

/-- Imported declaration from the Incompleteness formalization. -/
add_decl_doc LO.Modal.Kripke.FiniteTransitiveTree.toRootedFrame

namespace Kripke
namespace FiniteTransitiveTree

lemma rel_irreflexive (T : FiniteTransitiveTree) :
    Std.Irrefl T.Rel :=
  ⟨irreflexive_of_assymetric <| T.rel_assymetric⟩

end FiniteTransitiveTree
end Kripke


/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.Kripke.ValidOnFiniteTransitiveTreeFrame (T :
    Kripke.FiniteTransitiveTree) (φ :
    Formula ℕ) :=
  T.toFrame ⊧ φ

namespace ValidOnFiniteTransitiveTreeFrame

instance semantics :
    Semantics (Formula ℕ) (Kripke.FiniteFrame) :=
  ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩

end ValidOnFiniteTransitiveTreeFrame


namespace Kripke

open Relation (TransGen)

/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteTransitiveTreeModel extends FiniteTransitiveTree, Model where

/-- Imported declaration from the Incompleteness formalization. -/
add_decl_doc FiniteTransitiveTreeModel.toModel

variable {F : Frame} {r : F.World}

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.IsChain F.Rel }
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1
  world_nonempty := ⟨[r], (by simp)⟩

namespace Frame
namespace TreeUnravelling

@[simp 1100]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_length {x y : (F.TreeUnravelling r).World} (h : x ≺ y) : x.1.length < y.1.length := by
  obtain ⟨z, hz⟩ := h;
  rw [←hz];
  simp;

lemma irreflexive : Std.Irrefl (F.TreeUnravelling r).Rel := by
  constructor
  intro x
  simp [TreeUnravelling];

lemma assymetric : Assymetric (F.TreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  omega;

/-- Imported declaration from the Incompleteness formalization. -/
def PMorphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have hchain : (cx.1 ++ [z]).IsChain F.Rel := by
      rw [hz]
      exact cy.2.2
    have h := (List.isChain_append.mp hchain).2.2
    have hx : cx.1.getLast (by aesop) ∈ cx.1.getLast? :=
      List.getLast?_eq_getLast_of_ne_nil (by simp)
    have hy : z ∈ ([z] : List F.World).head? := by simp
    have hlast? : cy.1.getLast? = some z := by
      rw [←hz]
      simp
    have hcy := List.getLast?_eq_getLast_of_ne_nil (l := cy.1) (by aesop)
    have hlast : cy.1.getLast (by aesop) = z := by
      simpa [hcy] using hlast?
    simpa [hlast] using h (cx.1.getLast (by aesop)) hx z hy
  back {cx y} h := by
    simp_all only [Set.mem_setOf_eq];
    use ⟨cx.1 ++ [y], ?_⟩;
    · constructor;
      · simp;
      · use y;
    · constructor;
      · obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      · apply List.IsChain.append;
        · exact cx.2.2;
        · simp;
        · intro z hz; simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'];
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

end TreeUnravelling
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveTreeUnravelling (F : Frame) (r :
    F.World) :=
  (F.TreeUnravelling r)^+

namespace Frame
namespace TransitiveTreeUnravelling

lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_length {x y : (F.TransitiveTreeUnravelling r).World} (Rxy : x ≺ y) :
    x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact TreeUnravelling.rel_length Rxy;
  | tail _ h ih => have := TreeUnravelling.rel_length h; omega;

lemma rel_transitive :
    IsTrans (F.TransitiveTreeUnravelling r).World
      (F.TransitiveTreeUnravelling r).Rel :=
  TransitiveClosure.rel_transitive

lemma rel_asymmetric : Assymetric (F.TransitiveTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  omega;

lemma rel_def {x y : (F.TransitiveTreeUnravelling r).World} :
    x ≺ y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) := by
  constructor;
  · intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy;
      rw [←hz];
      constructor;
      · simp;
      · use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h;
      obtain ⟨_, ⟨zs, hzs⟩⟩ := ih;
      rw [←hw, ←hzs];
      constructor;
      · simp;
      · use zs ++ [w];
        simp [List.append_assoc];
  · replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x;
    replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y;
    subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩;
    simp only [List.cons_append, List.nil_append] at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z =>
      apply TransGen.single;
      use z;
      simp_all only [List.cons_append, List.nil_append];
    | hcons z zs h ih =>
      simp_all only [Set.mem_setOf_eq, List.cons_append, List.nil_append];
      refine TransGen.head ?h₁ <| ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅;
      · use z; simp;
      · apply List.IsChain.prefix hy₂;
        use zs; simp_all;
      · exact hy₂;
      · rw [←hzs]; simp only [List.length_cons, List.length_append, List.length_nil, zero_add,
          add_lt_add_iff_right, add_lt_add_iff_left, lt_add_iff_pos_left];
        by_contra hC;
        simp_all;
      · simp_all;

lemma rooted : (F.TransitiveTreeUnravelling r).isRooted ⟨[r], by tauto⟩ := by
  intro x ha;
  apply rel_def.mpr;
  obtain ⟨zs, hzs⟩ := x.2.1;
  constructor;
  · rw [←hzs];
    by_contra hC;
    simp at hC;
    simp_all;
  · use zs;

/-- Imported declaration from the Incompleteness formalization. -/
abbrev pMorphism (F : Frame) (F_trans : IsTrans F.World F.Rel) (r : F) :
    (F.TransitiveTreeUnravelling r) →ₚ F :=
  (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans

end TransitiveTreeUnravelling
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.TreeUnravelling (M : Kripke.Model) (r : M.World) :
    Kripke.Model where
  toFrame := M.toFrame.TreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a

namespace Model
namespace TreeUnravelling

variable {M : Kripke.Model} {r : M.World}

/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism (M : Kripke.Model) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.TreeUnravelling.PMorphism M.toFrame r) <| by aesop;

end TreeUnravelling
end Model


/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.TransitiveTreeUnravelling (M : Kripke.Model) (r : M.World) :
    Kripke.Model where
  toFrame := M.toFrame.TransitiveTreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a

namespace Model
namespace TransitiveTreeUnravelling

/-- Imported declaration from the Incompleteness formalization. -/
abbrev pMorphism (M : Kripke.Model) (M_trans : IsTrans M.World M.Rel) (r : M.World) :
    M.TransitiveTreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.TransitiveTreeUnravelling.pMorphism M.toFrame M_trans r) <|
      by aesop;

lemma modal_equivalence_at_root (M : Kripke.Model) (M_trans : IsTrans M.World M.Rel) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  :=
    Model.PseudoEpimorphism.modal_equivalence
      (Model.TransitiveTreeUnravelling.pMorphism M M_trans r) (⟨[r], by simp⟩)

end TransitiveTreeUnravelling
end Model


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Model.FiniteTransitiveTreeUnravelling (M : Kripke.Model) (r :
    M.World) :
    Kripke.Model :=
  (M↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteFrame.FiniteTransitiveTreeUnravelling
  (F : FiniteFrame) (F_trans : IsTrans F.World F.Rel) (F_irrefl : Std.Irrefl F.toFrame) (r :
    F.World) : FiniteTransitiveTree :=
  letI T := (F.toFrame↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩
  {
    World := T.World
    Rel := T.Rel
    root := ⟨[⟨r, by tauto⟩], by tauto⟩
    rel_transitive := Frame.TransitiveTreeUnravelling.rel_transitive
    rel_assymetric := Frame.TransitiveTreeUnravelling.rel_asymmetric
    root_rooted := Frame.TransitiveTreeUnravelling.rooted
    world_finite := by
      suffices h : Finite { x // List.IsChain (F.PointGenerated r).Rel x } by
        exact
          Finite.of_injective
          (β := { x // List.IsChain (F.PointGenerated r).Rel x })
          (fun x => ⟨x.1, x.2.2⟩)
          (by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp_all);
      exact List.chains_finite
        (Frame.PointGenerated.rel_transitive (F := F.toFrame) (r := r) F_trans)
        (Frame.PointGenerated.rel_irreflexive (F := F.toFrame) (r := r) F_irrefl)
  }

end Kripke

end Modal
end LO
