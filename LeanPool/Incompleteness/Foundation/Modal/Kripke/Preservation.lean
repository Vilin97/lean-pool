/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Closure

/-! # Preservation -/


namespace LO
namespace Modal

namespace Kripke

open Formula.Kripke

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.Model.Bisimulation (M₁ M₂ : Kripke.Model) where
  /-- Imported declaration from the Incompleteness formalization. -/
  toRel : Rel M₁.World M₂.World
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : ℕ} : toRel x₁ x₂ → ((M₁ x₁ a) ↔ (M₂ x₂ a))
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ →
    ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ →
    ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " ⇄ " => Model.Bisimulation

instance : CoeFun (Model.Bisimulation M₁ M₂) (fun _ => M₁.World → M₂.World → Prop) :=
  ⟨fun bi => bi.toRel⟩

end «lp_section_1»


section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
def ModalEquivalent {M₁ M₂ : Model} (w₁ : M₁.World) (w₂ : M₂.World) : Prop := ∀ {φ}, w₁ ⊧ φ ↔ w₂ ⊧ φ
/-- Imported declaration from the Incompleteness formalization. -/
infix:50 " ↭ " => ModalEquivalent

lemma modal_equivalent_of_bisimilar (Bi : M₁ ⇄ M₂) (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro φ;
  induction φ using Formula.rec' generalizing x₁ x₂ with
  | hatom a => exact Bi.atomic bisx;
  | hfalsum => simp [Satisfies];
  | himp φ ψ ihp ihq =>
    constructor;
    · exact fun hpq hp => ihq bisx |>.mp <| hpq <| ihp bisx |>.mpr hp;
    · exact fun hpq hp => ihq bisx |>.mpr <| hpq <| ihp bisx |>.mp hp;
  | hbox φ ih =>
    constructor;
    · intro h y₂ rx₂y₂;
      obtain ⟨y₁, ⟨bisy, rx₁y₁⟩⟩ := Bi.back bisx rx₂y₂;
      exact ih bisy |>.mp (h _ rx₁y₁);
    · intro h y₁ rx₁y₁;
      obtain ⟨y₂, ⟨bisy, rx₂y₂⟩⟩ := Bi.forth bisx rx₁y₁;
      exact ih bisy |>.mpr (h _ rx₂y₂);

end «lp_section_2»


section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.Frame.PseudoEpimorphism (F₁ F₂ : Kripke.Frame) where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : F₁.World → F₂.World
  forth {x y : F₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : F₁.World} {v : F₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u

/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " →ₚ " => Frame.PseudoEpimorphism

instance : CoeFun (Frame.PseudoEpimorphism F₁ F₂) (fun _ => F₁.World → F₂.World) :=
  ⟨fun f => f.toFun⟩

namespace Frame
namespace PseudoEpimorphism

variable {F F₁ F₂ F₃ : Kripke.Frame}

/-- Imported declaration from the Incompleteness formalization. -/
def id : F →ₚ F where
  toFun := _root_.id
  forth := by simp;
  back := by simp;

/-- Imported declaration from the Incompleteness formalization. -/
def TransitiveClosure (f : F₁ →ₚ F₂) (F₂_trans : IsTrans F₂.World F₂.Rel) : F₁^+ →ₚ F₂ where
  toFun := f.toFun
  forth := by
    intro x y hxy;
    induction hxy with
    | single hxy => exact f.forth hxy;
    | @tail z y _ Rzy Rxz =>
      replace Rzy := f.forth Rzy;
      exact F₂_trans.trans _ _ _ Rxz Rzy;
  back := by
    intro x w hxw;
    obtain ⟨u, ⟨rfl, hxu⟩⟩ := f.back hxw;
    exact ⟨u, rfl, Frame.RelTransGen.single hxu⟩;

/-- Imported declaration from the Incompleteness formalization. -/
def comp (f : F₁ →ₚ F₂) (g : F₂ →ₚ F₃) : F₁ →ₚ F₃ where
  toFun := g ∘ f
  forth := by
    intro x y hxy;
    exact g.forth <| f.forth hxy;
  back := by
    intro x w hxw;
    obtain ⟨y, ⟨rfl, hxy⟩⟩ := g.back hxw;
    obtain ⟨u, ⟨rfl, hfu⟩⟩ := f.back hxy;
    exact ⟨u, by simp_all, hfu⟩;

end PseudoEpimorphism
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.Model.PseudoEpimorphism (M₁ M₂ :
    Kripke.Model) extends M₁.toFrame →ₚ M₂.toFrame where
  atomic {w : M₁.World} : (M₁ w a) ↔ (M₂ (toFun w) a)

/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " →ₚ " => Model.PseudoEpimorphism

instance : CoeFun (Model.PseudoEpimorphism M₁ M₂) (fun _ => M₁.World → M₂.World) :=
  ⟨fun f => f.toFun⟩

namespace Model
namespace PseudoEpimorphism

variable {M M₁ M₂ M₃ : Kripke.Model}

/-- Imported declaration from the Incompleteness formalization. -/
def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp;
  back := by simp;
  atomic := by simp;

/-- Imported declaration from the Incompleteness formalization. -/
def ofAtomic (f : M₁.toFrame →ₚ M₂.toFrame) (atomic : ∀ {w a}, (M₁ w a) ↔ (M₂ (f w) a)) :
    M₁ →ₚ M₂ where
  toFun := f
  forth := f.forth
  back := f.back
  atomic := atomic

/-- Imported declaration from the Incompleteness formalization. -/
def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ :=
  ofAtomic (f.toPseudoEpimorphism.comp (g.toPseudoEpimorphism)) <| by
  intro x φ;
  exact ⟨fun h => g.atomic.mp <| f.atomic.mp h, fun h => f.atomic.mpr <| g.atomic.mpr h⟩;

/-- Imported declaration from the Incompleteness formalization. -/
def bisimulation (f : M₁ →ₚ M₂) : M₁ ⇄ M₂ where
  toRel := fun x₁ x₂ => f x₁ = x₂
  atomic := by
    intro x₁ x₂ a hx
    subst x₂
    exact ⟨f.atomic.mp, f.atomic.mpr⟩
  forth := by
    intro x₁ y₁ x₂ hx rx₁y₁
    subst x₂
    exact ⟨f y₁, rfl, f.forth rx₁y₁⟩
  back := by
    intro x₁ x₂ y₂ hx rx₂y₂
    subst x₂
    exact f.back rx₂y₂

lemma modal_equivalence (f : M₁ →ₚ M₂) (w : M₁.World) : w ↭ (f w) := by
  apply modal_equivalent_of_bisimilar <| Model.PseudoEpimorphism.bisimulation f;
  rfl

end PseudoEpimorphism
end Model


variable {F₁ F₂ : Kripke.Frame} {M₁ M₂ : Kripke.Model}

lemma validOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective :
    Function.Surjective f) : F₁ ⊧ φ → F₂ ⊧ φ := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  obtain ⟨w₁, rfl⟩ := f_surjective w₂;
  apply ValidOnFrame.not_of_exists_valuation_world;
  let V₁ := fun w a => V₂ (f w) a;
  use V₁, w₁;
  exact Model.PseudoEpimorphism.modal_equivalence (M₁ := ⟨F₁, V₁⟩) (M₂ := ⟨F₂, V₂⟩) {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := by aesop;
  } w₁ |>.not.mpr h;

lemma theory_ValidOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective :
    Function.Surjective f) : F₁ ⊧* T → F₂ ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h φ hp;
  exact validOnFrame_of_surjective_pseudoMorphism f f_surjective (h hp);

end «lp_section_3»


/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w

/-- Imported declaration from the Incompleteness formalization. -/
structure RootedFrame extends Kripke.Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  root : World
  root_rooted : Frame.isRooted _ root
  /-- Imported declaration from the Incompleteness formalization. -/
  default := root


section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Frame.PointGenerated (F : Kripke.Frame) (r : F.World) :
    Kripke.RootedFrame where
  World := { w | w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
  root := ⟨r, by tauto⟩
  root_rooted := by
    rintro ⟨x, (rfl | hx)⟩;
    · intro h; contradiction;
    · intro _; exact hx;
/-- Imported declaration from the Incompleteness formalization. -/
infix:100 "↾" => Frame.PointGenerated

namespace Frame
namespace PointGenerated

variable {F : Kripke.Frame} {r : F.World}

lemma rel_transitive (F_trans : IsTrans F.World F.Rel) : IsTrans (F↾r).World (F↾r).Rel := by
  exact ⟨fun _ _ _ hxy hyz => F_trans.trans _ _ _ hxy hyz⟩

lemma rel_irreflexive (F_irrefl : Std.Irrefl F.Rel) : Std.Irrefl (F↾r).Rel :=
  ⟨fun x h => F_irrefl.irrefl x.1 h⟩

lemma rel_universal (F_refl : Std.Refl F.Rel) (F_eucl : Euclidean F.Rel) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl.refl F_eucl;
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  · exact F_refl.refl _;
  · exact hy;
  · exact F_symm hx;
  · apply F_symm <| F_eucl hx hy;

instance [Finite F.World] : Finite (F↾r).World := by
  unfold Frame.PointGenerated;
  apply Subtype.finite;

instance [DecidableEq F.World] : DecidableEq (F↾r).World := by
  apply Subtype.instDecidableEq (p := fun w => w = r ∨ r ≺ w);

end PointGenerated
end Frame


/-- Imported declaration from the Incompleteness formalization. -/
structure RootedModel extends Kripke.Model, Kripke.RootedFrame where

/-- Imported declaration from the Incompleteness formalization. -/
add_decl_doc LO.Modal.Kripke.RootedModel.toRootedFrame


/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.Model.PointGenerated (M : Kripke.Model) (r : M.World) :
    Kripke.RootedModel :=
  letI rF := M.toFrame↾r;
  {
    toFrame := rF.toFrame
    Val := fun w a => M.Val w.1 a
    root := rF |>.root
    root_rooted := rF.root_rooted
  }
/-- Imported declaration from the Incompleteness formalization. -/
infix:100 "↾" => Model.PointGenerated

namespace Model
namespace PointGenerated

variable {M : Kripke.Model}

/-- Imported declaration from the Incompleteness formalization. -/
def bisimulationOfTrans (M_trans : IsTrans M.World M.Rel) (r : M.World) : (M↾r).toModel ⇄ M where
  toRel x y := x.1 = y
  atomic := by
    rintro x y a rfl;
    simp [Model.PointGenerated];
  forth := by
    rintro x₁ y₁ x₂ rfl Rx₂y₁;
    exact ⟨y₁.1, by simp, Rx₂y₁⟩;
  back := by
    rintro ⟨x₁, (rfl | hx₁)⟩ x₂ y₂ rfl Rx₂y₂;
    · exact ⟨⟨y₂, by right; exact Rx₂y₂⟩, by simp, Rx₂y₂⟩;
    · refine ⟨⟨y₂, ?_⟩, by simp, Rx₂y₂⟩;
      right;
      exact M_trans.trans _ _ _ hx₁ Rx₂y₂;

lemma modal_equivalent_at_root (M_trans : IsTrans M.World M.Rel) (r : M.World) :
    ModalEquivalent (M₁ :=
  (M↾r).toModel) (M₂ := M) ⟨r, by simp⟩ r
  :=
    modal_equivalent_of_bisimilar (bisimulationOfTrans M_trans r) <|
        by simp [bisimulationOfTrans];

end PointGenerated
end Model

end «lp_section_4»


section «lp_section_5»

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Modal.Kripke.Frame.GeneratedSub (F₁ F₂ : Kripke.Frame) extends F₁ →ₚ F₂ where
 monic : Function.Injective toFun

/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " ⊆ₚ " => Frame.GeneratedSub

end «lp_section_5»


end Kripke

end Modal
end LO
