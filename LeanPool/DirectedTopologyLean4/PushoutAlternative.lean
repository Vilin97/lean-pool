/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# LeanPool.DirectedTopologyLean4.PushoutAlternative
-/

/-
  This file contains an alternative way for proving a commutative square in a category is a pushout.
-/

universe u

open CategoryTheory

namespace PushoutAlternative

variable {X X₁ X₂ X₀ : Cat.{u, u}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X} {j₂ : X₂ ⟶ X}

lemma isPushout_alternative (h_comm : i₁ ≫ j₁ = i₂ ≫ j₂)
    (h_uniq : ∀ (C : Cat.{u, u}) (F₁ : X₁ ⟶ C) (F₂ : X₂ ⟶ C) (_ : i₁ ≫ F₁ = i₂ ≫ F₂),
      ∃! (F : X ⟶ C), j₁ ≫ F = F₁ ∧ j₂ ≫ F = F₂) :
    IsPushout i₁ i₂ j₁ j₂ := by
  let w : CommSq i₁ i₂ j₁ j₂ := { w := h_comm }
  have hcond : ∀ (s : Limits.Cocone (Limits.span i₁ i₂)),
      i₁ ≫ Limits.PushoutCocone.inl s = i₂ ≫ Limits.PushoutCocone.inr s :=
    Limits.PushoutCocone.condition
  let desc : ∀ (s : Limits.PushoutCocone i₁ i₂), X ⟶ s.pt :=
    fun s => Classical.choose (h_uniq s.pt _ _ (hcond s))
  have fac_left : ∀ (s : Limits.PushoutCocone i₁ i₂), j₁ ≫ desc s = s.inl :=
    fun s => (Classical.choose_spec (h_uniq s.pt _ _ (hcond s))).1.1
  have fac_right : ∀ (s : Limits.PushoutCocone i₁ i₂), j₂ ≫ desc s = s.inr :=
    fun s => (Classical.choose_spec (h_uniq s.pt _ _ (hcond s))).1.2
  have uniq : ∀ (s : Limits.PushoutCocone i₁ i₂) (m : X ⟶ s.pt)
      (_ : ∀ j : Limits.WalkingSpan, w.cocone.ι.app j ≫ m = s.ι.app j), m = desc s := by
    rintro s m h
    apply (Classical.choose_spec (h_uniq s.pt _ _ (hcond s))).right
    exact ⟨h Limits.WalkingCospan.left, h Limits.WalkingCospan.right⟩
  exact IsPushout.of_isColimit'
    w (Limits.PushoutCocone.isColimitAux _ desc fac_left fac_right uniq)

end PushoutAlternative
