/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Part
import LeanPool.PartialCombinatoryAlgebras.Basic
import LeanPool.PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-!
# Total combinatory algebras

A total combinatory structure on a type `A`, and the fact that any total
combinatory algebra induces a partial combinatory algebra on the same type.
-/

namespace LeanPool.PartialCombinatoryAlgebras

/-- A (total) combinatory structure on a set `A`. -/
class CA (A : Type*) extends HasDot A where
  /-- The `K` combinator. -/
  K : A
  /-- The `S` combinator. -/
  S : A
  /-- The defining equation of `K`. -/
  eq_K : ∀ {a b : A}, K ⬝ a ⬝ b = a
  /-- The defining equation of `S`. -/
  eq_S : ∀ {a b c : A}, S ⬝ a ⬝ b ⬝ c = (a ⬝ c) ⬝ (b ⬝ c)

namespace Part

/-- Missing from `Part`. -/
@[simps]
def map₂ {α β γ : Type*} (f : α → β → γ) (u : _root_.Part α) (v : _root_.Part β) : _root_.Part γ :=
  ⟨u.Dom ∧ v.Dom, fun p => f (u.get (And.left p)) (v.get (And.right p))⟩

@[simp]
lemma eq_map₂_some {α β γ : Type*} (f : α → β → γ) (a : α) (b : β) :
    map₂ f (.some a) (.some b) = .some (f a b) := by
  rw [_root_.Part.eq_some_iff]
  exact ⟨⟨trivial, trivial⟩, rfl⟩

end Part

namespace CA

/-- A total application induces a partial application -/
@[reducible]
instance partialApp {A : Type} [d : HasDot A] : PartialApplication A where
  app := Part.map₂ d.dot

lemma eq_app {A : Type} [HasDot A] {u v : Part A} (hu : u ⇓) (hv : v ⇓) :
    u ⬝ v = .some (u.get hu ⬝ v.get hv) := by
  nth_rewrite 1 [← Part.some_get hu]
  nth_rewrite 1 [← Part.some_get hv]
  apply Part.eq_map₂_some

/-- A combinatory algebra is a PCA. -/
instance isPCA {A : Type} [CA A] : PCA A where
  K := .some K
  S := .some S
  df_K₀ := by trivial
  df_K₁ := by intros; trivial
  eq_K := by
    intro u v hu hv
    rw [CA.eq_app trivial hu, CA.eq_app trivial hv]
    simp only [Part.get_some]
    rw [CA.eq_K]
    exact Part.some_get hu
  df_S₀ := by trivial
  df_S₁ := by intros; trivial
  df_S₂ := by intros; trivial
  eq_S := by
    intro u v w hu hv hw
    have huw : (u ⬝ w) ⇓ := by rw [CA.eq_app hu hw]; trivial
    have hvw : (v ⬝ w) ⇓ := by rw [CA.eq_app hv hw]; trivial
    have lhs : (Part.some (S : A)) ⬝ u ⬝ v ⬝ w =
        Part.some (S ⬝ u.get hu ⬝ v.get hv ⬝ w.get hw) := by
      rw [CA.eq_app trivial hu, CA.eq_app trivial hv, CA.eq_app trivial hw]
      simp only [Part.get_some]
    have heq1 : (u ⬝ w).get huw = u.get hu ⬝ w.get hw :=
      Part.get_eq_iff_eq_some.mpr (CA.eq_app hu hw)
    have heq2 : (v ⬝ w).get hvw = v.get hv ⬝ w.get hw :=
      Part.get_eq_iff_eq_some.mpr (CA.eq_app hv hw)
    have rhs : (u ⬝ w) ⬝ (v ⬝ w) =
        Part.some (u.get hu ⬝ w.get hw ⬝ (v.get hv ⬝ w.get hw)) := by
      rw [CA.eq_app huw hvw, heq1, heq2]
    rw [lhs, CA.eq_S, ← rhs]

end CA

end LeanPool.PartialCombinatoryAlgebras
