/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.DimensionCoproducts
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Finite

universe v' u' u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

section

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type u)] [Finite J]
  {F : J ⥤ SSet.{u}} {c : Cocone F}

lemma finite_obj_of_isColimit (hc : IsColimit c) (n : SimplexCategoryᵒᵖ)
    (h : ∀ j, Finite ((F.obj j).obj n)) :
    Finite (c.pt.obj n) := by
  let f : (Σ (j : J), (F.obj j).obj n) → c.pt.obj n := fun ⟨j, x⟩ ↦ (c.ι.app j).app n x
  apply Finite.of_surjective f
  rintro x
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x
  exact ⟨⟨j, y⟩, rfl⟩

lemma isFinite_of_isColimit [∀ j, (F.obj j).IsFinite]
    (hc : IsColimit c) : IsFinite c.pt := by
  obtain ⟨d, _⟩ : ∃ d, ∀ j, HasDimensionLT (F.obj j) d := by
    let d (j : J) : ℕ := (F.obj j).hasDimensionLT_of_isFinite.choose
    have hd (j : J) : HasDimensionLT (F.obj j) (d j) :=
      (F.obj j).hasDimensionLT_of_isFinite.choose_spec
    by_cases hJ : Nonempty J
    · obtain ⟨j₀, hj₀⟩ := Set.exists_upper_bound_image (f := d) ⊤ (Set.toFinite _)
      exact ⟨d j₀, fun j ↦ hasDimensionLT_of_le _ _ _ (hj₀ j (by simp))⟩
    · simp only [not_nonempty_iff] at hJ
      exact ⟨0, fun j ↦ (IsEmpty.false j).elim⟩
  have := hasDimensionLT_of_isColimit hc d inferInstance
  apply isFinite_of_hasDimensionLT _ d
  intro i hi
  have := finite_obj_of_isColimit hc (op ⦋i⦌) inferInstance
  infer_instance

instance [∀ j, (F.obj j).IsFinite] : (colimit F).IsFinite :=
  isFinite_of_isColimit (colimit.isColimit F)

end

instance (J : Type u') [Finite J] : Finite (Discrete J) :=
  Finite.of_surjective Discrete.mk (fun ⟨i⟩ ↦ ⟨i, rfl⟩)

instance {J : Type u'} [Finite J] (X : J → SSet.{u}) [∀ j, (X j).IsFinite] :
    (∐ X).IsFinite := by
  have : ∀ (j : Discrete J), ((Discrete.functor X).obj j).IsFinite := fun ⟨j⟩ ↦ by
    dsimp; infer_instance
  infer_instance

instance (X Y : SSet.{u}) [X.IsFinite] [Y.IsFinite] : (X ⨿ Y).IsFinite := by
  have : ∀ j, ((pair X Y).obj j).IsFinite := by rintro ⟨_ | _⟩ <;> assumption
  infer_instance

end SSet
