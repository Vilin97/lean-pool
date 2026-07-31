/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Degenerate

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

@[mk_iff]
class HasDimensionLT (X : SSet.{u}) (d : ℕ) : Prop where
  degenerate_eq_top (n : ℕ) (hn : d ≤ n) : X.degenerate n = ⊤

abbrev HasDimensionLE (X : SSet.{u}) (d : ℕ) := X.HasDimensionLT (d + 1)

section

variable (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] (n : ℕ)

lemma degenerate_eq_top_of_hasDimensionLT (hn : d ≤ n) : X.degenerate n = ⊤ :=
  HasDimensionLT.degenerate_eq_top n hn

lemma nondegenerate_eq_bot_of_hasDimensionLT (hn : d ≤ n) : X.nonDegenerate n = ⊥ := by
  simp [nonDegenerate, X.degenerate_eq_top_of_hasDimensionLT d n hn]

lemma dim_lt_of_nondegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLT d] : n < d := by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nondegenerate_eq_bot_of_hasDimensionLT d n this] at hx

lemma dim_le_of_nondegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLE d] : n ≤ d :=
  Nat.le_of_lt_succ (X.dim_lt_of_nondegenerate x (d + 1))

lemma hasDimensionLT_of_le (hn : d ≤ n) : HasDimensionLT X n where
  degenerate_eq_top i hi :=
    X.degenerate_eq_top_of_hasDimensionLT d i (hn.trans hi)

end

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

instance (d : ℕ) [X.HasDimensionLT d] : HasDimensionLT A d where
  degenerate_eq_top (n : ℕ) (hd : d ≤ n) := by
    ext x
    simp [A.mem_degenerate_iff, X.degenerate_eq_top_of_hasDimensionLT d n hd]

lemma eq_top_iff_of_hasDimensionLT (d : ℕ) [X.HasDimensionLT d] :
    A = ⊤ ↔ ∀ (i : ℕ) (_ : i < d), X.nonDegenerate i ⊆ A.obj _ := by
  constructor
  · rintro rfl
    simp
  · intro h
    rw [eq_top_iff_contains_nonDegenerate]
    intro i
    by_cases hi : i < d
    · exact h i hi
    · simp [X.nondegenerate_eq_bot_of_hasDimensionLT d i (by simpa using hi)]

end Subcomplex

lemma hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : ℕ)
    [Y.HasDimensionLT d] : X.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    rw [← degenerate_iff_of_isIso (toRangeSubcomplex f),
      Subcomplex.mem_degenerate_iff, Y.degenerate_eq_top_of_hasDimensionLT d n hn]
    simp

lemma Subcomplex.hasDimensionLT_of_le {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B)
    (d : ℕ) [HasDimensionLT B d] : HasDimensionLT A d := by
  have := mono_homOfLE h
  exact hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

lemma hasDimensionLT_of_epi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : ℕ)
    [X.HasDimensionLT d] : Y.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_map
    simp [X.degenerate_eq_top_of_hasDimensionLT d n hn]

lemma hasDimensionLT_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (d : ℕ) :
    X.HasDimensionLT d ↔ Y.HasDimensionLT d :=
  ⟨fun _ ↦ hasDimensionLT_of_epi e.hom d, fun _ ↦ hasDimensionLT_of_epi e.inv d⟩

instance {X Y : SSet.{u}} (f : X ⟶ Y) (d : ℕ) [X.HasDimensionLT d] :
    HasDimensionLT (Subcomplex.range f) d := by
  exact hasDimensionLT_of_epi (toRangeSubcomplex f) d

lemma hasDimensionLT_iSup_iff {X : SSet.{u}} {ι : Type*} (A : ι → X.Subcomplex) (d : ℕ) :
    HasDimensionLT (⨆ i, A i :) d ↔ ∀ i, HasDimensionLT (A i) d := by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop

lemma hasDimensionLT_iff_subcomplex_top (X : SSet.{u}) (d : ℕ) :
    X.HasDimensionLT d ↔ HasDimensionLT (⊤ : X.Subcomplex) d := by
  constructor
  · intro
    infer_instance
  · intro h
    simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff] at h
    simpa [hasDimensionLT_iff] using h

instance {X : SSet.{u}} (n : ℕ) : HasDimensionLT ((⊥ : X.Subcomplex)) n where
  degenerate_eq_top k hk := by
    ext ⟨x, hx⟩
    simp at hx

end SSet
