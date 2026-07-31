/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.StandardSimplex

universe u

open Simplicial CategoryTheory

namespace SSet

variable (X : SSet.{u})

class IsFinite : Prop where
  finite : Finite (Σ (n : ℕ), X.nonDegenerate n)

attribute [instance] IsFinite.finite

instance [X.IsFinite] (n : ℕ) : Finite (X.nonDegenerate n) :=
  Finite.of_injective (fun x ↦ (⟨n, x⟩ : Σ (d : ℕ), X.nonDegenerate d))
    (fun _ _ ↦ by simp)

lemma isFinite_of_hasDimensionLT (d : ℕ) [X.HasDimensionLT d]
    (h : ∀ (i : ℕ) (_ : i < d), Finite (X.nonDegenerate i)) :
    X.IsFinite where
  finite := by
    have (i : Fin d) : Finite (X.nonDegenerate i) := h i.1 i.2
    apply Finite.of_surjective (α := Σ (i : Fin d), X.nonDegenerate i)
      (f := fun ⟨i, x⟩ ↦ ⟨i.1, x⟩)
    rintro ⟨j, ⟨x, hx⟩⟩
    by_cases hj : j < d
    · exact ⟨⟨⟨j, hj⟩, ⟨x, hx⟩⟩, rfl⟩
    · simp [X.nondegenerate_eq_bot_of_hasDimensionLT d j (by simpa using hj)] at hx

instance (n : ℕ) : (Δ[n] : SSet.{u}).IsFinite :=
  isFinite_of_hasDimensionLT _ (n + 1) (by infer_instance)

lemma hasDimensionLT_of_isFinite [X.IsFinite] :
    ∃ (d : ℕ), X.HasDimensionLT d := by
  have : Fintype (Σ (n : ℕ), X.nonDegenerate n) := Fintype.ofFinite _
  let φ : (Σ (n : ℕ), X.nonDegenerate n) → ℕ := Sigma.fst
  obtain ⟨d, hd⟩ : ∃ (d : ℕ), ∀ (s : ℕ) (_ : s ∈ Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      refine ⟨d + 1, ?_⟩
      rintro m hm
      have := Finset.le_max hm
      rw [hd, WithBot.coe_le_coe] at this
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [h]
      exact ⟨0, fun s hs ↦ by simp at hs⟩
  refine ⟨d, ⟨fun n hn ↦ ?_⟩⟩
  ext x
  simp only [mem_degenerate_iff_not_mem_nonDegenerate, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  intro hx
  have := hd (φ ⟨n, ⟨x, hx⟩⟩) (by simp)
  dsimp [φ] at this
  omega

instance [X.IsFinite] (n : SimplexCategoryᵒᵖ) : Finite (X.obj n) := by
  obtain ⟨n⟩ := n
  induction' n using SimplexCategory.rec with n
  let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
    X.nonDegenerate m.1) → X _⦋n⦌ := fun ⟨m, f, x⟩ ↦ X.map f.op x.1
  have hφ : Function.Surjective φ := fun x ↦ by
    obtain ⟨m, f, hf, y, rfl⟩ := X.exists_nonDegenerate x
    have := SimplexCategory.le_of_epi hf
    exact ⟨⟨⟨m, by omega⟩, f, y⟩, rfl⟩
  exact Finite.of_surjective _ hφ

instance [X.IsFinite] (A : X.Subcomplex) : IsFinite A := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_isFinite
  refine isFinite_of_hasDimensionLT _ d (fun i hi ↦ ?_)
  apply Finite.of_injective (f := fun a ↦ a.1.1)
  rintro ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ rfl
  rfl

variable {X}

lemma isFinite_of_mono {Y : SSet.{u}} [Y.IsFinite] (f : X ⟶ Y) [hf : Mono f] : X.IsFinite := by
  obtain ⟨d, _⟩ := Y.hasDimensionLT_of_isFinite
  have := hasDimensionLT_of_mono f d
  refine isFinite_of_hasDimensionLT _ d (fun i hi ↦ ?_)
  apply Finite.of_injective (f := fun a ↦ f.app _ a.1)
  rintro ⟨x, _⟩ ⟨y, _⟩ h
  obtain rfl : x = y := by
    rw [NatTrans.mono_iff_mono_app] at hf
    simp only [mono_iff_injective] at hf
    exact hf _ h
  rfl

lemma isFinite_of_epi {Y : SSet.{u}} [X.IsFinite] (f : X ⟶ Y) [hf : Epi f] : Y.IsFinite := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_isFinite
  have := hasDimensionLT_of_epi f d
  refine isFinite_of_hasDimensionLT _ d (fun i hi ↦ ?_)
  have : Finite (Y _⦋i⦌) := by
    rw [NatTrans.epi_iff_epi_app] at hf
    simp only [epi_iff_surjective] at hf
    exact Finite.of_surjective _ (hf _)
  infer_instance

lemma isFinite_of_iso {Y : SSet.{u}} (e : X ≅ Y) [X.IsFinite] : Y.IsFinite :=
  isFinite_of_mono e.inv

end SSet
