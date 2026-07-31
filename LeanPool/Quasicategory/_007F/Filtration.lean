/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory._007F.Basic
import LeanPool.Quasicategory.Lex

namespace SSet

open CategoryTheory Simplicial MonoidalCategory SSet Subcomplex

variable {n : ℕ}

namespace σ

noncomputable
def filtration (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  ∂Δ[n + 1].unionProd Λ[2, 1] ⊔ (⨆ (j) (_ : j ≤ i), σ.subcomplex j)

lemma filtration_bot :
    filtration ⊥ = ∂Δ[n + 1].unionProd Λ[2, 1] ⊔ σ.subcomplex ⊥ := by
  simp [σ.subcomplex, filtration]

open Sigma.Lex in
lemma filtration_succ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    filtration (succ i) =
      filtration i ⊔ σ.subcomplex (succ i) := by
  simp only [filtration]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left) (iSup₂_le fun i' hi' ↦ ?_)
    obtain hi' | rfl := lt_or_eq_of_le hi'
    · exact
        le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le i' (Order.le_of_lt_succ hi') le_rfl))
    · exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact
      sup_le le_sup_left
        (iSup₂_le fun i' hi' ↦
          le_sup_of_le_right (le_iSup₂_of_le i' (hi'.trans (Sigma.Lex.le_succ i)) le_rfl))
    · exact
      le_sup_of_le_right
        (le_iSup₂_of_le (Sigma.Lex.succ i) (le_refl (Sigma.Lex.succ i)) fun i_1 ⦃a⦄ a ↦ a)

lemma filtration_monotone : Monotone (filtration (n := n)) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))

end σ

namespace τ

noncomputable
def filtration (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  (σ.filtration ⊤) ⊔ (⨆ (j) (_ : j ≤ i), τ.subcomplex j)

lemma filtration_bot :
    filtration (⊥ : Σₗ (b : Fin (n + 2)), Fin b.succ) = σ.filtration ⊤ ⊔ τ.subcomplex ⊥ := by
  simp [filtration, σ.filtration]

open Sigma.Lex in
lemma filtration_succ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    filtration (succ i) =
      filtration i ⊔ τ.subcomplex (succ i) := by
  simp only [filtration]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left) (iSup₂_le fun i' hi' ↦ ?_)
    obtain hi' | rfl := lt_or_eq_of_le hi'
    · exact
        le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le i' (Order.le_of_lt_succ hi') le_rfl))
    · exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact
      sup_le le_sup_left
        (iSup₂_le fun i' hi' ↦
          le_sup_of_le_right (le_iSup₂_of_le i' (hi'.trans (Sigma.Lex.le_succ i)) le_rfl))
    · exact
      le_sup_of_le_right
        (le_iSup₂_of_le (Sigma.Lex.succ i) (le_refl (Sigma.Lex.succ i)) fun i_1 ⦃a⦄ a ↦ a)

lemma filtration_last :
    filtration (⊤ : Σₗ (b : Fin (n + 2)), Fin b.succ) = ⊤ := by
  dsimp [filtration]
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := τ.nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : τ.simplex i = x := congrArg Subtype.val hi
  rw [← Subcomplex.ofSimplex_le_iff]
  exact le_sup_of_le_right (le_iSup₂_of_le i le_top le_rfl)

lemma filtration_monotone : Monotone (filtration (n := n)) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))

end τ
