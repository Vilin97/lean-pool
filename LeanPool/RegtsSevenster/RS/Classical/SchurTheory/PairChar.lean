/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourWeight

/-!
# The colour character of a pair

The colour character is multiplicative in the colour vector: the
character of a pair of colourings is the product of the two
characters at the same permutation.
-/

@[expose] public section

namespace RS

open Finset

open scoped Classical in
/-- **The colour character is multiplicative**: a product of two
characters counts the fixed pair-colourings with the two prescribed
margins. -/
theorem colourChar_mul {n k : ℕ} (α β : Fin k → ℕ) (π : Equiv.Perm (Fin n)) :
    colourChar α π * colourChar β π =
      (Finset.univ.filter (fun p : Fin n → Fin k × Fin k =>
        (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b) ∧
        p ∘ π = p)).card := by
  unfold colourChar
  rw [← card_product]
  apply card_bij (fun (gh : (Fin n → Fin k) × (Fin n → Fin k)) _ =>
    fun i => (gh.1 i, gh.2 i))
  · -- forward membership
    intro ⟨g, h⟩ hmem
    simp only [mem_filter, mem_univ, true_and, mem_product] at hmem ⊢
    refine ⟨hmem.1.1, hmem.2.1, funext fun i => ?_⟩
    exact Prod.ext (congrFun hmem.1.2 i) (congrFun hmem.2.2 i)
  · -- injectivity
    intro ⟨g₁, h₁⟩ _ ⟨g₂, h₂⟩ _ heq
    exact Prod.ext
      (funext fun i => congrArg Prod.fst (congrFun heq i))
      (funext fun i => congrArg Prod.snd (congrFun heq i))
  · -- surjectivity
    intro p hmem
    refine ⟨(fun i => (p i).1, fun i => (p i).2), ?_, funext fun i
      => Prod.mk.eta⟩
    simp only [mem_filter, mem_univ, true_and, mem_product] at hmem ⊢
    exact ⟨⟨hmem.1, funext fun i => congrArg Prod.fst (congrFun hmem.2.2 i)⟩,
           ⟨hmem.2.1, funext fun i => congrArg Prod.snd (congrFun hmem.2.2 i)⟩⟩

end RS
