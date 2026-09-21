/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTChar

/-!
# Class-function properties of the colour and Jacobi–Trudi
characters

`colourChar α` and `jtChar μ` are invariant under conjugation, and
under inversion (a permutation is conjugate to its inverse, having
the same cycle type).
-/

namespace RS

open Finset Equiv

variable {n N : ℕ}

/-- Fibre sizes are invariant under precomposition with a
permutation. -/
theorem fibreCard_comp_perm (g : Fin n → Fin N)
    (τ : Equiv.Perm (Fin n)) (j : Fin N) :
    fibreCard (g ∘ τ) j = fibreCard g j := by
  rw [fibreCard_eq_count, fibreCard_eq_count, content_comp_perm]

open scoped Classical in
/-- **The colour character is a class function.** -/
theorem colourChar_conj (α : Fin N → ℕ)
    (π τ : Equiv.Perm (Fin n)) :
    colourChar α (τ * π * τ⁻¹) = colourChar α π := by
  rw [colourChar, colourChar]
  refine Finset.card_bij'
    (fun g _ => g ∘ ⇑τ) (fun g _ => g ∘ ⇑τ⁻¹) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      at hg ⊢
    obtain ⟨hcls, hfix⟩ := hg
    constructor
    · intro j
      rw [fibreCard_comp_perm]
      exact hcls j
    · funext i
      have h1 := congrFun hfix (τ i)
      simp only [Function.comp_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h1
      simp only [Function.comp_apply]
      exact h1
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      at hg ⊢
    obtain ⟨hcls, hfix⟩ := hg
    constructor
    · intro j
      rw [fibreCard_comp_perm]
      exact hcls j
    · funext i
      have h1 := congrFun hfix (τ⁻¹ i)
      simp only [Function.comp_apply] at h1
      simp only [Function.comp_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      exact h1
  · intro g _
    funext i
    simp [Equiv.Perm.inv_def]
  · intro g _
    funext i
    simp [Equiv.Perm.inv_def]

open scoped Classical in
/-- The colour character is invariant under inversion. -/
theorem colourChar_inv (α : Fin N → ℕ) (π : Equiv.Perm (Fin n)) :
    colourChar α π⁻¹ = colourChar α π := by
  have hconj : IsConj π π⁻¹ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq]
    exact (Equiv.Perm.cycleType_inv π).symm
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  rw [← hτ, colourChar_conj]

open scoped Classical in
/-- The Jacobi–Trudi character is invariant under inversion. -/
theorem jtChar_inv (μ : YoungDiagram)
    (π : Equiv.Perm (Fin μ.card)) :
    jtChar μ π⁻¹ = jtChar μ π := by
  rw [jtChar, jtChar]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  by_cases hp : ∀ i, 0 ≤ jtSigned μ σ i
  · rw [if_pos hp, if_pos hp, colourChar_inv]
  · rw [if_neg hp, if_neg hp]

end RS
