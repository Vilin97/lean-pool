/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharDecomp
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PermModule

/-!
# The Jacobi–Trudi virtual character as a signed sum of native characters

Every summand in the Jacobi–Trudi character formula is a colour-class
representation character, hence decomposes into native characters of
simple submodules.  Assembling these decompositions over the Leibniz
sum yields `jtChar μ` as a signed combination of native characters
with signs in `{±1}`.
-/

namespace RS

open Finset Equiv

open scoped Classical in
/-- **The Jacobi–Trudi character is a signed sum of native
characters**: each summand of the formula is a colour-class
character, which decomposes into simples. -/
theorem jtChar_eq_sum_sign_nChar (μ : YoungDiagram) :
    ∃ (J : Type) (_ : Fintype J) (ε : J → ℤ)
      (T : J → Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
        (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))),
      (∀ j, IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (T j)) ∧
      (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ π : Equiv.Perm (Fin μ.card),
        jtChar μ π = ∑ j, ((ε j : ℤ) : ℂ) * nChar (T j) π := by
  classical
  -- Step 1: For each σ, produce a decomposition of the jtChar summand
  -- into a sum of signed native characters.
  have hdecomp : ∀ σ : Equiv.Perm (Fin μ.rowLens.length),
      ∃ (m : ℕ) (S : Fin m → Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin
        μ.card)))
          (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))),
        (∀ i, IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (S i))
          ∧
        ∀ π, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i, 0 ≤ jtSigned μ σ i
            then (colourChar (jtComp μ σ) π : ℂ) else 0) =
          ∑ i : Fin m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * nChar (S i) π := by
    intro σ
    by_cases hp : ∀ i, 0 ≤ jtSigned μ σ i
    · -- Guard true: decompose the colour representation character
      obtain ⟨m, S, hSimp, hChar⟩ :=
        character_eq_sum_nChar (G := Equiv.Perm (Fin μ.card)) (colourRep
          (jtComp μ σ))
      refine ⟨m, S, hSimp, fun π => ?_⟩
      rw [ite_eq_left hp]
      -- colourRep_character converts representation character to colourChar
      have hconv : (colourChar (jtComp μ σ) π : ℂ) =
          ∑ i : Fin m, nChar (S i) π := by
        rw [← colourRep_character (jtComp μ σ) π]
        exact hChar π
      rw [hconv, Finset.mul_sum]
    · -- Guard false: empty family, both sides are zero
      exact ⟨0, Fin.elim0, fun i => i.elim0, fun π => by
        rw [ite_eq_right hp, mul_zero]; simp⟩
  -- Step 2: Extract the families via Classical.choose
  let dm : Equiv.Perm (Fin μ.rowLens.length) → ℕ :=
    fun σ => (hdecomp σ).choose
  let dS : (σ : Equiv.Perm (Fin μ.rowLens.length)) →
      Fin (dm σ) → Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
        (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) :=
    fun σ => (hdecomp σ).choose_spec.choose
  have hdS_simp : ∀ σ i,
      IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) (dS σ i) :=
    fun σ => (hdecomp σ).choose_spec.choose_spec.1
  have hdS_char : ∀ σ π,
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if ∀ i, 0 ≤ jtSigned μ σ i
          then (colourChar (jtComp μ σ) π : ℂ) else 0) =
        ∑ i : Fin (dm σ), ((Equiv.Perm.sign σ : ℤ) : ℂ) * nChar (dS σ i) π :=
    fun σ => (hdecomp σ).choose_spec.choose_spec.2
  -- Step 3: Build the sigma type J and the witnesses
  let J := Σ σ : Equiv.Perm (Fin μ.rowLens.length), Fin (dm σ)
  let ε : J → ℤ := fun j => (Equiv.Perm.sign j.1 : ℤ)
  let T : J → Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) :=
    fun j => dS j.1 j.2
  refine ⟨J, inferInstance, ε, T, ?_, ?_, ?_⟩
  · -- Simplicity
    intro ⟨σ, i⟩
    exact hdS_simp σ i
  · -- Sign values: (Perm.sign σ : ℤ) ∈ {1, -1}
    intro ⟨σ, _⟩
    change (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · left; exact congrArg Units.val h
    · right; exact congrArg Units.val h
  · -- Character identity
    intro π
    -- Unfold jtChar to the outer sum
    change jtChar μ π = ∑ j : J, ((ε j : ℤ) : ℂ) * nChar (T j) π
    -- Step 3a: rewrite each summand of jtChar using hdS_char
    have h1 : jtChar μ π =
        ∑ σ : Equiv.Perm (Fin μ.rowLens.length),
          ∑ i : Fin (dm σ),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) * nChar (dS σ i) π := by
      unfold jtChar
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact hdS_char σ π
    -- Step 3b: convert double sum to sigma sum
    rw [h1]
    rw [← Fintype.sum_sigma']

end RS
