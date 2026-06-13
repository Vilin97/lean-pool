/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Inclusion
import LeanPool.Chomsky.Classes.Unrestricted.ClosureProperties.Union

/-!
# Union

Closure of context-free languages under union.
-/

open scoped Chomsky

namespace Chomsky

variable {T : Type}

private def liftCFR₁ {N₁ : Type} (N₂ : Type) (r : N₁ × List (Symbol T N₁)) :
  Option (N₁ ⊕ N₂) × List (Symbol T (Option (N₁ ⊕ N₂))) :=
⟨some ◄r.fst, liftString (Option.some ∘ Sum.inl) r.snd⟩

private def liftCFR₂ (N₁ : Type) {N₂ : Type} (r : N₂ × List (Symbol T N₂)) :
  Option (N₁ ⊕ N₂) × List (Symbol T (Option (N₁ ⊕ N₂))) :=
⟨some ▶r.fst, liftString (Option.some ∘ Sum.inr) r.snd⟩

private def unionCFG (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (Option (g₁.nt ⊕ g₂.nt)) none (
    (none, [Symbol.nonterminal (some ◄g₁.initial)]) :: (
    (none, [Symbol.nonterminal (some ▶g₂.initial)]) :: (
    g₁.rules.map (liftCFR₁ g₂.nt) ++
    g₂.rules.map (liftCFR₂ g₁.nt))))

private lemma unionCFG_language_eq_unionGrammar_language (g₁ g₂ : CFG T) :
  (unionCFG g₁ g₂).language = (unionGrammar g₁.toGeneral g₂.toGeneral).language := by
  rw [CFG.language_eq_toGeneral_language]
  simp only [unionCFG, unionGrammar, CFG.toGeneral, List.map_cons, List.map_append, List.map_map]
  rfl

theorem CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
  Language.IsCF L₁ ∧ Language.IsCF L₂ → Language.IsCF (L₁ + L₂) := by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  rw [g₁.language_eq_toGeneral_language]
  rw [g₂.language_eq_toGeneral_language]
  use unionCFG g₁ g₂
  rw [unionCFG_language_eq_unionGrammar_language]
  exact Set.eq_of_subset_of_subset ↓in_L₁_or_L₂_of_in_union
    ↓(·.casesOn in_union_of_in_L₁ in_union_of_in_L₂)

end Chomsky
