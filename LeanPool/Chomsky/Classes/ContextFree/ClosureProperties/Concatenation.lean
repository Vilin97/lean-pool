/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Inclusion
import LeanPool.Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation

/-!
# Concatenation

Closure of context-free languages under concatenation.
-/

open scoped Chomsky

namespace Chomsky

variable {T : Type}

private def wrapCFR₁ {N₁ : Type} (N₂ : Type) (r : N₁ × List (Symbol T N₁)) :
  nnn T N₁ N₂ × List (nst T N₁ N₂) :=
⟨◄(some ◄r.fst), r.snd.map (wrapSymbol₁ N₂)⟩

private def wrapCFR₂ (N₁ : Type) {N₂ : Type} (r : N₂ × List (Symbol T N₂)) :
  nnn T N₁ N₂ × List (nst T N₁ N₂) :=
⟨◄(some ▶r.fst), r.snd.map (wrapSymbol₂ N₁)⟩

private def CFG.terminalsRules₁ (g : CFG T) (N₂ : Type) :
  List (nnn T g.nt N₂ × List (nst T g.nt N₂)) :=
(allUsedTerminals g.toGeneral).map (fun t : T => ⟨▶◄t, [Symbol.terminal t]⟩)

private def CFG.terminalsRules₂ (g : CFG T) (N₁ : Type) :
  List (nnn T N₁ g.nt × List (nst T N₁ g.nt)) :=
(allUsedTerminals g.toGeneral).map (fun t : T => ⟨▶▶t, [Symbol.terminal t]⟩)

private def bigCFG (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (nnn T g₁.nt g₂.nt) ◄none (
    ⟨◄none, [
      Symbol.nonterminal ◄(some ◄g₁.initial),
      Symbol.nonterminal ◄(some ▶g₂.initial)]
    ⟩ :: ((
      g₁.rules.map (wrapCFR₁ g₂.nt) ++
      g₂.rules.map (wrapCFR₂ g₁.nt)
    ) ++ (
      g₁.terminalsRules₁ g₂.nt ++
      g₂.terminalsRules₂ g₁.nt)))

private lemma bigCFG_language_eq_bigGrammar_language (g₁ g₂ : CFG T) :
  (bigCFG g₁ g₂).language = (bigGrammar g₁.toGeneral g₂.toGeneral).language :=
by
  rw [CFG.language_eq_toGeneral_language]
  apply congr_arg
  dsimp only [bigCFG, bigGrammar, CFG.toGeneral, List.map_cons]
  congr 2
  simp only [List.map_append, List.map_map]
  congr 2
  · simp only [rulesForTerminals₁, CFG.terminalsRules₁, List.map_map]
    rfl
  · simp only [rulesForTerminals₂, CFG.terminalsRules₂, List.map_map]
    rfl

/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : Language T) (L₂ : Language T) :
  Language.IsCF L₁ ∧ Language.IsCF L₂ → Language.IsCF (L₁ * L₂) :=
by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  rw [g₁.language_eq_toGeneral_language]
  rw [g₂.language_eq_toGeneral_language]
  use bigCFG g₁ g₂
  rw [bigCFG_language_eq_bigGrammar_language]
  exact Set.eq_of_subset_of_subset ↓in_concatenated_of_in_big ↓in_big_of_in_concatenated

end Chomsky
