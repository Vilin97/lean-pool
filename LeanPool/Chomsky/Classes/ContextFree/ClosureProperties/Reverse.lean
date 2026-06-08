/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Toolbox
import LeanPool.Chomsky.Utilities.LanguageOperations
import LeanPool.Chomsky.Utilities.ListUtils

/-!
# Reverse

Closure of context-free languages under reversal.
-/

open scoped Chomsky

namespace Chomsky


variable {T : Type}

private def CFG.reverse (g : CFG T) : CFG T :=
  CFG.mk
    g.nt
    g.initial
    (g.rules.map (fun r : g.nt × List (Symbol T g.nt) => (r.fst, r.snd.reverse)))

private lemma dual_of_reversalGrammar (g : CFG T) :
  g.reverse.reverse = g :=
by
  obtain ⟨_, _, _⟩ := g
  unfold CFG.reverse
  aesop

private lemma derives_reversed {g : CFG T} {v : List (Symbol T g.nt)}
    (hgv : g.reverse.Derives [Symbol.nonterminal g.reverse.initial] v) :
  g.Derives [Symbol.nonterminal g.initial] v.reverse :=
by
  induction hgv with
  | refl =>
      change g.Derives _ (List.reverse [Symbol.nonterminal g.reverse.initial])
      rw [List.reverse_singleton]
      apply cf_deri_self
  | tail _ orig ih =>
      apply cf_deri_of_deri_tran ih
      rw [show g.reverse.Transforms = CFG.Transforms (T := T)
        ⟨g.nt, g.initial, g.rules.map (fun r : g.nt × List (Symbol T g.nt) =>
          (r.fst, r.snd.reverse))⟩ from rfl] at orig
      rcases orig with ⟨r, rin, x, y, bef, aft⟩
      rw [List.mem_map] at rin
      rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
      subst r_from_r₀
      refine ⟨r₀, rin₀, y.reverse, x.reverse, ?_, ?_⟩
      · rw [bef]
        simp [List.reverse_append, List.append_assoc]
      · rw [aft]
        simp [List.reverse_append, List.append_assoc, List.reverse_reverse]

private lemma reversed_word_in_original_language {g : CFG T} {w : List T}
    (hgw : w ∈ g.reverse.language) :
  w.reverse ∈ g.language :=
by
  unfold CFG.language at *
  change g.Derives [Symbol.nonterminal g.initial] (w.reverse.map Symbol.terminal)
  rw [List.map_reverse]
  exact derives_reversed hgw

/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : Language T) :
  Language.IsCF L → Language.IsCF L.reverse :=
by
  rintro ⟨g, rfl⟩
  use g.reverse
  apply Set.eq_of_subset_of_subset ↓reversed_word_in_original_language
  intro w hwL
  have pre_reversal : ∃ g₀ : CFG T, g = g₀.reverse := by
    use g.reverse
    rw [dual_of_reversalGrammar]
  obtain ⟨g₀, pre_rev⟩ := pre_reversal
  rw [pre_rev] at hwL ⊢
  have finished_modulo_reverses := reversed_word_in_original_language hwL
  rw [dual_of_reversalGrammar]
  rw [List.reverse_reverse] at finished_modulo_reverses
  exact finished_modulo_reverses

end Chomsky
