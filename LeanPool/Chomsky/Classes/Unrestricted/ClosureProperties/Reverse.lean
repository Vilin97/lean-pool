/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox
import LeanPool.Chomsky.Utilities.LanguageOperations
import LeanPool.Chomsky.Utilities.ListUtils

/-!
# Reverse

Closure of general-grammar languages under reversal.
-/

open scoped Chomsky

namespace Chomsky


variable {T : Type}

private def reversalGrule {N : Type} (r : Grule T N) : Grule T N :=
  Grule.mk r.inputR.reverse r.inputN r.inputL.reverse r.output.reverse

private lemma dual_of_reversalGrule {N : Type} (r : Grule T N) :
  reversalGrule (reversalGrule r) = r :=
by
  simp [reversalGrule, List.reverse_reverse]

private lemma reversal_grule_reversal_grule {N : Type} :
  @reversalGrule T N ∘ @reversalGrule T N = id :=
by
  ext
  apply dual_of_reversalGrule

private def reversalGrammar (g : Grammar T) : Grammar T :=
  Grammar.mk g.nt g.initial (g.rules.map reversalGrule)

private lemma dual_of_reversalGrammar (g : Grammar T) :
  reversalGrammar (reversalGrammar g) = g :=
by
  simp [reversalGrammar, reversal_grule_reversal_grule]

private lemma derives_reversed {g : Grammar T} {v : List (Symbol T g.nt)}
    (hgv : (reversalGrammar g).Derives [Symbol.nonterminal (reversalGrammar g).initial] v) :
  g.Derives [Symbol.nonterminal g.initial] v.reverse :=
by
  induction hgv with
  | refl =>
    change g.Derives _ (List.reverse [Symbol.nonterminal (reversalGrammar g).initial])
    rw [List.reverse_singleton]
    apply gr_deri_self
  | tail _ orig ih =>
    apply gr_deri_of_deri_tran ih
    rw [show (reversalGrammar g).Transforms = Grammar.Transforms (T := T)
      ⟨g.nt, g.initial, g.rules.map reversalGrule⟩ from rfl] at orig
    rcases orig with ⟨r, rin, x, y, bef, aft⟩
    rw [List.mem_map] at rin
    rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
    subst r_from_r₀
    use r₀, rin₀, y.reverse, x.reverse
    refine ⟨?_, ?_⟩ <;>
      · simp only [reversalGrule, *]
        simp [List.reverse_append, List.reverse_reverse, List.append_assoc]

private lemma reversed_word_in_original_language {g : Grammar T} {w : List T}
    (hwg : w ∈ (reversalGrammar g).language) :
  w.reverse ∈ g.language :=
by
  unfold Grammar.language at *
  have almost_done := derives_reversed hwg
  change g.Derives [Symbol.nonterminal g.initial] (w.reverse.map Symbol.terminal)
  rwa [List.map_reverse]


/-- The class of grammar-generated languages is closed under reversal. -/
theorem GG_of_reverse_GG (L : Language T) :
  Language.IsGG L → Language.IsGG L.reverse :=
by
  rintro ⟨g, rfl⟩
  use reversalGrammar g
  apply Set.eq_of_subset_of_subset ↓reversed_word_in_original_language
  intro w hwL
  change w.reverse ∈ g.language at hwL
  obtain ⟨g₀, pre_reversal⟩ : ∃ g₀ : Grammar T, g = reversalGrammar g₀ := by
    use reversalGrammar g
    rw [dual_of_reversalGrammar]
  rw [pre_reversal] at hwL ⊢
  have finished_up_to_reverses := reversed_word_in_original_language hwL
  rw [dual_of_reversalGrammar]
  rwa [List.reverse_reverse] at finished_up_to_reverses

end Chomsky
