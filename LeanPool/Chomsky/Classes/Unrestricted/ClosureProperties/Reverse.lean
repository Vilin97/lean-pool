/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox
import LeanPool.Chomsky.Utilities.LanguageOperations
import LeanPool.Chomsky.Utilities.ListUtils


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
  induction' hgv with u w _ orig ih
  · rw [List.reverse_singleton]
    apply gr_deri_self
  apply gr_deri_of_deri_tran ih
  rcases orig with ⟨r, rin, x, y, bef, aft⟩
  change r ∈ g.rules.map _ at rin
  rw [List.mem_map] at rin
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
  use r₀, rin₀, y.reverse, x.reverse
  constructor
  · have rid₁ : r₀.inputL = r.inputR.reverse
    · rw [←r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    have rid₂ : [Symbol.nonterminal r₀.inputN] = [Symbol.nonterminal r.inputN].reverse
    · rewrite [←r_from_r₀, @List.reverse_singleton]
      rfl
    have rid₃ : r₀.inputR = r.inputL.reverse
    · rw [←r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    rw [rid₁, rid₂, rid₃, ←List.reverse_append_append, ←List.reverse_append_append, ←List.append_assoc, ←List.append_assoc]
    congr
  · have snd_from_r : r₀.output = r.output.reverse
    · rw [←r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    rw [snd_from_r, ←List.reverse_append_append]
    exact congr_arg List.reverse aft

private lemma reversed_word_in_original_language {g : Grammar T} {w : List T}
    (hwg : w ∈ (reversalGrammar g).language) :
  w.reverse ∈ g.language :=
by
  unfold Grammar.language at *
  have almost_done := derives_reversed hwg
  rwa [←List.map_reverse] at almost_done


/-- The class of grammar-generated languages is closed under reversal. -/
theorem GG_of_reverse_GG (L : Language T) :
  L.IsGG → L.reverse.IsGG :=
by
  rintro ⟨g, rfl⟩
  use reversalGrammar g
  apply Set.eq_of_subset_of_subset ↓reversed_word_in_original_language
  intro w hwL
  change w.reverse ∈ g.language at hwL
  obtain ⟨g₀, pre_reversal⟩ : ∃ g₀ : Grammar T, g = reversalGrammar g₀
  · use reversalGrammar g
    rw [dual_of_reversalGrammar]
  rw [pre_reversal] at hwL ⊢
  have finished_up_to_reverses := reversed_word_in_original_language hwL
  rw [dual_of_reversalGrammar]
  rwa [List.reverse_reverse] at finished_up_to_reverses

