/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Toolbox
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox

/-!
# Inclusion

Context-free languages are included in the class of general-grammar languages.
-/

namespace Chomsky

variable {T : Type}

/-- The general grammar corresponding to a context-free grammar. -/
def CFG.toGeneral (g : CFG T) : Grammar T :=
  Grammar.mk g.nt g.initial
    (g.rules.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd))

private lemma CFG.tran_iff_toGeneral_tran (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) :
  g.Transforms w₁ w₂ ↔ g.toGeneral.Transforms w₁ w₂ :=
by
  have key : g.toGeneral.Transforms w₁ w₂ ↔
      ∃ rr : Grule T g.nt, rr ∈ g.toGeneral.rules ∧ ∃ uu vv,
        w₁ = uu ++ rr.inputL ++ [Symbol.nonterminal rr.inputN] ++ rr.inputR ++ vv ∧
          w₂ = uu ++ rr.output ++ vv := Iff.rfl
  rw [key]
  constructor
  · intro ⟨r, rin, u, v, bef, aft⟩
    exact ⟨Grule.mk [] r.fst [] r.snd, List.mem_map.mpr ⟨r, rin, rfl⟩, u, v,
      by rw [bef]; simp, by rw [aft]⟩
  · intro ⟨r, rin, u, v, bef, aft⟩
    obtain ⟨r₀, hgr₀, hrr₀⟩ := List.mem_map.mp rin
    refine ⟨r₀, hgr₀, u, v, ?_, ?_⟩
    · rw [bef, ← hrr₀]; simp
    · rw [aft, ← hrr₀]

private lemma CFG.deri_iff_toGeneral_deri (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) :
  g.Derives w₁ w₂ ↔ g.toGeneral.Derives w₁ w₂ :=
by
  constructor <;> intro hgww
  · induction hgww with
    | refl => apply gr_deri_self
    | tail _ hg ih =>
      apply gr_deri_of_deri_tran ih
      rwa [CFG.tran_iff_toGeneral_tran] at hg
  · induction hgww with
    | refl => apply cf_deri_self
    | tail _ hg ih =>
      apply cf_deri_of_deri_tran ih
      rwa [←CFG.tran_iff_toGeneral_tran] at hg

lemma CFG.language_eq_toGeneral_language (g : CFG T) :
  g.language = g.toGeneral.language :=
by
  rw [Language.ext_iff]
  intro
  apply g.deri_iff_toGeneral_deri

theorem CF_subclass_GG (L : Language T) :
  Language.IsCF L → Language.IsGG L :=
by
  rintro ⟨g, rfl⟩
  exact ⟨g.toGeneral, g.language_eq_toGeneral_language.symm⟩

end Chomsky
