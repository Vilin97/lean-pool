/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Toolbox
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox

variable {T : Type}

def CFG.toGeneral (g : CFG T) : Grammar T :=
  Grammar.mk g.nt g.initial (g.rules.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd))

private lemma CFG.tran_iff_toGeneral_tran (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) :
  g.Transforms w₁ w₂ ↔ g.toGeneral.Transforms w₁ w₂ :=
by
  constructor <;> intro ⟨r, rin, u, v, bef, aft⟩
  · use ⟨[], r.fst, [], r.snd⟩, (by erw [List.mem_map]; use r), u, v
    simp [bef, aft]
  · erw [List.mem_map] at rin
    obtain ⟨r₀, hgr₀, hrr₀⟩ := rin
    use r₀, hgr₀, u, v
    rw [←hrr₀] at bef aft
    rw [bef, aft]
    simp

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
  L.IsCF → L.IsGG :=
by
  rintro ⟨g, rfl⟩
  exact ⟨g.toGeneral, g.language_eq_toGeneral_language.symm⟩
