/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Functions

/-!
# LeanPool.ZFLean.Embeddings

Imported Lean Pool material for `LeanPool.ZFLean.Embeddings`.
-/

namespace ZFSet
/-- Imported ZFLean declaration. -/
def hasEmbedding (A B : ZFSet) : Prop :=
  ∃ (f : ZFSet) (hf : A.IsFunc B f), IsInjective f
/-- Imported ZFLean declaration. -/
infix:50 " ↪ᶻ " => hasEmbedding
/-- Imported ZFLean declaration. -/
infix:50 " ↩ᶻ " => fun A B ↦ B ↪ᶻ A

theorem embedding_symm {A B : ZFSet} : A ↪ᶻ B ↔ B ↩ᶻ A := id Iff.rfl

theorem embedding_singleton {x y : ZFSet} : {x} ↪ᶻ {y} := by
  use {x.pair y}, ?_
  · intro a b c ha hb hc ac bc
    simp_all
  · and_intros
    · intro z hz
      simp_all
    · simp_all

theorem embedding_pair (a b c d : ZFSet) (hab_cd : a = b ↔ c = d) : {a, b} ↪ᶻ {c, d} := by
  use {a.pair c, b.pair d}, ?_
  · intro x y z hx hy hz xy yz
    rw [mem_pair] at hx hy hz xy yz
    simp_rw [pair_inj] at xy yz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> try rfl
    · rcases xy with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> rcases yz with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> try rfl
      rw [hab_cd]
    · rcases xy with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> rcases yz with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> try rfl
      rw [hab_cd]
    · rcases xy with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> rcases yz with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> try rfl
      simp_all
    · rcases xy with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> rcases yz with ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;> try rfl
      simp_all
  · and_intros
    · intro z hz
      rw [mem_pair] at hz
      rcases hz with rfl | rfl
      · simp_all
      · simp_all
    · intro z hz
      rw [mem_pair] at hz
      rcases hz with rfl | rfl
      · by_cases hc : c = d
        · simp_all
        · simp_all
      · by_cases hc : c = d
        · simp_all
        · simp only [hc, iff_false] at hab_cd
          use d
          and_intros
          · simp_all
          · intro y hy
            rw [mem_pair, pair_inj] at hy
            rcases hy with ⟨rfl, _⟩ | eq
            · nomatch hab_cd rfl
            · simp_all

theorem embedding_refl (A : ZFSet) : A ↪ᶻ A := by
  use A.Id, Id.IsFunc
  intro x y z hx hy hz xz yz
  rw [pair_mem_Id_iff] at xz yz
  · simp_all
  · exact hy
  · exact hx

theorem embedding_trans {A B C : ZFSet} (hAB : A ↪ᶻ B) (hBC : B ↪ᶻ C) : A ↪ᶻ C := by
  obtain ⟨f, hf, injf⟩ := hAB
  obtain ⟨g, hg, injg⟩ := hBC
  use composition g f A B C, IsFunc_of_composition_IsFunc hg hf
  intro x y z hx hy hz xz yz
  simp only [mem_composition, pair_inj, existsAndEq, and_true,
    exists_and_left, exists_eq_left'] at xz yz
  obtain ⟨xA, zC, w, wB, xw, wz⟩ := xz
  obtain ⟨-, -, w', w'B, xw', w'z⟩ := yz
  obtain rfl := injg _ _ _ wB w'B hz wz w'z
  obtain rfl := injf _ _ _ hx hy wB xw xw'
  rfl

end ZFSet
