/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Fin

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.EdgePatterns
import LeanPool.TwoColoringOneRound.LowerBound.LocalRule

/-!
Small “sanity checks” intended to validate that the Lean definitions in `Defs.lean` match the
intended combinatorial model.

This file proves, in a fully kernel-checked way, that for `n = 5` there is an explicit coloring
with monochromatic edge fraction exactly `1/5`.
-/

namespace Distributed2Coloring.LowerBound


namespace Sanity

open Distributed2Coloring.LowerBound
open LocalRule

/-!
## `n = 5`

We split the symbols into `{0,1}` (“small”) and `{2,3,4}` (“big”), round to a bit, and apply `g`.
This yields `24` monochromatic edges out of `120`, hence `monoFraction = 1/5`.
-/

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev two5 : Sym 5 := ⟨2, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small5 : Type := Set.Iio two5
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big5 : Type := Set.Ici two5

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def round5 (a : Sym 5) : Bool :=
  decide (two5 ≤ a)

@[simp] lemma round5_eq_true {a : Sym 5} : round5 a = true ↔ two5 ≤ a := by
  simp [round5]

@[simp] lemma round5_eq_false {a : Sym 5} : round5 a = false ↔ a < two5 := by
  simp [round5, not_le]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev f5 : Coloring 5 :=
  fun v => g (round5 (Vertex.a v)) (round5 (Vertex.b v)) (round5 (Vertex.c v))

lemma card_Small5 : Fintype.card Small5 = 2 := by
  norm_num [Small5, two5]

lemma card_Big5 : Fintype.card Big5 = 3 := by
  norm_num [Big5, two5]

private lemma not_all_small (e : Edge 5) : ¬ (∀ i : Fin 4, e.1 i < two5) := by
  classical
  intro hall
  let emb : Fin 4 ↪ Small5 :=
    { toFun := fun i => ⟨e.1 i, hall i⟩
      inj' := by
        intro i j hij
        apply e.2
        exact congrArg Subtype.val hij }
  have hle : Fintype.card (Fin 4) ≤ Fintype.card Small5 :=
    Fintype.card_le_of_embedding emb
  -- Turn the card inequality into a numeral contradiction.
  simp only [Fintype.card_fin, card_Small5] at hle
  exact (by decide : ¬(4 : Nat) ≤ 2) hle

private lemma not_all_big (e : Edge 5) : ¬ (∀ i : Fin 4, two5 ≤ e.1 i) := by
  classical
  intro hall
  let emb : Fin 4 ↪ Big5 :=
    { toFun := fun i => ⟨e.1 i, hall i⟩
      inj' := by
        intro i j hij
        apply e.2
        exact congrArg Subtype.val hij }
  have hle : Fintype.card (Fin 4) ≤ Fintype.card Big5 :=
    Fintype.card_le_of_embedding emb
  simp only [Fintype.card_fin, card_Big5] at hle
  exact (by decide : ¬(4 : Nat) ≤ 3) hle

private abbrev pat0000 : Edge 5 → Prop := EdgePatterns.Pat0000 (two := two5)
private abbrev pat1111 : Edge 5 → Prop := EdgePatterns.Pat1111 (two := two5)
private abbrev pat1001 : Edge 5 → Prop := EdgePatterns.Pat1001 (two := two5)
private abbrev pat0110 : Edge 5 → Prop := EdgePatterns.Pat0110 (two := two5)

private lemma monochromatic_iff_pat (e : Edge 5) :
    Edge.monochromatic f5 e ↔ pat1001 e ∨ pat0110 e := by
  have hpatterns :
      Edge.monochromatic f5 e ↔ pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e := by
    simpa [f5, pat0000, pat1111, pat1001, pat0110] using
      (LocalRule.monochromatic_iff_patterns (round := round5) (two := two5)
        (hr_true := fun a => round5_eq_true (a := a))
        (hr_false := fun a => round5_eq_false (a := a))
        (e := e))
  constructor
  · intro hmono
    rcases hpatterns.mp hmono with hall0 | hall1 | hall2 | hall3
    · -- all bits `false` is impossible for an injective 4-tuple into `Small5` (only 2 elements)
      have hall : ∀ i : Fin 4, e.1 i < two5 := by
        intro i
        fin_cases i
        · exact hall0.1
        · exact hall0.2.1
        · exact hall0.2.2.1
        · exact hall0.2.2.2
      exact False.elim (not_all_small (e := e) hall)
    · -- all bits `true` is impossible for an injective 4-tuple into `Big5` (only 3 elements)
      have hall : ∀ i : Fin 4, two5 ≤ e.1 i := by
        intro i
        fin_cases i
        · exact hall1.1
        · exact hall1.2.1
        · exact hall1.2.2.1
        · exact hall1.2.2.2
      exact False.elim (not_all_big (e := e) hall)
    · exact Or.inl hall2
    · exact Or.inr hall3
  · rintro (h1001 | h0110)
    · exact hpatterns.mpr (Or.inr <| Or.inr <| Or.inl h1001)
    · exact hpatterns.mpr (Or.inr <| Or.inr <| Or.inr h0110)
private lemma card_pat1001 : Fintype.card {e : Edge 5 // pat1001 e} = 12 := by
  classical
  have h :
      Fintype.card {e : Edge 5 // pat1001 e}
        = (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 := by
    exact EdgePatterns.card_pat1001 (n := 5) (two := two5)
  have hnum : (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 = 12 := by
    rw [card_Big5, card_Small5]
    decide
  exact h.trans hnum

private lemma card_pat0110 : Fintype.card {e : Edge 5 // pat0110 e} = 12 := by
  classical
  have h :
      Fintype.card {e : Edge 5 // pat0110 e}
        = (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 := by
    exact EdgePatterns.card_pat0110 (n := 5) (two := two5)
  have hnum : (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 = 12 := by
    rw [card_Big5, card_Small5]
    decide
  exact h.trans hnum

theorem edgeCount_5 : edgeCount 5 = 120 := by
  classical
  -- `Edge 5` is equivalent to the type of embeddings `Fin 4 ↪ Fin 5`.
  have hcongr : edgeCount 5 = Fintype.card (Fin 4 ↪ Sym 5) := by
    have : Fintype.card (Edge 5) = Fintype.card (Fin 4 ↪ Sym 5) :=
      Fintype.card_congr
        { toFun := fun e => ⟨e.1, e.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro e; apply Subtype.ext; funext i; rfl
          right_inv := by intro x; ext i; rfl }
    simpa [edgeCount] using this
  have : edgeCount 5 = (5 : Nat).descFactorial 4 := by
    simp [hcongr, Sym, Fintype.card_embedding_eq]
  simpa using this.trans (by decide : (5 : Nat).descFactorial 4 = 120)

theorem monoCount_f5 : monoCount f5 = 24 := by
  classical
  have hsub :
      monoCount f5 = Fintype.card {e : Edge 5 // Edge.monochromatic f5 e} := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge 5) (p := Edge.monochromatic f5)).symm
  have hmono :
      Fintype.card {e : Edge 5 // Edge.monochromatic f5 e}
        = Fintype.card {e : Edge 5 // pat1001 e ∨ pat0110 e} := by
    exact Fintype.card_congr <|
      Equiv.subtypeEquivRight (fun e => monochromatic_iff_pat (e := e))
  have hdisj : Disjoint pat1001 pat0110 := by
    intro r hr hs e hre
    exact (not_lt_of_ge (hr e hre).1) (hs e hre).1
  calc
    monoCount f5
        = Fintype.card {e : Edge 5 // Edge.monochromatic f5 e} := hsub
    _ = Fintype.card {e : Edge 5 // pat1001 e ∨ pat0110 e} := hmono
    _ = Fintype.card {e : Edge 5 // pat1001 e} + Fintype.card {e : Edge 5 // pat0110 e} := by
          simpa using
            (Fintype.card_subtype_or_disjoint (p := pat1001) (q := pat0110) hdisj)
    _ = 12 + 12 := by simp [card_pat1001, card_pat0110]
    _ = 24 := by decide

theorem monoFraction_f5 : monoFraction f5 = (1 : ℚ) / 5 := by
  simp [monoFraction, monoCount_f5, edgeCount_5]
  norm_num

end Sanity

end Distributed2Coloring.LowerBound
