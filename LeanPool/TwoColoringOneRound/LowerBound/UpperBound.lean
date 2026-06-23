/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.EdgePatterns
import LeanPool.TwoColoringOneRound.LowerBound.LocalRule

/-!
## Upper bounds (explicit colorings)

The main formalized result of this project is a *lower bound*: every coloring has at least
`23.879%` monochromatic edges when `n = 1_000_000`.

This file provides small explicit *upper bounds* (i.e. constructions of colorings with relatively
few monochromatic edges), to complement the lower bounds.

The coloring used here is the simple rounding-based local rule from the report:

* round each symbol `a : Fin n` to a bit `r(a)` depending on whether `a < n/2`;
* apply a fixed local rule `g` to the rounded bits.
-/

namespace Distributed2Coloring.LowerBound


namespace UpperBound

open scoped BigOperators
open LocalRule

/-- The cardinality of a 4-way disjunction subtype is bounded by the sum of the parts. -/
private lemma card_or4_le {α : Type*} [Fintype α] (p q r s : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s] :
    Fintype.card {e : α // p e ∨ q e ∨ r e ∨ s e} ≤
      Fintype.card {e : α // p e} +
        (Fintype.card {e : α // q e} +
          (Fintype.card {e : α // r e} + Fintype.card {e : α // s e})) := by
  refine le_trans (Fintype.card_subtype_or (p := p) (q := fun e => q e ∨ r e ∨ s e)) ?_
  refine Nat.add_le_add_left ?_ _
  refine le_trans (Fintype.card_subtype_or (p := q) (q := fun e => r e ∨ s e)) ?_
  exact Nat.add_le_add_left (Fintype.card_subtype_or (p := r) (q := s)) _

/-!
### `n = 9`

We use the rounding threshold `4`, so `Small = {0,1,2,3}` and `Big = {4,5,6,7,8}`.
The resulting coloring has monochromatic fraction exactly `13/63 ≈ 20.63%`.
-/

namespace N9

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := 9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Sym9 := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Coloring9 := Coloring n

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev two9 : Sym9 := ⟨4, by decide⟩
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small9 : Type := Set.Iio two9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big9 : Type := Set.Ici two9

lemma card_Small9 : Fintype.card Small9 = 4 := by simp [Small9, two9]

lemma card_Big9 : Fintype.card Big9 = 5 := by
  -- `simp` reduces the card to `n - 4`, then `decide` finishes.
  simpa [Big9, two9] using (by decide : (n - 4 : Nat) = 5)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def round9 (a : Sym9) : Bool :=
  decide (two9 ≤ a)

@[simp] lemma round9_eq_true {a : Sym9} : round9 a = true ↔ two9 ≤ a := by simp [round9]

@[simp] lemma round9_eq_false {a : Sym9} : round9 a = false ↔ a < two9 := by simp [round9, not_le]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev f9 : Coloring9 :=
  fun v => g (round9 (Vertex.a v)) (round9 (Vertex.b v)) (round9 (Vertex.c v))

private abbrev pat0000 : Edge n → Prop := EdgePatterns.Pat0000 (two := two9)
private abbrev pat1111 : Edge n → Prop := EdgePatterns.Pat1111 (two := two9)
private abbrev pat1001 : Edge n → Prop := EdgePatterns.Pat1001 (two := two9)
private abbrev pat0110 : Edge n → Prop := EdgePatterns.Pat0110 (two := two9)

private lemma monochromatic_iff_patterns (e : Edge n) :
    Edge.monochromatic f9 e ↔ pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e := by
  simpa [f9, pat0000, pat1111, pat1001, pat0110] using
    (LocalRule.monochromatic_iff_patterns (round := round9) (two := two9)
      (hr_true := fun a => round9_eq_true (a := a))
      (hr_false := fun a => round9_eq_false (a := a))
      (e := e))

private abbrev Edge0000 : Type := {e : Edge n // pat0000 e}
private abbrev Edge1111 : Type := {e : Edge n // pat1111 e}
private abbrev Edge1001 : Type := {e : Edge n // pat1001 e}
private abbrev Edge0110 : Type := {e : Edge n // pat0110 e}

private lemma card_edge0000 : Fintype.card Edge0000 = 24 := by
  have h : Fintype.card Edge0000 = (Fintype.card Small9).descFactorial 4 :=
    EdgePatterns.card_pat0000 (n := n) (two := two9)
  rw [h, card_Small9]
  decide

private lemma card_edge1111 : Fintype.card Edge1111 = 120 := by
  have h : Fintype.card Edge1111 = (Fintype.card Big9).descFactorial 4 :=
    EdgePatterns.card_pat1111 (n := n) (two := two9)
  rw [h, card_Big9]
  decide

private lemma card_edge1001 : Fintype.card Edge1001 = 240 := by
  have h : Fintype.card Edge1001 =
      (Fintype.card Big9).descFactorial 2 * (Fintype.card Small9).descFactorial 2 :=
    EdgePatterns.card_pat1001 (n := n) (two := two9)
  rw [h, card_Big9, card_Small9]
  decide

private lemma card_edge0110 : Fintype.card Edge0110 = 240 := by
  have h : Fintype.card Edge0110 =
      (Fintype.card Big9).descFactorial 2 * (Fintype.card Small9).descFactorial 2 :=
    EdgePatterns.card_pat0110 (n := n) (two := two9)
  rw [h, card_Big9, card_Small9]
  decide

private lemma edgeCount_9 : edgeCount n = 3024 := by
  classical
  have : edgeCount n = (9 : Nat).descFactorial 4 := by
    have : Fintype.card (Edge n) = Fintype.card (Fin 4 ↪ Sym n) :=
      Fintype.card_congr
        { toFun := fun e => ⟨e.1, e.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro e; apply Subtype.ext; funext i; rfl
          right_inv := by intro x; ext i; rfl }
    have hcongr : edgeCount n = Fintype.card (Fin 4 ↪ Sym n) := by simpa [edgeCount] using this
    simp [hcongr, Sym, n, Fintype.card_embedding_eq]
  exact this.trans (by decide : (9 : Nat).descFactorial 4 = 3024)

theorem monoFraction_f9_le_13_63 : monoFraction f9 ≤ (13 : ℚ) / 63 := by
  classical
  -- Upper bound `monoCount` by summing the four pattern counts.
  have hmonoCount :
      monoCount f9 = Fintype.card {e : Edge n // Edge.monochromatic f9 e} := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge n) (p := Edge.monochromatic f9)).symm
  have hEquiv :
      {e : Edge n // Edge.monochromatic f9 e}
        ≃ {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e} :=
    Equiv.subtypeEquivRight (fun e => monochromatic_iff_patterns (e := e))
  have hmonoPatterns :
      monoCount f9 =
        Fintype.card {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e} := by
    simpa [hmonoCount] using (Fintype.card_congr hEquiv)
  have hUnion :
      Fintype.card {e : Edge n // pat0000 e ∨ pat1111 e ∨ pat1001 e ∨ pat0110 e}
        ≤
          Fintype.card Edge0000
            + (Fintype.card Edge1111 + (Fintype.card Edge1001 + Fintype.card Edge0110)) := by
    dsimp only [Edge0000, Edge1111, Edge1001, Edge0110]
    exact card_or4_le pat0000 pat1111 pat1001 pat0110
  have hmonoNat : monoCount f9 ≤ 624 := by
    have : monoCount f9 ≤
        Fintype.card Edge0000
          + (Fintype.card Edge1111 + (Fintype.card Edge1001 + Fintype.card Edge0110)) := by
      simpa [hmonoPatterns] using hUnion
    simpa [card_edge0000, card_edge1111, card_edge1001, card_edge0110, Nat.add_assoc] using this
  have hcount : (monoCount f9 : ℚ) ≤ (624 : ℚ) := by exact_mod_cast hmonoNat
  have hE : (edgeCount n : ℚ) = 3024 := by exact_mod_cast edgeCount_9
  -- Divide both sides by `edgeCount`.
  have hdiv : monoFraction f9 ≤ (624 : ℚ) / (edgeCount n : ℚ) := by
    have hEpos : (0 : ℚ) ≤ (edgeCount n : ℚ) := by exact_mod_cast (Nat.zero_le (edgeCount n))
    simpa [monoFraction] using (div_le_div_of_nonneg_right hcount hEpos)
  have hred : (624 : ℚ) / (edgeCount n : ℚ) = (13 : ℚ) / 63 := by
    simp [hE, show (624 : ℚ) / 3024 = (13 : ℚ) / 63 by norm_num]
  simpa [hred] using hdiv

theorem exists_coloring_monoFraction_le_13_63 : ∃ f : Coloring9, monoFraction f ≤ (13 : ℚ) / 63 :=
  ⟨f9, monoFraction_f9_le_13_63⟩

end N9

/-!
### A clean universal upper bound (`≤ 1/4` for all `n ≥ 5`)

We give an explicit coloring (the same rounding-based rule as above) and show its monochromatic-edge
fraction is at most `1/4` for every `n ≥ 5`.
-/

namespace Universal

open scoped BigOperators

variable {n : Nat}

-- We assume `n ≥ 5` throughout this section.
variable (hn : 5 ≤ n)

/-- The rounding threshold `⌊n/2⌋`, viewed as an element of `Fin n`. -/
abbrev two (n : Nat) (hn : 5 ≤ n) : Sym n :=
  ⟨n / 2, Nat.div_lt_self (lt_of_lt_of_le (by decide : 0 < 5) hn) (by decide : 1 < 2)⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Small (n : Nat) (hn : 5 ≤ n) : Type := EdgePatterns.Small (two := two n hn)
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Big (n : Nat) (hn : 5 ≤ n) : Type := EdgePatterns.Big (two := two n hn)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def round (n : Nat) (hn : 5 ≤ n) (a : Sym n) : Bool :=
  decide (two n hn ≤ a)

@[simp] lemma round_eq_true {a : Sym n} :
    round (n := n) hn a = true ↔ two n hn ≤ a := by
  simp [round]

@[simp] lemma round_eq_false {a : Sym n} :
    round (n := n) hn a = false ↔ a < two n hn := by
  simp [round, not_le]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev f (n : Nat) (hn : 5 ≤ n) : Coloring n :=
  fun v =>
    g (round n hn (Vertex.a v)) (round n hn (Vertex.b v)) (round n hn (Vertex.c v))

private abbrev pat0000 : Edge n → Prop := EdgePatterns.Pat0000 (two := two n hn)
private abbrev pat1111 : Edge n → Prop := EdgePatterns.Pat1111 (two := two n hn)
private abbrev pat1001 : Edge n → Prop := EdgePatterns.Pat1001 (two := two n hn)
private abbrev pat0110 : Edge n → Prop := EdgePatterns.Pat0110 (two := two n hn)

private lemma monochromatic_iff_patterns (e : Edge n) :
    Edge.monochromatic (f (n := n) hn) e ↔
      pat0000 (n := n) hn e ∨
        pat1111 (n := n) hn e ∨ pat1001 (n := n) hn e ∨ pat0110 (n := n) hn e := by
  simpa [f, pat0000, pat1111, pat1001, pat0110] using
    (LocalRule.monochromatic_iff_patterns (round := round (n := n) hn) (two := two n hn)
      (hr_true := fun a => round_eq_true (n := n) (hn := hn) (a := a))
      (hr_false := fun a => round_eq_false (n := n) (hn := hn) (a := a))
      (e := e))

private abbrev Edge0000 : Type := {e : Edge n // pat0000 (n := n) hn e}
private abbrev Edge1111 : Type := {e : Edge n // pat1111 (n := n) hn e}
private abbrev Edge1001 : Type := {e : Edge n // pat1001 (n := n) hn e}
private abbrev Edge0110 : Type := {e : Edge n // pat0110 (n := n) hn e}

private lemma cardEdgePatternsSmall :
    @Fintype.card (EdgePatterns.Small (two := two n hn)) (Subtype.fintype _) =
      @Fintype.card (Small (n := n) hn) (Set.instFintypeIio (two n hn)) := by
  exact @Fintype.card_congr (EdgePatterns.Small (two := two n hn)) (Small (n := n) hn)
    (Subtype.fintype _) (Set.instFintypeIio (two n hn)) (Equiv.refl _)

private lemma cardEdgePatternsBig :
    @Fintype.card (EdgePatterns.Big (two := two n hn)) (Subtype.fintype _) =
      @Fintype.card (Big (n := n) hn) (Set.instFintypeIci (two n hn)) := by
  exact @Fintype.card_congr (EdgePatterns.Big (two := two n hn)) (Big (n := n) hn)
    (Subtype.fintype _) (Set.instFintypeIci (two n hn)) (Equiv.refl _)

private lemma card_edge0000 :
    Fintype.card (Edge0000 (n := n) hn) = (Fintype.card (Small (n := n) hn)).descFactorial 4 := by
  classical
  refine Eq.trans (EdgePatterns.card_pat0000 (n := n) (two := two n hn)) ?_
  exact congrArg (fun k : Nat => k.descFactorial 4) (cardEdgePatternsSmall (n := n) hn)

private lemma card_edge1111 :
    Fintype.card (Edge1111 (n := n) hn) = (Fintype.card (Big (n := n) hn)).descFactorial 4 := by
  classical
  refine Eq.trans (EdgePatterns.card_pat1111 (n := n) (two := two n hn)) ?_
  exact congrArg (fun k : Nat => k.descFactorial 4) (cardEdgePatternsBig (n := n) hn)

private lemma card_edge1001 :
    Fintype.card (Edge1001 (n := n) hn)
      =
      (Fintype.card (Big (n := n) hn)).descFactorial 2 *
        (Fintype.card (Small (n := n) hn)).descFactorial 2 := by
  classical
  refine Eq.trans (EdgePatterns.card_pat1001 (n := n) (two := two n hn)) ?_
  rw [cardEdgePatternsBig (n := n) hn, cardEdgePatternsSmall (n := n) hn]

private lemma card_edge0110 :
    Fintype.card (Edge0110 (n := n) hn)
      =
      (Fintype.card (Big (n := n) hn)).descFactorial 2 *
        (Fintype.card (Small (n := n) hn)).descFactorial 2 := by
  classical
  refine Eq.trans (EdgePatterns.card_pat0110 (n := n) (two := two n hn)) ?_
  rw [cardEdgePatternsBig (n := n) hn, cardEdgePatternsSmall (n := n) hn]

private lemma edgeCount_eq_descFactorial : edgeCount n = n.descFactorial 4 := by
  classical
  have :
      Fintype.card (Edge n) = Fintype.card (Fin 4 ↪ Sym n) :=
    Fintype.card_congr
      { toFun := fun e => ⟨e.1, e.2⟩
        invFun := fun x => ⟨x, x.injective⟩
        left_inv := by intro e; apply Subtype.ext; funext i; rfl
        right_inv := by intro x; ext i; rfl }
  simpa [edgeCount, Sym, Fintype.card_embedding_eq] using this

private lemma monoCount_le_bound :
    monoCount (f (n := n) hn)
      ≤ (Fintype.card (Small (n := n) hn)).descFactorial 4
          + (Fintype.card (Big (n := n) hn)).descFactorial 4
          + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
              * (Fintype.card (Big (n := n) hn)).descFactorial 2)) := by
  classical
  have hMonoEq :
      monoCount (f (n := n) hn)
        = Fintype.card {e : Edge n // Edge.monochromatic (f (n := n) hn) e} := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge n) (p := Edge.monochromatic (f (n := n) hn))).symm
  have hEquiv :
      {e : Edge n // Edge.monochromatic (f (n := n) hn) e}
        ≃
        {e : Edge n //
          pat0000 (n := n) hn e ∨
            pat1111 (n := n) hn e ∨ pat1001 (n := n) hn e ∨ pat0110 (n := n) hn e} :=
    Equiv.subtypeEquivRight (fun e => monochromatic_iff_patterns (n := n) hn (e := e))
  have hMonoPatterns :
      monoCount (f (n := n) hn)
        = Fintype.card {e : Edge n //
            pat0000 (n := n) hn e ∨
              pat1111 (n := n) hn e ∨ pat1001 (n := n) hn e ∨ pat0110 (n := n) hn e} := by
    simpa [hMonoEq] using (Fintype.card_congr hEquiv)
  -- Bound the card of the disjunction subtype by the sum of the four pattern subtype cards.
  have hUnion :
      Fintype.card {e : Edge n //
          pat0000 (n := n) hn e ∨
            pat1111 (n := n) hn e ∨ pat1001 (n := n) hn e ∨ pat0110 (n := n) hn e}
        ≤
          Fintype.card (Edge0000 (n := n) hn)
            + (Fintype.card (Edge1111 (n := n) hn)
              + (Fintype.card (Edge1001 (n := n) hn) + Fintype.card (Edge0110 (n := n) hn))) := by
    dsimp only [Edge0000, Edge1111, Edge1001, Edge0110]
    exact card_or4_le (pat0000 (n := n) hn) (pat1111 (n := n) hn) (pat1001 (n := n) hn)
      (pat0110 (n := n) hn)
  have hMono :
      monoCount (f (n := n) hn)
        ≤
          Fintype.card (Edge0000 (n := n) hn)
            + (Fintype.card (Edge1111 (n := n) hn)
              + (Fintype.card (Edge1001 (n := n) hn) + Fintype.card (Edge0110 (n := n) hn))) := by
    simpa [hMonoPatterns] using hUnion
  -- Evaluate the pattern cards using the bijections above.
  have h0000 := card_edge0000 (n := n) hn
  have h1111 := card_edge1111 (n := n) hn
  have h1001 := card_edge1001 (n := n) hn
  have h0110 := card_edge0110 (n := n) hn
  -- Rewrite into the claimed (slightly grouped) bound.
  -- The mixed patterns have the same cardinality.
  have :
      monoCount (f (n := n) hn)
        ≤
          (Fintype.card (Small (n := n) hn)).descFactorial 4
            + ((Fintype.card (Big (n := n) hn)).descFactorial 4
              + ((Fintype.card (Big (n := n) hn)).descFactorial 2
                  * (Fintype.card (Small (n := n) hn)).descFactorial 2
                + (Fintype.card (Big (n := n) hn)).descFactorial 2
                  * (Fintype.card (Small (n := n) hn)).descFactorial 2)) := by
    simpa [h0000, h1111, h1001, h0110, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hMono
  -- Turn `x + x` into `2 * x`.
  simpa [two_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

/-- The discriminant-style product `4·m·(m-1)·(4m-k)` is nonnegative once `1 ≤ m` and `0 ≤ 4m-k`. -/
private lemma prod_quarter_nonneg {m k : ℚ} (hm1 : 1 ≤ m) (hk : 0 ≤ 4 * m - k) :
    0 ≤ 4 * m * (m - 1) * (4 * m - k) :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hk

private lemma bound_le_quarter_of_even (m : Nat) (hm : 3 ≤ m) :
    (4 : ℚ) *
        ((2 * (m.descFactorial 4) + 2 * (m.descFactorial 2 * m.descFactorial 2) : Nat) : ℚ)
      ≤ ((2 * m).descFactorial 4 : ℚ) := by
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 3) hm
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 3) hm
  have h2m1 : 1 ≤ 2 * m := by
    have : 2 ≤ 2 * m := by simpa [two_mul] using Nat.mul_le_mul_left 2 hm1
    exact le_trans (by decide : 1 ≤ 2) this
  have h2m2 : 2 ≤ 2 * m := by simpa [two_mul] using Nat.mul_le_mul_left 2 hm1
  have h2m3 : 3 ≤ 2 * m := by
    have : 6 ≤ 2 * m := by simpa [two_mul] using Nat.mul_le_mul_left 2 hm
    exact le_trans (by decide : 3 ≤ 6) this
  have hmQ : (3 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hdiff :
      ((2 * m).descFactorial 4 : ℚ)
        -
          (4 : ℚ) *
            ((2 * (m.descFactorial 4) + 2 * (m.descFactorial 2 * m.descFactorial 2) : Nat) : ℚ)
        =
        (4 : ℚ) * (m : ℚ) * ((m : ℚ) - 1) * ((4 : ℚ) * (m : ℚ) - 9) := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hm1, Nat.cast_sub hm2, Nat.cast_sub hm, Nat.cast_sub h2m1, Nat.cast_sub h2m2,
      Nat.cast_sub h2m3]
    ring
  have hm1Q : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
  have h4m9 : (0 : ℚ) ≤ (4 : ℚ) * (m : ℚ) - 9 := by nlinarith [hmQ]
  exact (sub_nonneg).1 (hdiff ▸ prod_quarter_nonneg hm1Q h4m9)

private lemma bound_le_quarter_of_odd (m : Nat) (hm : 2 ≤ m) :
    (4 : ℚ) *
        ((m.descFactorial 4 + (m + 1).descFactorial 4 +
              2 * (m.descFactorial 2 * (m + 1).descFactorial 2) : Nat) : ℚ)
      ≤ ((2 * m + 1).descFactorial 4 : ℚ) := by
  have cast_descFactorial_four (a : Nat) :
      (a.descFactorial 4 : ℚ) =
        (a : ℚ) * ((a : ℚ) - 1) * ((a : ℚ) - 2) * ((a : ℚ) - 3) := by
    have hdf : (a.descFactorial 4 : ℚ) = (descPochhammer ℚ 4).eval (a : ℚ) := by
      simpa using (descPochhammer_eval_eq_descFactorial (R := ℚ) a 4).symm
    rw [hdf, descPochhammer_eval_eq_prod_range (R := ℚ) 4 (a : ℚ)]
    simp [Finset.prod_range_succ, mul_assoc]
  have cast_descFactorial_two (a : Nat) :
      (a.descFactorial 2 : ℚ) = (a : ℚ) * ((a : ℚ) - 1) := by
    have hdf : (a.descFactorial 2 : ℚ) = (descPochhammer ℚ 2).eval (a : ℚ) := by
      simpa using (descPochhammer_eval_eq_descFactorial (R := ℚ) a 2).symm
    rw [hdf, descPochhammer_eval_eq_prod_range (R := ℚ) 2 (a : ℚ)]
    simp [Finset.prod_range_succ]
  have hdiff :
      ((2 * m + 1).descFactorial 4 : ℚ)
        -
          (4 : ℚ) *
            ((m.descFactorial 4 + (m + 1).descFactorial 4 +
                  2 * (m.descFactorial 2 * (m + 1).descFactorial 2) : Nat) : ℚ)
        =
        (4 : ℚ) * (m : ℚ) * ((m : ℚ) - 1) * ((4 : ℚ) * (m : ℚ) - 5) := by
    -- Restrict to cast lemmas: we don't want `simp` to unfold `Nat.descFactorial`.
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [cast_descFactorial_four (a := 2 * m + 1)]
    rw [cast_descFactorial_four (a := m)]
    rw [cast_descFactorial_four (a := m + 1)]
    rw [cast_descFactorial_two (a := m)]
    rw [cast_descFactorial_two (a := m + 1)]
    -- Expand remaining casts like `↑(m + 1)` into `↑m + 1` so `ring_nf` can normalize.
    simp [Nat.cast_add, Nat.cast_mul]
    ring_nf
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hm1Q : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
  have h4m5 : (0 : ℚ) ≤ (4 : ℚ) * (m : ℚ) - 5 := by nlinarith [hmQ]
  exact (sub_nonneg).1 (hdiff ▸ prod_quarter_nonneg hm1Q h4m5)

/-- The rounding-based coloring has monochromatic fraction at most `1/4` for every `n ≥ 5`. -/
theorem monoFraction_f_le_one_quarter : monoFraction (f (n := n) hn) ≤ (1 : ℚ) / 4 := by
  classical
  -- Reduce to a numeric inequality between the explicit count bound and `edgeCount n`.
  have hEdge : edgeCount n = n.descFactorial 4 := edgeCount_eq_descFactorial (n := n)
  have hCount :
      monoCount (f (n := n) hn)
        ≤ (Fintype.card (Small (n := n) hn)).descFactorial 4
            + (Fintype.card (Big (n := n) hn)).descFactorial 4
            + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
              * (Fintype.card (Big (n := n) hn)).descFactorial 2)) :=
    monoCount_le_bound (n := n) hn
  have hCountQ :
      (monoCount (f (n := n) hn) : ℚ)
        ≤
          ((Fintype.card (Small (n := n) hn)).descFactorial 4
              + (Fintype.card (Big (n := n) hn)).descFactorial 4
              + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
                * (Fintype.card (Big (n := n) hn)).descFactorial 2)) : Nat) := by
    exact_mod_cast hCount
  have hEpos : (0 : ℚ) < (edgeCount n : ℚ) := by
    -- For `n ≥ 5`, the set of edges is nonempty (take `0,1,2,3`).
    have hn4 : 4 ≤ n := le_trans (by decide : 4 ≤ 5) hn
    let e0 : Edge n :=
      ⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 hn4⟩, by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Fin n => x.1) hij⟩
    have : Nonempty (Edge n) := ⟨e0⟩
    have : 0 < Fintype.card (Edge n) := Fintype.card_pos_iff.2 this
    simpa [edgeCount] using (show (0 : ℚ) < (Fintype.card (Edge n) : ℚ) from by exact_mod_cast this)
  -- It suffices to show the explicit count bound is at most `edgeCount/4`.
  have hQuarter :
      (4 : ℚ) *
          ((Fintype.card (Small (n := n) hn)).descFactorial 4
              + (Fintype.card (Big (n := n) hn)).descFactorial 4
              + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
                * (Fintype.card (Big (n := n) hn)).descFactorial 2)) : Nat) ≤
        (edgeCount n : ℚ) := by
    -- Evaluate the half sizes via parity.
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- even `n = m + m`
      have hm : 3 ≤ m := by
        -- if `m ≤ 2` then `m + m ≤ 4`, contradicting `hn : 5 ≤ m + m`
        by_contra h
        have hmLt : m < 3 := Nat.lt_of_not_ge h
        have hmLe2 : m ≤ 2 := Nat.lt_succ_iff.mp hmLt
        have hsum : m + m ≤ 4 := by
          have := Nat.add_le_add hmLe2 hmLe2
          simpa using this
        have : 5 ≤ 4 := le_trans hn hsum
        exact (by decide : ¬ 5 ≤ 4) this
      have hDiv : (m + m) / 2 = m := by
        rw [← two_mul m]
        simp
      have hSmall : Fintype.card (Small (n := m + m) hn) = m := by
        calc
          Fintype.card (Small (n := m + m) hn) = (m + m) / 2 := by simp [Small, two]
          _ = m := hDiv
      have hBig : Fintype.card (Big (n := m + m) hn) = m := by
        have hCard : Fintype.card (Big (n := m + m) hn) = (m + m) - (m + m) / 2 := by
          simp [Big, two]
        calc
          Fintype.card (Big (n := m + m) hn) = (m + m) - (m + m) / 2 := hCard
          _ = (m + m) - m := by simp [hDiv]
          _ = m := by simp
      have hEdgeQ : (edgeCount (m + m) : ℚ) = ((m + m).descFactorial 4 : ℚ) := by
        exact_mod_cast (edgeCount_eq_descFactorial (n := m + m))
      rw [hEdgeQ]
      rw [hSmall, hBig]
      simpa
          [two_mul,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using bound_le_quarter_of_even (m := m) hm
    · -- odd `n = 2*m+1`
      have hm : 2 ≤ m := by
        -- if `m ≤ 1` then `2*m + 1 ≤ 3`, contradicting `hn : 5 ≤ 2*m + 1`
        by_contra h
        have hmLt : m < 2 := Nat.lt_of_not_ge h
        have hmLe1 : m ≤ 1 := Nat.lt_succ_iff.mp hmLt
        have hmul : 2 * m ≤ 2 := by
          have := Nat.mul_le_mul_left 2 hmLe1
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
        have hsum : 2 * m + 1 ≤ 3 := by
          have := Nat.succ_le_succ hmul
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using this
        have : 5 ≤ 3 := le_trans hn hsum
        exact (by decide : ¬ 5 ≤ 3) this
      have hDiv : (2 * m + 1) / 2 = m := by
        have : (1 + 2 * m) / 2 = m := by
          simpa using (Nat.add_mul_div_left 1 m (y := 2) (by decide : 0 < 2))
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have hSmall : Fintype.card (Small (n := 2 * m + 1) hn) = m := by
        calc
          Fintype.card (Small (n := 2 * m + 1) hn) = (2 * m + 1) / 2 := by simp [Small, two]
          _ = m := hDiv
      have hBig : Fintype.card (Big (n := 2 * m + 1) hn) = m + 1 := by
        have hCard :
            Fintype.card (Big (n := 2 * m + 1) hn) = (2 * m + 1) - (2 * m + 1) / 2 := by
          simp [Big, two]
        have hRewrite : 2 * m + 1 = m + (m + 1) := by simpa [two_mul] using (Nat.add_assoc m m 1)
        calc
          Fintype.card (Big (n := 2 * m + 1) hn) = (2 * m + 1) - (2 * m + 1) / 2 := hCard
          _ = (2 * m + 1) - m := by simp [hDiv]
          _ = m + 1 := by
            calc
              (2 * m + 1) - m = (m + (m + 1)) - m := by simp [hRewrite]
              _ = m + 1 := by simp
      have hEdgeQ : (edgeCount (2 * m + 1) : ℚ) = ((2 * m + 1).descFactorial 4 : ℚ) := by
        exact_mod_cast (edgeCount_eq_descFactorial (n := 2 * m + 1))
      rw [hEdgeQ]
      rw [hSmall, hBig]
      simpa
          [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        using bound_le_quarter_of_odd (m := m) hm
  have hFracBound :
      monoFraction (f (n := n) hn)
        ≤
          ((Fintype.card (Small (n := n) hn)).descFactorial 4
              + (Fintype.card (Big (n := n) hn)).descFactorial 4
              + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
                * (Fintype.card (Big (n := n) hn)).descFactorial 2)) : Nat) /
              (edgeCount n : ℚ) := by
    -- divide the `monoCount` bound by `edgeCount`
    have hEpos' : 0 ≤ (edgeCount n : ℚ) := le_of_lt hEpos
    simpa [monoFraction] using (div_le_div_of_nonneg_right hCountQ hEpos')
  -- Finish: the RHS is at most `1/4` since `4 * bound ≤ edgeCount`.
  have hBoundFrac :
      ((Fintype.card (Small (n := n) hn)).descFactorial 4
              + (Fintype.card (Big (n := n) hn)).descFactorial 4
              + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
                * (Fintype.card (Big (n := n) hn)).descFactorial 2)) : Nat) / (edgeCount n : ℚ)
        ≤ (1 : ℚ) / 4 := by
    have hEpos' : 0 < (edgeCount n : ℚ) := hEpos
    have hmul : ((1 : ℚ) / 4) * (4 : ℚ) = 1 := by norm_num
    have hBoundLe :
        (((Fintype.card (Small (n := n) hn)).descFactorial 4
                + (Fintype.card (Big (n := n) hn)).descFactorial 4
                + (2 * ((Fintype.card (Small (n := n) hn)).descFactorial 2
                  * (Fintype.card (Big (n := n) hn)).descFactorial 2)) : Nat) : ℚ)
          ≤ ((1 : ℚ) / 4) * (edgeCount n : ℚ) := by
      have h :=
          mul_le_mul_of_nonneg_left hQuarter (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 4)
      simpa [mul_assoc, hmul] using h
    exact (div_le_iff₀ hEpos').2 hBoundLe
  exact le_trans hFracBound hBoundFrac

theorem exists_coloring_monoFraction_le_one_quarter {n : Nat} (hn : 5 ≤ n) :
    ∃ f : Coloring n, monoFraction f ≤ (1 : ℚ) / 4 :=
  ⟨f (n := n) hn, monoFraction_f_le_one_quarter (n := n) hn⟩

end Universal

end UpperBound

end Distributed2Coloring.LowerBound
