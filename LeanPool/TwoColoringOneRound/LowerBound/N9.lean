/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
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

/-!
## Warm-up: `n = 9` gives `> 20%`

This file proves a small “warm-up” theorem matching the report:

* the `5`-cycle argument gives `monoCount f ≥ 605` for every `f : Coloring 9`;
* a parity lemma shows `monoCount f` is even, hence `monoCount f ≥ 606`;
* therefore `monoFraction f ≥ 606/3024 = 101/504 > 1/5`.

All proofs are kernel-checked (no `native_decide`).
-/

namespace Distributed2Coloring.LowerBound


namespace N9

open scoped BigOperators

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := 9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Sym9 := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Coloring9 := Coloring n

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Emb4 : Type := Fin 4 ↪ Sym9
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Emb5 : Type := Fin 5 ↪ Sym9

noncomputable instance : Fintype Emb4 := by infer_instance
noncomputable instance : Fintype Emb5 := by infer_instance

/-!
### A cyclic `5`-cycle model on `Emb5`

For `t : Emb5` (five distinct symbols) and `k : Fin 5`, define the directed edge obtained from the
ordered quadruple of consecutive symbols starting at position `k` (cyclically).

We also record the “missing” index in the `5`-tuple.
-/

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def idx4 (k : Fin 5) : Fin 4 → Fin 5 :=
  fun i => k + i.castAdd 1

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def next (k : Fin 5) : Fin 5 :=
  k + 1

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def remIndex (k : Fin 5) : Fin 5 :=
  k + 4

private lemma idx4_injective (k : Fin 5) : Function.Injective (idx4 k) := by
  intro i j hij
  have hcast : (i.castAdd 1 : Fin 5) = j.castAdd 1 := by
    simpa [idx4] using congrArg (fun x : Fin 5 => x - k) hij
  exact Fin.castAdd_injective _ _ hcast

private lemma idx4_ne_remIndex (k : Fin 5) (i : Fin 4) : idx4 k i ≠ remIndex k := by
  intro h
  have hcast : (i.castAdd 1 : Fin 5) = 4 := by
    simpa [idx4, remIndex] using congrArg (fun x : Fin 5 => x - k) h
  have hne : ((i.castAdd 1 : Fin 5) : Nat) ≠ 4 := Nat.ne_of_lt i.2
  exact hne (by simpa using congrArg Fin.val hcast)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def edgeAt (t : Emb5) (k : Fin 5) : Edge n :=
  ⟨fun i => t (idx4 k i), by
    intro i j hij
    exact idx4_injective k (t.injective hij)⟩

private lemma dst_edgeAt_eq_src_edgeAt_next (t : Emb5) (k : Fin 5) :
    Edge.dst (edgeAt t k) = Edge.src (edgeAt t (next k)) := by
  classical
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.dst, Edge.src, Edge.dstIndex, Edge.srcIndex, edgeAt, idx4, next, add_assoc]

/-!
### An odd cycle has a monochromatic edge

We use brute-force case splitting on 5 booleans (32 cases), which is small and kernel-checked.
-/

private lemma cycle5_has_adjacent_equal (b0 b1 b2 b3 b4 : Bool) :
    (b0 = b1) ∨ (b1 = b2) ∨ (b2 = b3) ∨ (b3 = b4) ∨ (b4 = b0) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma monochromatic_edgeAt_iff (f : Coloring9) (t : Emb5) (k : Fin 5) :
    Edge.monochromatic f (edgeAt t k) ↔
      f (Edge.src (edgeAt t k)) = f (Edge.src (edgeAt t (next k))) := by
  have h := dst_edgeAt_eq_src_edgeAt_next (t := t) (k := k)
  unfold Edge.monochromatic
  simp [h]

private lemma exists_mono_edge_in_cycle (f : Coloring9) (t : Emb5) :
    ∃ k : Fin 5, Edge.monochromatic f (edgeAt t k) := by
  classical
  let b0 := f (Edge.src (edgeAt t 0))
  let b1 := f (Edge.src (edgeAt t 1))
  let b2 := f (Edge.src (edgeAt t 2))
  let b3 := f (Edge.src (edgeAt t 3))
  let b4 := f (Edge.src (edgeAt t 4))
  have hb : (b0 = b1) ∨ (b1 = b2) ∨ (b2 = b3) ∨ (b3 = b4) ∨ (b4 = b0) :=
    cycle5_has_adjacent_equal b0 b1 b2 b3 b4
  rcases hb with h01 | h12 | h23 | h34 | h40
  · refine ⟨0, (monochromatic_edgeAt_iff (f := f) (t := t) (k := 0)).2 ?_⟩
    simpa [b0, b1, next] using h01
  · refine ⟨1, (monochromatic_edgeAt_iff (f := f) (t := t) (k := 1)).2 ?_⟩
    simpa [b1, b2, next] using h12
  · refine ⟨2, (monochromatic_edgeAt_iff (f := f) (t := t) (k := 2)).2 ?_⟩
    simpa [b2, b3, next] using h23
  · refine ⟨3, (monochromatic_edgeAt_iff (f := f) (t := t) (k := 3)).2 ?_⟩
    simpa [b3, b4, next] using h34
  · refine ⟨4, (monochromatic_edgeAt_iff (f := f) (t := t) (k := 4)).2 ?_⟩
    simpa [b4, b0, next] using h40

/-!
### Double-counting the cycle-edge pairs

We count pairs `(t,k)` where the `k`-th edge in the `5`-cycle from `t` is monochromatic.
For `n = 9`, every edge participates in exactly `5 * (9-4) = 25` such pairs, hence

`Fintype.card (CycleMonoPairs f) = 25 * monoCount f`.
-/

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev CyclePairs : Type := Emb5 × Fin 5

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def CycleMonoPairs (f : Coloring9) : Type :=
  {p : CyclePairs // Edge.monochromatic f (edgeAt p.1 p.2)}

noncomputable instance (f : Coloring9) : Fintype (CycleMonoPairs f) := by
  classical
  dsimp [CycleMonoPairs, CyclePairs]
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def edgeEmb (e : Edge n) : Emb4 := ⟨e.1, e.2⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Extra (e : Edge n) : Set Sym9 := (Set.range (edgeEmb e))ᶜ

noncomputable instance (e : Edge n) : Fintype (Extra e) := by
  classical
  dsimp [Extra]
  infer_instance

private lemma card_extra (e : Edge n) : Fintype.card (Extra e) = 5 := by
  classical
  have hr : Fintype.card (Set.range (edgeEmb e)) = 4 := by
    simpa using (Fintype.card_range (f := edgeEmb e))
  -- `|Sym9| = 9` and `|range(edgeEmb e)| = 4`.
  have h := Fintype.card_compl_set (s := Set.range (edgeEmb e))
  norm_num [Extra, Sym9, Sym, hr, Fintype.card_fin] at h ⊢
  exact h

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev EdgeExtraK : Type := {q : Edge n × (Sym9 × Fin 5) // q.2.1 ∈ Extra q.1}

noncomputable instance : Fintype EdgeExtraK := by
  classical
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def cyclePairToEdgeExtraK : CyclePairs → EdgeExtraK
  | (t, k) =>
      let e : Edge n := edgeAt t k
      let r : Sym9 := t (remIndex k)
      have hr : r ∈ Extra e := by
        -- `r` is the unused symbol among the five; it cannot lie in the range of the 4-tuple `e`.
        intro hIn
        rcases hIn with ⟨i, hi⟩
        have hIdx : idx4 k i = remIndex k := by
          apply t.injective
          -- `edgeEmb e i = r` expands to `t (idx4 k i) = t (remIndex k)`.
          have : t (idx4 k i) = t (remIndex k) := by simpa [e, edgeAt, edgeEmb, r] using hi
          exact this
        exact idx4_ne_remIndex k i hIdx
      ⟨(e, (r, k)), hr⟩

private def choice (k : Fin 5) : Fin 5 → Option (Fin 4) :=
  match k.1 with
  | 0 =>
      fun i =>
        match i.1 with
        | 0 => some 0
        | 1 => some 1
        | 2 => some 2
        | 3 => some 3
        | _ => none
  | 1 =>
      fun i =>
        match i.1 with
        | 0 => none
        | 1 => some 0
        | 2 => some 1
        | 3 => some 2
        | _ => some 3
  | 2 =>
      fun i =>
        match i.1 with
        | 0 => some 3
        | 1 => none
        | 2 => some 0
        | 3 => some 1
        | _ => some 2
  | 3 =>
      fun i =>
        match i.1 with
        | 0 => some 2
        | 1 => some 3
        | 2 => none
        | 3 => some 0
        | _ => some 1
  | _ =>
      fun i =>
        match i.1 with
        | 0 => some 1
        | 1 => some 2
        | 2 => some 3
        | 3 => none
        | _ => some 0

private lemma choice_injective (k : Fin 5) : Function.Injective (choice k) := by
  intro i j hij
  fin_cases k <;> fin_cases i <;> fin_cases j <;> cases hij <;> rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def edgeExtraKToCyclePair : EdgeExtraK → CyclePairs
  | ⟨⟨e, (r, k)⟩, hr⟩ =>
      let tFun : Fin 5 → Sym9 := fun i =>
        match choice k i with
        | none => r
        | some j => e.1 j
      have ht : Function.Injective tFun := by
        classical
        have hrne : ∀ j : Fin 4, r ≠ e.1 j := by
          intro j hj
          have : r ∈ Set.range (edgeEmb e) := ⟨j, by simpa [edgeEmb] using hj.symm⟩
          exact hr this
        intro i j hij
        cases hci : choice k i with
        | none =>
            cases hcj : choice k j with
            | none =>
                exact choice_injective k (by simp [hci, hcj])
            | some j' =>
                have : r = e.1 j' := by simpa [tFun, hci, hcj] using hij
                exact False.elim (hrne j' this)
        | some i' =>
            cases hcj : choice k j with
            | none =>
                have : e.1 i' = r := by simpa [tFun, hci, hcj] using hij
                exact False.elim (hrne i' this.symm)
            | some j' =>
                have hij' : i' = j' := e.2 (by simpa [tFun, hci, hcj] using hij)
                exact choice_injective k (by simp [hci, hcj, hij'])
      (⟨tFun, ht⟩, k)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def cyclePairEquiv : CyclePairs ≃ EdgeExtraK where
  toFun := cyclePairToEdgeExtraK
  invFun := edgeExtraKToCyclePair
  left_inv := by
    classical
    intro p
    rcases p with ⟨t, k⟩
    apply Prod.ext
    · ext i
      fin_cases k <;> fin_cases i <;>
        simp [cyclePairToEdgeExtraK, edgeExtraKToCyclePair, edgeAt, choice, idx4, remIndex]
    · rfl
  right_inv := by
    classical
    intro q
    rcases q with ⟨⟨e, ⟨r, k⟩⟩, hr⟩
    apply Subtype.ext
    -- Equality in `Edge n × (Sym9 × Fin 5)`.
    apply Prod.ext
    · -- edge component
      apply Subtype.ext
      funext i
      fin_cases k <;> fin_cases i <;>
        simp [cyclePairToEdgeExtraK, edgeExtraKToCyclePair, edgeAt, choice, idx4, remIndex]
    · -- `(Sym9 × Fin 5)` component
      apply Prod.ext
      · -- the “extra” symbol is exactly `r`
        fin_cases k <;>
          simp [cyclePairToEdgeExtraK, edgeExtraKToCyclePair, choice, remIndex]
      · rfl

private lemma card_cycleMonoPairs_eq (f : Coloring9) :
    Fintype.card (CycleMonoPairs f) = 25 * monoCount f := by
  classical
  let P : EdgeExtraK → Prop := fun q => Edge.monochromatic f q.1.1
  have hcongr :
      Fintype.card (CycleMonoPairs f) = Fintype.card {q : EdgeExtraK // P q} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun p => ⟨cyclePairEquiv p.1, by
          simpa [CycleMonoPairs, P, cyclePairEquiv, cyclePairToEdgeExtraK] using p.2⟩
        invFun := fun q => ⟨cyclePairEquiv.symm q.1, by
          have hEdge :
              edgeAt (cyclePairEquiv.symm q.1).1 (cyclePairEquiv.symm q.1).2 = q.1.1.1 := by
            -- Extract the edge component from `cyclePairEquiv (cyclePairEquiv.symm q.1) = q.1`.
            have h :=
              congrArg (fun z : EdgeExtraK => z.1.1) (cyclePairEquiv.apply_symm_apply q.1)
            simpa [cyclePairEquiv, cyclePairToEdgeExtraK] using h
          -- Rewrite the goal with `hEdge` and use `q.2`.
          simpa [CycleMonoPairs, P] using (hEdge ▸ q.2)⟩
        left_inv := by
          intro p
          apply Subtype.ext
          simp
        right_inv := by
          intro q
          apply Subtype.ext
          simp }
  have hreassoc :
      Fintype.card {q : EdgeExtraK // P q}
        = Fintype.card (Σ e : {e : Edge n // Edge.monochromatic f e}, Extra e.1 × Fin 5) := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun q =>
          ⟨⟨q.1.1.1, q.2⟩, (⟨q.1.1.2.1, q.1.2⟩, q.1.1.2.2)⟩
        invFun := fun x =>
          ⟨⟨(x.1.1, (x.2.1.1, x.2.2)), x.2.1.2⟩, x.1.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by intro x; cases x; rfl }
  have hmono :
      Fintype.card {e : Edge n // Edge.monochromatic f e} = monoCount f := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge n) (p := Edge.monochromatic f))
  calc
    Fintype.card (CycleMonoPairs f)
        = Fintype.card {q : EdgeExtraK // P q} := hcongr
    _ = Fintype.card (Σ e : {e : Edge n // Edge.monochromatic f e}, Extra e.1 × Fin 5) := hreassoc
    _ = ∑ e : {e : Edge n // Edge.monochromatic f e}, Fintype.card (Extra e.1 × Fin 5) := by
          simp [Fintype.card_sigma]
    _ = ∑ _e : {e : Edge n // Edge.monochromatic f e}, 25 := by
          refine Finset.sum_congr rfl ?_
          intro e _
          have hE : Fintype.card (Extra e.1) = 5 := card_extra e.1
          simp [Fintype.card_prod, hE, Fintype.card_fin]
    _ = (Fintype.card {e : Edge n // Edge.monochromatic f e}) * 25 := by
          simp [Finset.sum_const, mul_comm]
    _ = monoCount f * 25 := by simp [hmono]
    _ = 25 * monoCount f := by ac_rfl

private lemma monoCount_ge_605 (f : Coloring9) : 605 ≤ monoCount f := by
  classical
  -- Inject `Emb5` into `CycleMonoPairs f` by choosing a monochromatic edge on each 5-cycle.
  let chooseK : Emb5 → Fin 5 := fun t => Classical.choose (exists_mono_edge_in_cycle (f := f) t)
  have chooseK_spec (t : Emb5) : Edge.monochromatic f (edgeAt t (chooseK t)) :=
    Classical.choose_spec (exists_mono_edge_in_cycle (f := f) t)
  let inj : Emb5 → CycleMonoPairs f := fun t => ⟨(t, chooseK t), chooseK_spec t⟩
  have hinj : Function.Injective inj := by
    intro t1 t2 h
    have : (t1, chooseK t1) = (t2, chooseK t2) := congrArg Subtype.val h
    exact congrArg Prod.fst this
  have hcard : Fintype.card Emb5 ≤ Fintype.card (CycleMonoPairs f) :=
    Fintype.card_le_of_injective inj hinj
  have hEmb5 : Fintype.card Emb5 = 15120 := by
    have : Fintype.card Emb5 = (9 : Nat).descFactorial 5 := by
      simp [Emb5, Sym9, Sym, n, Fintype.card_embedding_eq]
    exact this.trans (by decide : (9 : Nat).descFactorial 5 = 15120)
  have hPairs : Fintype.card (CycleMonoPairs f) = 25 * monoCount f :=
    card_cycleMonoPairs_eq (f := f)
  have : 15120 ≤ 25 * monoCount f := by simpa [hEmb5, hPairs] using hcard
  nlinarith

/-!
### Parity lemma: `monoCount` is even

We show `(monoCount f : ZMod 2) = (edgeCount 9 : ZMod 2)`, hence `monoCount f` is even since
`edgeCount 9 = 3024` is even.
-/

private def bit : Bool → ZMod 2 := fun b => if b then 1 else 0

private lemma monoIndicator_zmod2 (f : Coloring9) (e : Edge n) :
    (if Edge.monochromatic f e then (1 : ZMod 2) else 0)
      = (1 : ZMod 2) + bit (f (Edge.src e)) + bit (f (Edge.dst e)) := by
  unfold bit Edge.monochromatic
  by_cases hs : f (Edge.src e) <;> by_cases ht : f (Edge.dst e) <;>
    simp only [hs, ht] <;> decide

private abbrev rotIndex : Equiv.Perm (Fin 4) := finRotate 4

private noncomputable def rotEdge : Edge n ≃ Edge n where
  toFun := fun e => ⟨fun i => e.1 (rotIndex i), by
    intro i j hij
    have : rotIndex i = rotIndex j := by
      apply e.2
      simpa using hij
    exact rotIndex.injective this⟩
  invFun := fun e => ⟨fun i => e.1 (rotIndex⁻¹ i), by
    intro i j hij
    have : rotIndex⁻¹ i = rotIndex⁻¹ j := by
      apply e.2
      simpa using hij
    exact (Equiv.injective rotIndex⁻¹) this⟩
  left_inv := by
    intro e
    apply Subtype.ext
    funext i
    -- `rotIndex (rotIndex⁻¹ i) = i`.
    have := congrArg e.1 (rotIndex.apply_symm_apply i)
    exact this
  right_inv := by
    intro e
    apply Subtype.ext
    funext i
    -- `rotIndex⁻¹ (rotIndex i) = i`.
    have := congrArg e.1 (rotIndex.symm_apply_apply i)
    exact this

private lemma edge_src_rotEdge (e : Edge n) : Edge.src (rotEdge e) = Edge.dst e := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [rotEdge, rotIndex, Edge.src, Edge.dst]

private lemma sum_bit_src_eq_sum_bit_dst (f : Coloring9) :
    (∑ e : Edge n, bit (f (Edge.src e))) = ∑ e : Edge n, bit (f (Edge.dst e)) := by
  classical
  have h :=
    (Fintype.sum_equiv rotEdge (fun e : Edge n => bit (f (Edge.src (rotEdge e))))
      (fun e : Edge n => bit (f (Edge.src e))) (by intro e; rfl))
  simpa [edge_src_rotEdge] using h.symm

private lemma monoCount_zmod2_eq_edgeCount_zmod2 (f : Coloring9) :
    (monoCount f : ZMod 2) = (edgeCount n : ZMod 2) := by
  classical
  have hmono :
      (monoCount f : ZMod 2)
        = ∑ e : Edge n, (if Edge.monochromatic f e then (1 : ZMod 2) else 0) := by
    -- Cast `card (univ.filter _)` into `ZMod 2` as a sum of indicators.
    -- (This avoids a `simp` loop on `Finset.card_eq_sum_ones`.)
    classical
    let p : Edge n → Prop := Edge.monochromatic f
    let s : Finset (Edge n) := (Finset.univ : Finset (Edge n)).filter p
    have hNat : s.card = s.sum (fun _ => (1 : Nat)) := by exact Finset.card_eq_sum_ones (s := s)
    have hCast : (s.card : ZMod 2) = s.sum (fun _ => (1 : ZMod 2)) := by
      convert congrArg (fun m : Nat => (m : ZMod 2)) hNat using 1
      · simp
    -- rewrite `monoCount` in terms of `s`
    have hs : monoCount f = s.card := by simp [monoCount, monoEdges, s, p]
    -- rewrite the sum over the filter
    have hsum :
        (s.sum (fun _ => (1 : ZMod 2)))
          = (∑ e : Edge n, if p e then (1 : ZMod 2) else 0) := by
      -- `sum_filter` moves the predicate from the finset into the summand.
      -- (`∑ e : Edge n, _` is `Finset.univ.sum _`.)
      dsimp [s, p]
      rw [Finset.sum_filter]
    -- put it together
    calc
      (monoCount f : ZMod 2) = (s.card : ZMod 2) := by rw [hs]
      _ = s.sum (fun _ => (1 : ZMod 2)) := hCast
      _ = ∑ e : Edge n, (if p e then (1 : ZMod 2) else 0) := hsum
  calc
    (monoCount f : ZMod 2)
        = ∑ e : Edge n, (if Edge.monochromatic f e then (1 : ZMod 2) else 0) := hmono
    _ = ∑ e : Edge n, ((1 : ZMod 2) + bit (f (Edge.src e)) + bit (f (Edge.dst e))) := by
          apply Fintype.sum_congr
          intro e
          simpa using (monoIndicator_zmod2 (f := f) e)
    _ = (∑ _e : Edge n, (1 : ZMod 2))
          + (∑ e : Edge n, bit (f (Edge.src e)))
          + (∑ e : Edge n, bit (f (Edge.dst e))) := by
          -- distribute `sum` across `+`
          simp [add_left_comm, add_comm, Finset.sum_add_distrib]
    _ = (edgeCount n : ZMod 2)
          + (∑ e : Edge n, bit (f (Edge.src e)))
          + (∑ e : Edge n, bit (f (Edge.src e))) := by
          simp [edgeCount, sum_bit_src_eq_sum_bit_dst (f := f)]
    _ = (edgeCount n : ZMod 2) := by
          -- in characteristic 2, `x + x = 0`
          have hself :
              (∑ e : Edge n, bit (f (Edge.src e))) + (∑ e : Edge n, bit (f (Edge.src e))) = 0 := by
            simpa using
              (CharTwo.add_self_eq_zero (R := ZMod 2) (x := ∑ e : Edge n, bit (f (Edge.src e))))
          -- clean up the associativity
          simp [add_left_comm, add_comm, hself]

private lemma edgeCount_9 : edgeCount n = 3024 := by
  classical
  have : edgeCount n = (9 : Nat).descFactorial 4 := by
    have : Fintype.card (Edge n) = Fintype.card (Fin 4 ↪ Sym n) :=
      Fintype.card_congr
        { toFun := fun e => ⟨e.1, e.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro e; apply Subtype.ext; funext i; rfl
          right_inv := by intro x; ext i; rfl }
    have hcongr : edgeCount n = Fintype.card (Fin 4 ↪ Sym n) := by
      rwa [edgeCount]
    rw [hcongr]
    simp [Sym, n, Fintype.card_embedding_eq]
  exact this.trans (by decide : (9 : Nat).descFactorial 4 = 3024)

private lemma monoCount_even (f : Coloring9) : Even (monoCount f) := by
  have hcast : (monoCount f : ZMod 2) = 0 := by
    have hE : (edgeCount n : ZMod 2) = 0 := by
      simpa [edgeCount_9] using (show ((3024 : Nat) : ZMod 2) = 0 by decide)
    simpa [monoCount_zmod2_eq_edgeCount_zmod2 (f := f)] using hE
  exact (ZMod.natCast_eq_zero_iff_even (n := monoCount f)).1 hcast

private lemma monoCount_ge_606 (f : Coloring9) : 606 ≤ monoCount f := by
  have h605 : 605 ≤ monoCount f := monoCount_ge_605 (f := f)
  have hEven : Even (monoCount f) := monoCount_even (f := f)
  by_contra h606
  have hlt : monoCount f < 606 := Nat.lt_of_not_ge h606
  have hle : monoCount f ≤ 605 := Nat.le_of_lt_succ (by simpa using hlt)
  have hm : monoCount f = 605 := le_antisymm hle h605
  have : Even 605 := by simpa [hm] using hEven
  exact (by decide : ¬ Even 605) this

theorem monoFraction_ge_101_504 (f : Coloring9) : (101 : ℚ) / 504 ≤ monoFraction f := by
  have h606 : (606 : ℚ) ≤ (monoCount f : ℚ) := by exact_mod_cast monoCount_ge_606 (f := f)
  have hE : (edgeCount n : ℚ) = 3024 := by exact_mod_cast edgeCount_9
  have hEpos : (0 : ℚ) ≤ (edgeCount n : ℚ) := by exact_mod_cast (Nat.zero_le (edgeCount n))
  have hdiv : (606 : ℚ) / (edgeCount n : ℚ) ≤ monoFraction f := by
    simpa [monoFraction] using (div_le_div_of_nonneg_right h606 hEpos)
  have hred : (606 : ℚ) / (edgeCount n : ℚ) = (101 : ℚ) / 504 := by
    simp [hE, show (606 : ℚ) / 3024 = (101 : ℚ) / 504 by norm_num]
  simpa [hred] using hdiv

theorem monoFraction_gt_one_fifth (f : Coloring9) : (1 : ℚ) / 5 < monoFraction f := by
  have h := monoFraction_ge_101_504 (f := f)
  have hstrict : (1 : ℚ) / 5 < (101 : ℚ) / 504 := by norm_num
  exact lt_of_lt_of_le hstrict h

end N9

end Distributed2Coloring.LowerBound
