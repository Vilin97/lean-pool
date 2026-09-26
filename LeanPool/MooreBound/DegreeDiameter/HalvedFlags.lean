/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.Lemma21
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# The halved flag graph

This file defines the two kinds of partial flags and their compatibility
relation exactly as in the paper.  A partial flag is represented by a full
rank-indexed family in which ranks of the other parity are replaced by `⊥`.
The fixed endpoint ranks are retained; this does not change the objects and
makes even and odd parts jointly determine a complete flag definitionally.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- Keep the ranks congruent to `parity` modulo two and erase the others. -/
@[expose] def flagPart (parity : ℕ) (F : CompleteFlag K V n) :
    Fin (n + 1) → Submodule K V :=
  fun i ↦ if i.val % 2 = parity % 2 then F i else ⊥

/-- Partial complete flags supported on one parity of ranks. -/
@[expose]
def PartialFlag (parity : ℕ) :=
  {P : Fin (n + 1) → Submodule K V //
    ∃ F : CompleteFlag K V n, flagPart parity F = P}

/-- The subspaces at even ranks of some complete flag. -/
abbrev EvenPartialFlag := PartialFlag (K := K) (V := V) (n := n) 0
/-- The subspaces at odd ranks of some complete flag. -/
abbrev OddPartialFlag := PartialFlag (K := K) (V := V) (n := n) 1

namespace PartialFlag

instance {parity : ℕ} [Finite V] :
    Finite (PartialFlag (K := K) (V := V) (n := n) parity) := by
  let : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective
    (fun P : PartialFlag (K := K) (V := V) (n := n) parity ↦ P.1)
    Subtype.val_injective

@[ext]
theorem ext {parity : ℕ}
    {P Q : PartialFlag (K := K) (V := V) (n := n) parity}
    (h : ∀ i, P.1 i = Q.1 i) : P = Q := by
  apply Subtype.ext
  exact funext h

/-- The partial flag of a complete flag at the selected parity. -/
@[expose] def ofComplete (parity : ℕ) (F : CompleteFlag K V n) :
    PartialFlag (K := K) (V := V) (n := n) parity :=
  ⟨flagPart parity F, F, rfl⟩

@[simp]
theorem ofComplete_val (parity : ℕ) (F : CompleteFlag K V n) :
    (ofComplete parity F).1 = flagPart parity F := rfl

end PartialFlag

/-- An even and an odd partial flag are compatible when they are the two
parts of one complete flag. -/
@[expose] def Compatible (P : EvenPartialFlag (K := K) (V := V) (n := n))
    (Q : OddPartialFlag (K := K) (V := V) (n := n)) : Prop :=
  ∃ F : CompleteFlag K V n,
    PartialFlag.ofComplete 0 F = P ∧ PartialFlag.ofComplete 1 F = Q

theorem compatible_parts (F : CompleteFlag K V n) :
    Compatible (PartialFlag.ofComplete 0 F) (PartialFlag.ofComplete 1 F) :=
  ⟨F, rfl, rfl⟩

/-- Even and odd parts determine their common complete flag uniquely. -/
theorem compatible_unique
    {P : EvenPartialFlag (K := K) (V := V) (n := n)}
    {Q : OddPartialFlag (K := K) (V := V) (n := n)}
    {F G : CompleteFlag K V n}
    (hF : PartialFlag.ofComplete 0 F = P)
    (hF' : PartialFlag.ofComplete 1 F = Q)
    (hG : PartialFlag.ofComplete 0 G = P)
    (hG' : PartialFlag.ofComplete 1 G = Q) : F = G := by
  apply CompleteFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · have h := congrFun (congrArg Subtype.val (hF.trans hG.symm)) i
    simpa [PartialFlag.ofComplete, flagPart, hi] using h
  · have hi' : i.val % 2 = 1 := by omega
    have h := congrFun (congrArg Subtype.val (hF'.trans hG'.symm)) i
    simpa [PartialFlag.ofComplete, flagPart, hi'] using h

/-- The graph on even partial flags in which distinct flags are adjacent when
they have a common compatible odd partial flag. -/
def halvedFlagGraph : SimpleGraph (EvenPartialFlag (K := K) (V := V) (n := n)) :=
  SimpleGraph.fromRel fun P P' ↦
    ∃ Q : OddPartialFlag (K := K) (V := V) (n := n),
      Compatible P Q ∧ Compatible P' Q

theorem halvedFlagGraph_adj_iff
    {P P' : EvenPartialFlag (K := K) (V := V) (n := n)} :
    (halvedFlagGraph (K := K) (V := V) (n := n)).Adj P P' ↔
      P ≠ P' ∧ ∃ Q : OddPartialFlag (K := K) (V := V) (n := n),
        Compatible P Q ∧ Compatible P' Q := by
  rw [halvedFlagGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, ⟨Q, hPQ, hP'Q⟩ | ⟨Q, hP'Q, hPQ⟩⟩
    · exact ⟨hne, Q, hPQ, hP'Q⟩
    · exact ⟨hne, Q, hPQ, hP'Q⟩
  · rintro ⟨hne, Q, hPQ, hP'Q⟩
    exact ⟨hne, Or.inl ⟨Q, hPQ, hP'Q⟩⟩

theorem evenPart_eq_of_alternatingStep {s : Fin n}
    {F G : CompleteFlag K V n} (h : AlternatingStep K V s F G)
    (hs : (s.val + 1) % 2 = 1) :
    PartialFlag.ofComplete 0 F = PartialFlag.ofComplete 0 G := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · have hFG : F i = G i := h i (by omega)
    simpa [PartialFlag.ofComplete, flagPart, hi] using hFG
  · simp [PartialFlag.ofComplete, flagPart, hi]

theorem oddPart_eq_of_alternatingStep {s : Fin n}
    {F G : CompleteFlag K V n} (h : AlternatingStep K V s F G)
    (hs : (s.val + 1) % 2 = 0) :
    PartialFlag.ofComplete 1 F = PartialFlag.ofComplete 1 G := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 1
  · have hFG : F i = G i := h i (by omega)
    simpa [PartialFlag.ofComplete, flagPart, hi] using hFG
  · have hi' : i.val % 2 ≠ 1 := hi
    simp [PartialFlag.ofComplete, flagPart, hi']

/-- Two even parts separated by an odd step and then an even step have
extended graph distance at most one. -/
theorem halved_edist_le_one_of_parts
    (F₀ F₁ F₂ : CompleteFlag K V n)
    (heven : PartialFlag.ofComplete 0 F₀ = PartialFlag.ofComplete 0 F₁)
    (hodd : PartialFlag.ofComplete 1 F₁ = PartialFlag.ofComplete 1 F₂) :
    (halvedFlagGraph (K := K) (V := V) (n := n)).edist
      (PartialFlag.ofComplete 0 F₀) (PartialFlag.ofComplete 0 F₂) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases heq : PartialFlag.ofComplete 0 F₀ = PartialFlag.ofComplete 0 F₂
  · exact Or.inr heq
  · apply Or.inl
    rw [halvedFlagGraph_adj_iff]
    refine ⟨heq, PartialFlag.ofComplete 1 F₁, ?_, ?_⟩
    · exact ⟨F₁, heven.symm, rfl⟩
    · exact ⟨F₂, rfl, hodd.symm⟩

/-- A chain with at most unit extended distance at every step has distance at
most its number of steps. -/
theorem edist_chain_le {W : Type*} (G : SimpleGraph W) (P : ℕ → W) :
    ∀ m : ℕ, (∀ j < m, G.edist (P j) (P (j + 1)) ≤ 1) →
      G.edist (P 0) (P m) ≤ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro h
      calc
        G.edist (P 0) (P (m + 1)) ≤
            G.edist (P 0) (P m) + G.edist (P m) (P (m + 1)) :=
          G.edist_triangle
        _ ≤ (m : ℕ∞) + 1 :=
          add_le_add (ih fun j hj ↦ h j (Nat.lt_succ_of_lt hj)) (h m (Nat.lt_succ_self m))
        _ = (m + 1 : ℕ) := by simp

/-- The odd-first alternating route of Lemma 2.1 projects to a route of at
most `k` edges in the halved graph on a `(2*k+1)`-dimensional space. -/
theorem halvedFlagGraph_ediam_le (k : ℕ) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam ≤ (k : ℕ∞) := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro P P'
  obtain ⟨F, hF⟩ := P.property
  obtain ⟨F', hF'⟩ := P'.property
  have hPF : PartialFlag.ofComplete 0 F = P := by
    apply Subtype.ext
    exact hF
  have hPF' : PartialFlag.ofComplete 0 F' = P' := by
    apply Subtype.ext
    exact hF'
  obtain ⟨route, hroute₀, hrouteLast, hroute⟩ := alternating_route K V F F'
  let E : ℕ → EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) := fun j ↦
    if hj : j ≤ k then
      PartialFlag.ofComplete 0 (route ⟨2 * j, by omega⟩)
    else P
  have hchain : ∀ j < k,
      (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).edist
        (E j) (E (j + 1)) ≤ 1 := by
    intro j hj
    have hj₀ : j ≤ k := Nat.le_of_lt hj
    have hj₁ : j + 1 ≤ k := by omega
    let sOdd : Fin (2 * k + 1) := ⟨2 * j, by omega⟩
    let sEven : Fin (2 * k + 1) := ⟨2 * j + 1, by omega⟩
    have heven :
        PartialFlag.ofComplete 0 (route sOdd.castSucc) =
          PartialFlag.ofComplete 0 (route sOdd.succ) :=
      evenPart_eq_of_alternatingStep (hroute sOdd) (by simp [sOdd])
    have hodd :
        PartialFlag.ofComplete 1 (route sEven.castSucc) =
          PartialFlag.ofComplete 1 (route sEven.succ) :=
      oddPart_eq_of_alternatingStep (hroute sEven) (by simp [sEven]; omega)
    have hdist := halved_edist_le_one_of_parts
      (route sOdd.castSucc) (route sOdd.succ) (route sEven.succ) heven (by
        simpa [sOdd, sEven] using hodd)
    have hstart : sOdd.castSucc = ⟨2 * j, by omega⟩ := by
      apply Fin.ext
      simp [sOdd]
    have hend : sEven.succ = ⟨2 * (j + 1), by omega⟩ := by
      apply Fin.ext
      simp [sEven]
      omega
    rw [hstart, hend] at hdist
    simpa [E, hj₀, hj₁] using hdist
  have hE₀ : E 0 = P := by
    simp [E, hroute₀, hPF]
  have hlastPart :
      PartialFlag.ofComplete 0 (route ⟨2 * k, by omega⟩) =
        PartialFlag.ofComplete 0 F' := by
    let sLast : Fin (2 * k + 1) := Fin.last (2 * k)
    have h := evenPart_eq_of_alternatingStep (hroute sLast) (by simp [sLast])
    have hstart : sLast.castSucc = ⟨2 * k, by omega⟩ := by
      apply Fin.ext
      simp [sLast]
    have hend : sLast.succ = Fin.last (2 * k + 1) := by
      apply Fin.ext
      simp [sLast]
    rw [hstart, hend, hrouteLast] at h
    exact h
  have hEk : E k = P' := by
    simp [E, hlastPart, hPF']
  simpa [hE₀, hEk] using
    (edist_chain_le (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)) E k hchain)

end DegreeDiameter

end MooreBound
