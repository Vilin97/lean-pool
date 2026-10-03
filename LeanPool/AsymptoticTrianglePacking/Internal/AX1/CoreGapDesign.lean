/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — from a *sub-triple design* to a near-regular family

`Nibble.AX1.uniform_triple_member` (`Nibble.CoreGapPrune`) turns **one** triple of pairwise uniform,
pairwise dense, scale-equalised vertex sets into one member of the family
`Nibble.AX1.HasNearRegularFamily` asks for.  This file performs the **assembly**: a finite list of
such triples whose tripartite graphs are pairwise edge-disjoint, and which together carry enough
edges, is a near-regular family.

* `Nibble.AX1.designBad` — the exceptional-edge budget `4ε₂(ab + ac + bc)` of one sub-triple.
* `Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` — **the bridge**.  All hypotheses are
  explicit real inequalities about the sub-triples; no probability and no regularity argument is
  left inside it.

Together with `Nibble.AX1.hasNearRegularFamily_of_reduced` and the `ν₃*` bookkeeping of
`Nibble.CoreGapPackingSplit` this reduces `Nibble.AX1.ReducedFamilyResidual` to the purely
combinatorial problem of *constructing* such a design — see `Nibble.CoreGapGridResidual`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPrune
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularFamily

/-! # CoreGapDesign -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The exceptional-edge budget of a sub-triple at uniformity scale `ε₂`: the bound
`4ε₂(|A||B| + |A||C| + |B||C|)` of `Nibble.AX1.tripleGraph_near_regular`. -/
@[expose]
noncomputable def designBad (ε₂ : ℝ) (A B C : Finset V) : ℝ :=
  4 * ε₂ * ((#A : ℝ) * (#B : ℝ) + (#A : ℝ) * (#C : ℝ) + (#B : ℝ) * (#C : ℝ))

/-- **A sub-triple design for `G` at parameters `(ε, μ, η, d₀)`, with internal scales
`(ε₂, μ₂, t)`.**  This is the exact package of hypotheses that
`Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` turns into a near-regular family; it contains
no probability and no regularity argument, only explicit inequalities about the `k` sub-triples
`(A i, B i, C i)`, their common triangle-degree scales `d i` and the lower bounds `Elo i` for their
edge counts. -/
@[expose]
def IsSubTripleDesign (G : SimpleGraph V) [DecidableRel G.Adj] (ε μ η d₀ ε₂ μ₂ t : ℝ) (k : ℕ)
    (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ) : Prop :=
  0 < ε₂ ∧ ε₂ ≤ 1 ∧ 0 < t ∧ 0 ≤ η ∧ μ₂ ≤ μ ∧
  (∀ i < k, Disjoint (A i) (B i)) ∧
  (∀ i < k, Disjoint (A i) (C i)) ∧
  (∀ i < k, Disjoint (B i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (B i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (B i) (C i)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (B i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (C i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (B i) (C i) : ℝ)) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (C i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(C i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (C i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(C i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(B i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(B i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) - 2 * ε₂) * (#(A i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) + 2 * ε₂) * (#(A i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, d₀ ≤ d i) ∧ (∀ i < k, 0 ≤ d i) ∧
  (∀ i < k, 2 * t ≤ (μ - μ₂) * d i) ∧
  (∀ i < k, ∀ j < k, i ≠ j → ∀ x y,
    (tripleGraph G (A i) (B i) (C i)).Adj x y → ¬ (tripleGraph G (A j) (B j) (C j)).Adj x y) ∧
  (∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ)) ∧
  (∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * (Fintype.card V : ℝ)
    ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i))) ∧
  nu3star G ≤ (∑ i ∈ Finset.range k,
    (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2

/-- **The bridge from a sub-triple design to a near-regular family.**

A *design* consists of `k` triples `(A i, B i, C i)` of pairwise disjoint vertex sets which are

* pairwise `ε₂`-uniform of density at least `2ε₂`;
* *scale equalised*: the three triangle-degree scales of the triple agree with a common
  `d i ≥ d₀` to within `μ₂`, even after the `ε₂`-slack of the counting lemma;
* pairwise **edge-disjoint** as tripartite graphs;
* large: `Elo i` is a lower bound for the number of edges of the `i`-th tripartite graph, the
  exceptional edges produced by pruning are at most an `η`-fraction of what survives, and the
  surviving edges recover `3ν₃*(G) − 3ε|V|²`.

Then `G` has a near-regular family at `(ε, μ, η, d₀)`.  The members are the pruned tripartite
graphs `Nibble.AX1.prune (tripleGraph G (A i) (B i) (C i)) Badᵢ` of
`Nibble.AX1.uniform_triple_member`. -/
theorem hasNearRegularFamily_of_subTripleDesign
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε μ η d₀ ε₂ μ₂ t : ℝ}
    (k : ℕ) (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ)
    (hε₂ : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (ht : 0 < t) (hη : 0 ≤ η)
    (hdAB : ∀ i < k, Disjoint (A i) (B i))
    (hdAC : ∀ i < k, Disjoint (A i) (C i))
    (hdBC : ∀ i < k, Disjoint (B i) (C i))
    (huAB : ∀ i < k, G.IsUniform ε₂ (A i) (B i))
    (huAC : ∀ i < k, G.IsUniform ε₂ (A i) (C i))
    (huBC : ∀ i < k, G.IsUniform ε₂ (B i) (C i))
    (hρAB : ∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (B i) : ℝ))
    (hρAC : ∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (C i) : ℝ))
    (hρBC : ∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (B i) (C i) : ℝ))
    (hClo : ∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (C i) : ℝ) - ε₂)
      * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(C i) : ℝ))
    (hChi : ∀ i < k, ((G.edgeDensity (A i) (C i) : ℝ) + ε₂)
      * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(C i) : ℝ) ≤ (1 + μ₂) * d i)
    (hBlo : ∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
      * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(B i) : ℝ))
    (hBhi : ∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
      * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(B i) : ℝ) ≤ (1 + μ₂) * d i)
    (hAlo : ∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
      * ((G.edgeDensity (A i) (C i) : ℝ) - 2 * ε₂) * (#(A i) : ℝ))
    (hAhi : ∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
      * ((G.edgeDensity (A i) (C i) : ℝ) + 2 * ε₂) * (#(A i) : ℝ) ≤ (1 + μ₂) * d i)
    (hd₀ : ∀ i < k, d₀ ≤ d i) (hdnn : ∀ i < k, 0 ≤ d i) (hμ₂ : μ₂ ≤ μ)
    (hslack : ∀ i < k, 2 * t ≤ (μ - μ₂) * d i)
    (hpair : ∀ i < k, ∀ j < k, i ≠ j → ∀ x y,
      (tripleGraph G (A i) (B i) (C i)).Adj x y → ¬ (tripleGraph G (A j) (B j) (C j)).Adj x y)
    (hElo : ∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ))
    (hexc : ∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * (Fintype.card V : ℝ)
      ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i)))
    (hcover : nu3star G ≤ (∑ i ∈ Finset.range k,
      (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2) :
    HasNearRegularFamily G ε μ η d₀ := by
  classical
  -- the member attached to the `i`-th sub-triple
  have hmem : ∀ i : ℕ, ∃ Bad : Finset (Finset V), i < k →
      (((#Bad : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) ∧
        prune (tripleGraph G (A i) (B i) (C i)) Bad ≤ G ∧
        (∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2,
          (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)
            ≤ (1 + μ₂) * d i) ∧
        (∃ Exc : Finset (Finset V),
          ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * (Fintype.card V : ℝ) ∧
          ∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2, e ∉ Exc →
            (1 - μ₂) * d i - 2 * t
              ≤ (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)) ∧
        ((#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2) : ℕ) : ℝ)) := by
    intro i
    by_cases hi : i < k
    · obtain ⟨Bad, h1, h2, h3, h4, h5⟩ :=
        uniform_triple_member G (hdAB i hi) (hdAC i hi) (hdBC i hi) hε₂ hε₂1 ht
          (huAB i hi) (huAC i hi) (huBC i hi) (hρAB i hi) (hρAC i hi) (hρBC i hi)
          (hClo i hi) (hChi i hi) (hBlo i hi) (hBhi i hi) (hAlo i hi) (hAhi i hi)
      exact ⟨Bad, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Bad hBad using hmem
  refine ⟨k, fun i => prune (tripleGraph G (A i) (B i) (C i)) (Bad i), d, ?_, ?_, hd₀, ?_, ?_, ?_⟩
  · exact fun i hi => (hBad i hi).2.1
  · -- edge-disjointness
    intro i hi j hj hij x y hxi hxj
    exact hpair i hi j hj hij x y (prune_le _ _ hxi) (prune_le _ _ hxj)
  · -- upper bound on the triangle degrees
    intro i hi e he
    have h := (hBad i hi).2.2.1 e he
    have : (1 + μ₂) * d i ≤ (1 + μ) * d i := by
      have := hdnn i hi; nlinarith only [hμ₂, this]
    linarith only [h, this]
  · -- the exceptional set
    intro i hi
    obtain ⟨Exc, hExc, hlo⟩ := (hBad i hi).2.2.2.1
    refine ⟨Exc, ?_, ?_⟩
    · have hBadle : ((#(Bad i) : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) := (hBad i hi).1
      have hmono : (2 * ((#(Bad i) : ℕ) : ℝ) / t) * (Fintype.card V : ℝ)
          ≤ (2 * designBad ε₂ (A i) (B i) (C i) / t) * (Fintype.card V : ℝ) := by
        have hV : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
        have : 2 * ((#(Bad i) : ℕ) : ℝ) / t ≤ 2 * designBad ε₂ (A i) (B i) (C i) / t := by
          gcongr
        exact mul_le_mul_of_nonneg_right this hV
      have hsurv : Elo i - designBad ε₂ (A i) (B i) (C i)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) := by
        have h5 := (hBad i hi).2.2.2.2
        have := hElo i hi
        linarith only [hBadle, h5, this]
      have := hexc i hi
      have hη' : η * (Elo i - designBad ε₂ (A i) (B i) (C i))
          ≤ η * ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsurv hη
      linarith only [hExc, hmono, this, hη']
    · intro e he hne
      have h := hlo e he hne
      have := hslack i hi
      linarith only [h, this]
  · -- the covering bound
    refine le_trans hcover ?_
    have hterm : ∀ i ∈ Finset.range k,
        (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2)
              : ℕ) : ℝ) / 3 := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h5 := (hBad i hi).2.2.2.2
      have h1 := (hBad i hi).1
      have := hElo i hi
      linarith only [h5, h1, this]
    have := Finset.sum_le_sum hterm
    linarith only [this]

/-- **The bridge, in packaged form.** -/
theorem hasNearRegularFamily_of_isSubTripleDesign (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ ε₂ μ₂ t : ℝ} {k : ℕ} {A B C : ℕ → Finset V} {d Elo : ℕ → ℝ}
    (h : IsSubTripleDesign G ε μ η d₀ ε₂ μ₂ t k A B C d Elo) :
    HasNearRegularFamily G ε μ η d₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := h
  exact hasNearRegularFamily_of_subTripleDesign G k A B C d Elo h1 h2 h3 h4 h6 h7 h8 h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h5 h23 h24 h25 h26 h27

end Nibble.AX1
