/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — triangle degrees inside a cluster triple

`Nibble.AX1.uniform_triple_codegree` (`Nibble.CoreGapUniformCodegree`) counts, for most pairs
`(x, y) ∈ A × B`, the common neighbours of `x` and `y` inside a third set `C`.  This file turns that
codegree count into a statement about the **triangle degrees** `Nibble.AX1.edgeTriangleDegree` of
the tripartite graph a cluster triple carries, which is the shape required by
`Nibble.AX1.HasNearRegularFamily`.

* `Nibble.AX1.edgeTriangleDegree_pair` — the triangle degree of an edge `{x, y}` is the number of
  common neighbours of `x` and `y`.
* `Nibble.AX1.tripleGraph` — the tripartite subgraph of `G` spanned by the three pairs of a triple
  `(U, W, X)` of pairwise disjoint finsets, and its symmetry under permuting the three parts.
* `Nibble.AX1.edgeTriangleDegree_tripleGraph` — for an edge between `U` and `W`, the triangle degree
  in `tripleGraph G U W X` is exactly the codegree into `X`.
* `Nibble.AX1.tripleGraph_near_regular_pair` — **near-regular triangle degrees on one pair of the
  triple**: all but `4ε|U||W|` of the edges between `U` and `W` have triangle degree
  `(d(U,X) ± ε)(d(W,X) ± 2ε)|X|`.
* `Nibble.AX1.tripleGraph_near_regular` — **the equalised triple**: if the three "scales"
  `d(U,X)d(W,X)|X|`, `d(U,W)d(W,X)|W|`, `d(U,W)d(U,X)|U|` all agree with a common `d` to within
  `μ/2`, then all but `12ε·m²` of the edges of `tripleGraph G U W X` have triangle degree in
  `[(1−μ)d, (1+μ)d]`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularFamily
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus


/-! # CoreGapUniformCodegree -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Counting edges fibrewise -/

/-- The number of pairs of a product satisfying a predicate, summed fibrewise. -/
theorem card_filter_product {α β : Type*} (s : Finset α) (t : Finset β)
    (P : α × β → Prop) [DecidablePred P] :
    #{e ∈ s ×ˢ t | P e} = ∑ x ∈ s, #{y ∈ t | P (x, y)} := by
  classical
  have hmem : ∀ e ∈ {e ∈ s ×ˢ t | P e}, e.1 ∈ s := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_product] at he
    exact he.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun x hx => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    subst h4; exact ⟨h2, h3⟩
  · intro p hp q hq h
    simp only [Finset.mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · intro y hy
    simp only [Finset.mem_filter] at hy
    exact ⟨(x, y), by simp [Finset.mem_filter, Finset.mem_product, hx, hy.1, hy.2], rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- The number of edges between two finsets is the sum over the first of the degrees into the
second. -/
theorem card_interedges_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    #(G.interedges s t) = ∑ x ∈ s, #{z ∈ t | G.Adj x z} := by
  classical
  simpa [SimpleGraph.interedges, Rel.interedges] using
    card_filter_product s t (fun e => G.Adj e.1 e.2)

omit [Fintype V] [DecidableEq V] in
/-- The edge density as a real number. -/
theorem edgeDensity_real (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    (G.edgeDensity s t : ℝ) = (#(G.interedges s t) : ℝ) / ((#s : ℝ) * (#t : ℝ)) := by
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  ring

/-! ### The one-sided degree lemmas -/

omit [Fintype V] [DecidableEq V] in
/-- **Few vertices have small degree into a large subset.**  If `(B, C)` is `ε`-uniform and
`C' ⊆ C` has `|C'| ≥ ε|C|`, then at most `ε|B|` vertices `y ∈ B` have fewer than `θ|C'|`
neighbours in `C'`, for any `θ ≤ d(B,C) − ε`. -/
theorem card_filter_lt_le (G : SimpleGraph V) [DecidableRel G.Adj] {B C C' : Finset V} {ε θ : ℝ}
    (hε : 0 < ε) (hu : G.IsUniform ε B C) (hC'sub : C' ⊆ C) (hC'card : (#C : ℝ) * ε ≤ (#C' : ℝ))
    (hθ : θ + ε ≤ (G.edgeDensity B C : ℝ)) :
    ((#{y ∈ B | ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < θ * (#C' : ℝ)} : ℕ) : ℝ) ≤ ε * (#B : ℝ) := by
  classical
  set S : Finset V := {y ∈ B | ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < θ * (#C' : ℝ)} with hS
  by_contra hcon
  push Not at hcon
  have hSsub : S ⊆ B := Finset.filter_subset _ _
  have hSpos : (0 : ℝ) < (#S : ℝ) := lt_of_le_of_lt (by positivity) hcon
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hSpos
  -- `C'` is nonempty, else the defining condition is `0 < 0`
  have hC'pos : (0 : ℝ) < (#C' : ℝ) := by
    rcases Nat.eq_zero_or_pos (#C') with h0 | hpos
    · exfalso
      obtain ⟨y, hy⟩ := hSne
      rw [hS, Finset.mem_filter] at hy
      have hsub : {z ∈ C' | G.Adj y z} ⊆ C' := Finset.filter_subset _ _
      have : #{z ∈ C' | G.Adj y z} = 0 := Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card hsub)
      rw [this, h0] at hy
      norm_num at hy
    · exact_mod_cast hpos
  -- uniformity applies
  have h1 : (#B : ℝ) * ε ≤ (#S : ℝ) := by linarith only [hcon]
  have huni := hu hSsub hC'sub h1 hC'card
  have hlow : (G.edgeDensity B C : ℝ) - ε < (G.edgeDensity S C' : ℝ) := by
    have := abs_lt.mp huni
    linarith only [this.1]
  -- but the density of `(S, C')` is less than `θ`
  have hcount : (#(G.interedges S C') : ℝ) < (#S : ℝ) * (θ * (#C' : ℝ)) := by
    have hsum : ((∑ y ∈ S, #{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < ∑ _y ∈ S, θ * (#C' : ℝ) := by
      push_cast
      refine Finset.sum_lt_sum_of_nonempty hSne ?_
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact hy.2
    rw [card_interedges_eq_sum]
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hden : (G.edgeDensity S C' : ℝ) < θ := by
    rw [edgeDensity_real]
    rw [div_lt_iff₀ (by positivity)]
    calc (#(G.interedges S C') : ℝ) < (#S : ℝ) * (θ * (#C' : ℝ)) := hcount
      _ = θ * ((#S : ℝ) * (#C' : ℝ)) := by ring
  linarith only [hθ, hlow, hden]

omit [Fintype V] [DecidableEq V] in
/-- **Few vertices have large degree into a large subset.**  The mirror image of
`Nibble.AX1.card_filter_lt_le`. -/
theorem card_filter_gt_le (G : SimpleGraph V) [DecidableRel G.Adj] {B C C' : Finset V} {ε θ : ℝ}
    (hε : 0 < ε) (hu : G.IsUniform ε B C) (hC'sub : C' ⊆ C) (hC'card : (#C : ℝ) * ε ≤ (#C' : ℝ))
    (hθ : (G.edgeDensity B C : ℝ) + ε ≤ θ) :
    ((#{y ∈ B | θ * (#C' : ℝ) < ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ)} : ℕ) : ℝ) ≤ ε * (#B : ℝ) := by
  classical
  set S : Finset V := {y ∈ B | θ * (#C' : ℝ) < ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ)} with hS
  by_contra hcon
  push Not at hcon
  have hSsub : S ⊆ B := Finset.filter_subset _ _
  have hSpos : (0 : ℝ) < (#S : ℝ) := lt_of_le_of_lt (by positivity) hcon
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hSpos
  have hC'pos : (0 : ℝ) < (#C' : ℝ) := by
    rcases Nat.eq_zero_or_pos (#C') with h0 | hpos
    · exfalso
      obtain ⟨y, hy⟩ := hSne
      rw [hS, Finset.mem_filter] at hy
      have hsub : {z ∈ C' | G.Adj y z} ⊆ C' := Finset.filter_subset _ _
      have : #{z ∈ C' | G.Adj y z} = 0 := Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card hsub)
      rw [this, h0] at hy
      norm_num at hy
    · exact_mod_cast hpos
  have h1 : (#B : ℝ) * ε ≤ (#S : ℝ) := by linarith only [hcon]
  have huni := hu hSsub hC'sub h1 hC'card
  have hhigh : (G.edgeDensity S C' : ℝ) < (G.edgeDensity B C : ℝ) + ε := by
    have := abs_lt.mp huni
    linarith only [this.2]
  have hcount : (#S : ℝ) * (θ * (#C' : ℝ)) < (#(G.interedges S C') : ℝ) := by
    have hsum : ∑ _y ∈ S, θ * (#C' : ℝ) < ((∑ y ∈ S, #{z ∈ C' | G.Adj y z} : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_lt_sum_of_nonempty hSne ?_
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact hy.2
    rw [card_interedges_eq_sum]
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hden : θ < (G.edgeDensity S C' : ℝ) := by
    rw [edgeDensity_real, lt_div_iff₀ (by positivity)]
    calc θ * ((#S : ℝ) * (#C' : ℝ)) = (#S : ℝ) * (θ * (#C' : ℝ)) := by ring
      _ < (#(G.interedges S C') : ℝ) := hcount
  linarith only [hθ, hhigh, hden]

/-! ### Ingredient 1: near-regular triangle degrees across a uniform triple -/

/-- The number of common neighbours of `x` and `y` inside `C`. -/
def codegreeIn (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) (x y : V) : ℕ :=
  #{z ∈ C | G.Adj x z ∧ G.Adj y z}

omit [Fintype V] [DecidableEq V] in
theorem codegreeIn_eq_card_filter (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (x y : V) : codegreeIn G C x y = #{z ∈ {z ∈ C | G.Adj x z} | G.Adj y z} := by
  rw [codegreeIn, Finset.filter_filter]

omit [Fintype V] [DecidableEq V] in
/-- **Ingredient 1 — per-edge triangle counting in a uniform triple.**  If `(A, C)` and `(B, C)`
are `ε`-uniform pairs of density at least `2ε`, then all but at most `4ε|A||B|` of the pairs
`(x, y) ∈ A × B` have

`(d(A,C) − ε)(d(B,C) − 2ε)|C| ≤ |N(x) ∩ N(y) ∩ C| ≤ (d(A,C) + ε)(d(B,C) + 2ε)|C|`,

i.e. the triangle degree of an edge of the pair `(A, B)` into `C` is already near-regular, at the
scale `d(A,C)·d(B,C)·|C|`.

The proof is the standard two-sided count: all but `2ε|A|` vertices `x ∈ A` have
`|N(x) ∩ C| = (d(A,C) ± ε)|C|` (`Nibble.AX1.card_filter_lt_le` with `C' = C`), and for such an `x`
the set `N(x) ∩ C` is large enough that uniformity of `(B, C)` applies to it, so all but `2ε|B|`
vertices `y ∈ B` have `|N(y) ∩ N(x) ∩ C| = (d(B,C) ± 2ε)|N(x) ∩ C|`. -/
theorem uniform_triple_codegree (G : SimpleGraph V) [DecidableRel G.Adj] {A B C : Finset V} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hAC : G.IsUniform ε A C) (hBC : G.IsUniform ε B C)
    (hdAC : 2 * ε ≤ (G.edgeDensity A C : ℝ)) (hdBC : 2 * ε ≤ (G.edgeDensity B C : ℝ)) :
    ((#{p ∈ A ×ˢ B | ¬ (((G.edgeDensity A C : ℝ) - ε) * ((G.edgeDensity B C : ℝ) - 2 * ε)
            * (#C : ℝ) ≤ (codegreeIn G C p.1 p.2 : ℝ) ∧
          (codegreeIn G C p.1 p.2 : ℝ) ≤ ((G.edgeDensity A C : ℝ) + ε)
            * ((G.edgeDensity B C : ℝ) + 2 * ε) * (#C : ℝ))} : ℕ) : ℝ)
      ≤ 4 * ε * (#A : ℝ) * (#B : ℝ) := by
  classical
  set dA : ℝ := (G.edgeDensity A C : ℝ) with hdA
  set dB : ℝ := (G.edgeDensity B C : ℝ) with hdB
  set Q : V × V → Prop := fun p => ¬ ((dA - ε) * (dB - 2 * ε) * (#C : ℝ)
      ≤ (codegreeIn G C p.1 p.2 : ℝ) ∧
    (codegreeIn G C p.1 p.2 : ℝ) ≤ (dA + ε) * (dB + 2 * ε) * (#C : ℝ)) with hQ
  have hCnn : (0 : ℝ) ≤ (#C : ℝ) := by positivity
  have hBnn : (0 : ℝ) ≤ (#B : ℝ) := by positivity
  have hAnn : (0 : ℝ) ≤ (#A : ℝ) := by positivity
  -- the two exceptional vertex sets in `A`
  set Alo : Finset V := {x ∈ A | ((#{z ∈ C | G.Adj x z} : ℕ) : ℝ) < (dA - ε) * (#C : ℝ)} with hAlo
  set Ahi : Finset V := {x ∈ A | (dA + ε) * (#C : ℝ) < ((#{z ∈ C | G.Adj x z} : ℕ) : ℝ)} with hAhi
  have hCC : (#C : ℝ) * ε ≤ (#C : ℝ) := by nlinarith only [hε1]
  have hAlocard : ((#Alo : ℕ) : ℝ) ≤ ε * (#A : ℝ) :=
    card_filter_lt_le G hε hAC (subset_refl C) hCC (by linarith)
  have hAhicard : ((#Ahi : ℕ) : ℝ) ≤ ε * (#A : ℝ) :=
    card_filter_gt_le G hε hAC (subset_refl C) hCC (by linarith)
  -- the good vertices of `A` have few bad partners in `B`
  have hgood : ∀ x ∈ A, x ∉ Alo → x ∉ Ahi →
      ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ 2 * ε * (#B : ℝ) := by
    intro x hxA hxlo hxhi
    set Cx : Finset V := {z ∈ C | G.Adj x z} with hCx
    have hCxsub : Cx ⊆ C := Finset.filter_subset _ _
    have hCxlo : (dA - ε) * (#C : ℝ) ≤ ((#Cx : ℕ) : ℝ) := by
      by_contra hc
      push Not at hc
      exact hxlo (by rw [hAlo, Finset.mem_filter]; exact ⟨hxA, hc⟩)
    have hCxhi : ((#Cx : ℕ) : ℝ) ≤ (dA + ε) * (#C : ℝ) := by
      by_contra hc
      push Not at hc
      exact hxhi (by rw [hAhi, Finset.mem_filter]; exact ⟨hxA, hc⟩)
    have hCxcard : (#C : ℝ) * ε ≤ ((#Cx : ℕ) : ℝ) := by nlinarith only [hdAC, hCxlo]
    set Blo : Finset V := {y ∈ B | ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) < (dB - 2 * ε) * (#Cx : ℝ)}
      with hBlo
    set Bhi : Finset V := {y ∈ B | (dB + 2 * ε) * (#Cx : ℝ) < ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ)}
      with hBhi
    have hBlocard : ((#Blo : ℕ) : ℝ) ≤ ε * (#B : ℝ) :=
      card_filter_lt_le G hε hBC hCxsub hCxcard (by linarith)
    have hBhicard : ((#Bhi : ℕ) : ℝ) ≤ ε * (#B : ℝ) :=
      card_filter_gt_le G hε hBC hCxsub hCxcard (by linarith)
    have hsub : {y ∈ B | Q (x, y)} ⊆ Blo ∪ Bhi := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hyB, hyQ⟩ := hy
      by_contra hc
      rw [Finset.mem_union] at hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have h1 : (dB - 2 * ε) * (#Cx : ℝ) ≤ ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) := by
        by_contra hcc
        push Not at hcc
        exact hc1 (by rw [hBlo, Finset.mem_filter]; exact ⟨hyB, hcc⟩)
      have h2 : ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) ≤ (dB + 2 * ε) * (#Cx : ℝ) := by
        by_contra hcc
        push Not at hcc
        exact hc2 (by rw [hBhi, Finset.mem_filter]; exact ⟨hyB, hcc⟩)
      have hcodeg : (codegreeIn G C x y : ℝ) = ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) := by
        rw [codegreeIn_eq_card_filter, hCx]
      apply hyQ
      constructor
      · rw [hcodeg]
        nlinarith only [hdBC, hCxlo, h1]
      · rw [hcodeg]
        nlinarith
    calc ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ ((#(Blo ∪ Bhi) : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((#Blo : ℕ) : ℝ) + ((#Bhi : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_union_le Blo Bhi
      _ ≤ 2 * ε * (#B : ℝ) := by linarith
  -- assemble
  rw [card_filter_product A B Q]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not A (fun x => x ∈ Alo ∪ Ahi)
    (fun x => ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ))]
  have hbad : ∑ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
      ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
    have hle : ∀ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ (#B : ℝ) := by
      intro x _
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
        ≤ ∑ _x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, (#B : ℝ) := Finset.sum_le_sum hle
      _ = ((#{x ∈ A | x ∈ Alo ∪ Ahi} : ℕ) : ℝ) * (#B : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
          have hs : {x ∈ A | x ∈ Alo ∪ Ahi} ⊆ Alo ∪ Ahi := by
            intro x hx; exact (Finset.mem_filter.mp hx).2
          have h1 : ((#{x ∈ A | x ∈ Alo ∪ Ahi} : ℕ) : ℝ) ≤ ((#(Alo ∪ Ahi) : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hs
          have h2 : ((#(Alo ∪ Ahi) : ℕ) : ℝ) ≤ ((#Alo : ℕ) : ℝ) + ((#Ahi : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_union_le Alo Ahi
          nlinarith
  have hgoodsum : ∑ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
      ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
    have hle : ∀ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)},
        ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ 2 * ε * (#B : ℝ) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_union] at hx
      push Not at hx
      exact hgood x hx.1 hx.2.1 hx.2.2
    calc ∑ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
        ≤ ∑ _x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, 2 * ε * (#B : ℝ) := Finset.sum_le_sum hle
      _ = ((#{x ∈ A | ¬ (x ∈ Alo ∪ Ahi)} : ℕ) : ℝ) * (2 * ε * (#B : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
          have h1 : ((#{x ∈ A | ¬ (x ∈ Alo ∪ Ahi)} : ℕ) : ℝ) ≤ (#A : ℝ) := by
            exact_mod_cast Finset.card_filter_le A _
          have h2 : (0 : ℝ) ≤ 2 * ε * (#B : ℝ) := by positivity
          linarith only [mul_le_mul_of_nonneg_right h1 h2]
  linarith

end Nibble.AX1

end


/-! # CoreGapTripleDegrees -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The triangle degree of an edge is a codegree -/

omit [Fintype V] in
/-- Three distinct vertices form a set of size three. -/
theorem card_triple (x y z : V) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    #({x, y, z} : Finset V) = 3 := by
  have hx : x ∉ ({y, z} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨h1, h2⟩
  have hy : y ∉ ({z} : Finset V) := by
    simp only [Finset.mem_singleton]; exact h3
  rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy, Finset.card_singleton]

/-- **The triangle degree of an edge is the number of common neighbours of its endpoints.** -/
theorem edgeTriangleDegree_pair (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hxy : G.Adj x y) :
    edgeTriangleDegree G {x, y} = #{z ∈ (univ : Finset V) | G.Adj x z ∧ G.Adj y z} := by
  classical
  set Z : Finset V := {z ∈ (univ : Finset V) | G.Adj x z ∧ G.Adj y z} with hZ
  have hmemZ : ∀ z, z ∈ Z ↔ (G.Adj x z ∧ G.Adj y z) := by
    intro z; rw [hZ]; simp
  have hset : (G.cliqueFinset 3).filter (fun t => ({x, y} : Finset V) ⊆ t)
      = Z.image (fun z => ({x, y, z} : Finset V)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hcl, hsub⟩
      have hx : x ∈ t := hsub (by simp)
      have hy : y ∈ t := hsub (by simp)
      have hcard : #(t \ ({x, y} : Finset V)) = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcl.card_eq,
          Finset.card_pair hxy.ne]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hzmem : z ∈ t \ ({x, y} : Finset V) := by rw [hz]; simp
      rw [Finset.mem_sdiff] at hzmem
      obtain ⟨hzt, hznot⟩ := hzmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hznot
      push Not at hznot
      have hxz : G.Adj x z := hcl.1 hx hzt (Ne.symm hznot.1)
      have hyz : G.Adj y z := hcl.1 hy hzt (Ne.symm hznot.2)
      refine ⟨z, (hmemZ z).mpr ⟨hxz, hyz⟩, ?_⟩
      have hsub3 : ({x, y, z} : Finset V) ⊆ t := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      exact Finset.eq_of_subset_of_card_le hsub3
        (by rw [hcl.card_eq, card_triple x y z hxy.ne hxz.ne hyz.ne])
    · rintro ⟨z, hzZ, hteq⟩
      have hteq' : ({x, y, z} : Finset V) = t := hteq
      subst hteq'
      obtain ⟨hxz, hyz⟩ := (hmemZ z).mp hzZ
      refine ⟨⟨?_, card_triple x y z hxy.ne hxz.ne hyz.ne⟩, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hab
            | assumption
            | exact hxy.symm
            | exact hxz.symm
            | exact hyz.symm
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> simp
  have heq : edgeTriangleDegree G {x, y}
      = #((G.cliqueFinset 3).filter (fun t => ({x, y} : Finset V) ⊆ t)) := rfl
  rw [heq, hset, Finset.card_image_of_injOn]
  intro z hz z' hz' h
  have h' : ({x, y, z} : Finset V) = {x, y, z'} := h
  have hzn : z ∉ ({x, y} : Finset V) := by
    obtain ⟨h1, h2⟩ := (hmemZ z).mp hz
    simp [h1.ne', h2.ne']
  have hmem : z ∈ ({x, y, z'} : Finset V) := by rw [← h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hzn
  push Not at hzn
  tauto

/-! ### The tripartite graph carried by a triple of parts -/

/-- The (symmetric) predicate "`x` and `y` lie in two different parts of the triple". -/
@[expose]
def crossAdj (U W X : Finset V) (x y : V) : Prop :=
  (x ∈ U ∧ y ∈ W) ∨ (x ∈ W ∧ y ∈ U) ∨ (x ∈ U ∧ y ∈ X) ∨ (x ∈ X ∧ y ∈ U) ∨
    (x ∈ W ∧ y ∈ X) ∨ (x ∈ X ∧ y ∈ W)

omit [Fintype V] [DecidableEq V] in
theorem crossAdj_symm {U W X : Finset V} {x y : V} (h : crossAdj U W X x y) :
    crossAdj U W X y x := by
  unfold crossAdj at h ⊢; tauto

/-- **The tripartite subgraph carried by a triple of parts**: the edges of `G` joining two
different parts of `(U, W, X)`. -/
@[expose]
def tripleGraph (G : SimpleGraph V) (U W X : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ crossAdj U W X x y
  symm := ⟨by
    rintro x y ⟨h1, h2⟩
    exact ⟨h1.symm, crossAdj_symm h2⟩⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance instDecidableRelTripleGraph (G : SimpleGraph V) (U W X : Finset V) :
    DecidableRel (tripleGraph G U W X).Adj := fun _ _ => Classical.dec _

omit [Fintype V] [DecidableEq V] in
theorem tripleGraph_le (G : SimpleGraph V) (U W X : Finset V) : tripleGraph G U W X ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
theorem tripleGraph_adj (G : SimpleGraph V) (U W X : Finset V) (x y : V) :
    (tripleGraph G U W X).Adj x y ↔ G.Adj x y ∧ crossAdj U W X x y := Iff.rfl

omit [Fintype V] [DecidableEq V] in
/-- The tripartite graph does not depend on the order of the three parts. -/
theorem tripleGraph_comm₁ (G : SimpleGraph V) (U W X : Finset V) :
    tripleGraph G U W X = tripleGraph G W U X := by
  ext x y
  simp only [tripleGraph_adj, crossAdj]
  tauto

omit [Fintype V] [DecidableEq V] in
/-- The tripartite graph does not depend on the order of the three parts. -/
theorem tripleGraph_comm₂ (G : SimpleGraph V) (U W X : Finset V) :
    tripleGraph G U W X = tripleGraph G U X W := by
  ext x y
  simp only [tripleGraph_adj, crossAdj]
  tauto

/-- **The triangle degree of a `U`–`W` edge of the triple is the codegree into `X`.** -/
theorem edgeTriangleDegree_tripleGraph (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {x y : V} (hx : x ∈ U)
    (hy : y ∈ W) (hadj : (tripleGraph G U W X).Adj x y) :
    edgeTriangleDegree (tripleGraph G U W X) {x, y} = codegreeIn G X x y := by
  classical
  rw [edgeTriangleDegree_pair _ hadj, codegreeIn]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hxz, hcx⟩, ⟨hyz, hcy⟩⟩
    refine ⟨?_, hxz, hyz⟩
    -- `z` is in a part different from `U` (via `x`) and different from `W` (via `y`)
    have hxW : x ∉ W := Finset.disjoint_left.mp hUW hx
    have hxX : x ∉ X := Finset.disjoint_left.mp hUX hx
    have hyU : y ∉ U := Finset.disjoint_right.mp hUW hy
    have hyX : y ∉ X := Finset.disjoint_left.mp hWX hy
    have hzUW : z ∈ W ∨ z ∈ X := by
      unfold crossAdj at hcx
      rcases hcx with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h2
      · exact absurd h1 hxW
      · exact Or.inr h2
      · exact absurd h1 hxX
      · exact absurd h1 hxW
      · exact absurd h1 hxX
    have hzUX : z ∈ U ∨ z ∈ X := by
      unfold crossAdj at hcy
      rcases hcy with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h1 hyU
      · exact Or.inl h2
      · exact absurd h1 hyU
      · exact absurd h1 hyX
      · exact Or.inr h2
      · exact absurd h1 hyX
    rcases hzUX with hzU | hzX
    · rcases hzUW with hzW | hzX
      · exact absurd hzW (Finset.disjoint_left.mp hUW hzU)
      · exact absurd hzX (Finset.disjoint_left.mp hUX hzU)
    · exact hzX
  · rintro ⟨hzX, hxz, hyz⟩
    exact ⟨⟨hxz, Or.inr (Or.inr (Or.inl ⟨hx, hzX⟩))⟩,
      ⟨hyz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hy, hzX⟩))))⟩⟩

/-! ### Near-regular triangle degrees on one pair of the triple -/

/-- **Ingredient 1, in triangle-degree form.**  If the pairs `(U, X)` and `(W, X)` are `ε`-uniform
of density at least `2ε`, then all but at most `4ε|U||W|` of the edges of `tripleGraph G U W X`
joining `U` to `W` have triangle degree `(d(U,X) ± ε)(d(W,X) ± 2ε)|X|`. -/
theorem tripleGraph_near_regular_pair (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hUXu : G.IsUniform ε U X) (hWXu : G.IsUniform ε W X)
    (hdUX : 2 * ε ≤ (G.edgeDensity U X : ℝ)) (hdWX : 2 * ε ≤ (G.edgeDensity W X : ℝ)) :
    ∃ Bad : Finset (Finset V), ((#Bad : ℕ) : ℝ) ≤ 4 * ε * (#U : ℝ) * (#W : ℝ) ∧
      ∀ x ∈ U, ∀ y ∈ W, (tripleGraph G U W X).Adj x y → ({x, y} : Finset V) ∉ Bad →
        ((G.edgeDensity U X : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε) * (#X : ℝ)
            ≤ (edgeTriangleDegree (tripleGraph G U W X) {x, y} : ℝ) ∧
          (edgeTriangleDegree (tripleGraph G U W X) {x, y} : ℝ)
            ≤ ((G.edgeDensity U X : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ) := by
  classical
  set Q : V × V → Prop := fun p => ¬ (((G.edgeDensity U X : ℝ) - ε)
      * ((G.edgeDensity W X : ℝ) - 2 * ε) * (#X : ℝ) ≤ (codegreeIn G X p.1 p.2 : ℝ) ∧
    (codegreeIn G X p.1 p.2 : ℝ) ≤ ((G.edgeDensity U X : ℝ) + ε)
      * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ)) with hQ
  have hcount := uniform_triple_codegree G hε hε1 hUXu hWXu hdUX hdWX
  refine ⟨{p ∈ U ×ˢ W | Q p}.image (fun p => ({p.1, p.2} : Finset V)), ?_, ?_⟩
  · refine le_trans ?_ hcount
    exact_mod_cast Finset.card_image_le
  · intro x hx y hy hadj hnb
    have hpair : (x, y) ∉ {p ∈ U ×ˢ W | Q p} := by
      intro hmem
      exact hnb (Finset.mem_image.mpr ⟨(x, y), hmem, rfl⟩)
    have hQxy : ¬ Q (x, y) := by
      intro hQ'
      exact hpair (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hQ'⟩)
    simp only [hQ, not_not] at hQxy
    rw [edgeTriangleDegree_tripleGraph G hUW hUX hWX hx hy hadj]
    exact hQxy

/-! ### The equalised triple -/

/-- **Near-regular triangle degrees on a whole cluster triple.**  Suppose the three pairs of the
triple `(U, W, X)` are `ε`-uniform of density at least `2ε`, and that the three triangle-degree
scales `d(U,X)d(W,X)|X|` (for the `U`–`W` edges), `d(U,W)d(W,X)|W|` (for the `U`–`X` edges) and
`d(U,W)d(U,X)|U|` (for the `W`–`X` edges) all lie in `[(1−μ)d, (1+μ)d]`, even after the `ε`-slack of
`Nibble.AX1.tripleGraph_near_regular_pair` is taken into account.  Then all but at most
`4ε(|U||W| + |U||X| + |W||X|)` of the edges of the tripartite graph `tripleGraph G U W X` have
triangle degree in `[(1−μ)d, (1+μ)d]`.

This is the near-regular member the Haxell–Rödl construction attaches to a cluster triple, before
the exceptional edges are deleted; the equalisation hypotheses are what the sparsification of the
three pairs to a common density is for. -/
theorem tripleGraph_near_regular (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {ε μ d : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hUWu : G.IsUniform ε U W) (hUXu : G.IsUniform ε U X) (hWXu : G.IsUniform ε W X)
    (hdUW : 2 * ε ≤ (G.edgeDensity U W : ℝ)) (hdUX : 2 * ε ≤ (G.edgeDensity U X : ℝ))
    (hdWX : 2 * ε ≤ (G.edgeDensity W X : ℝ))
    (hXlo : (1 - μ) * d ≤ ((G.edgeDensity U X : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#X : ℝ))
    (hXhi : ((G.edgeDensity U X : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ)
      ≤ (1 + μ) * d)
    (hWlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#W : ℝ))
    (hWhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#W : ℝ)
      ≤ (1 + μ) * d)
    (hUlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity U X : ℝ) - 2 * ε)
      * (#U : ℝ))
    (hUhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity U X : ℝ) + 2 * ε) * (#U : ℝ)
      ≤ (1 + μ) * d) :
    ∃ Bad : Finset (Finset V),
      ((#Bad : ℕ) : ℝ) ≤ 4 * ε * ((#U : ℝ) * (#W : ℝ) + (#U : ℝ) * (#X : ℝ)
        + (#W : ℝ) * (#X : ℝ)) ∧
      ∀ e ∈ (tripleGraph G U W X).cliqueFinset 2, e ∉ Bad →
        (1 - μ) * d ≤ (edgeTriangleDegree (tripleGraph G U W X) e : ℝ) ∧
          (edgeTriangleDegree (tripleGraph G U W X) e : ℝ) ≤ (1 + μ) * d := by
  classical
  set T : SimpleGraph V := tripleGraph G U W X with hT
  have hT2 : tripleGraph G U X W = T := (tripleGraph_comm₂ G U W X).symm
  have hT3 : tripleGraph G W X U = T := by
    rw [hT, tripleGraph_comm₁ G U W X, tripleGraph_comm₂ G W U X]
  have hcXW : (G.edgeDensity X W : ℝ) = (G.edgeDensity W X : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have hcWU : (G.edgeDensity W U : ℝ) = (G.edgeDensity U W : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have hcXU : (G.edgeDensity X U : ℝ) = (G.edgeDensity U X : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  obtain ⟨B1, hB1card, hB1⟩ :=
    tripleGraph_near_regular_pair G hUW hUX hWX hε hε1 hUXu hWXu hdUX hdWX
  obtain ⟨B2, hB2card, hB2⟩ :=
    tripleGraph_near_regular_pair G hUX hUW (Disjoint.symm hWX) hε hε1 hUWu
      ((SimpleGraph.isUniform_comm G).mp hWXu) hdUW (by rw [hcXW]; exact hdWX)
  obtain ⟨B3, hB3card, hB3⟩ :=
    tripleGraph_near_regular_pair G hWX (Disjoint.symm hUW) (Disjoint.symm hUX) hε hε1
      ((SimpleGraph.isUniform_comm G).mp hUWu) ((SimpleGraph.isUniform_comm G).mp hUXu)
      (by rw [hcWU]; exact hdUW) (by rw [hcXU]; exact hdUX)
  refine ⟨B1 ∪ B2 ∪ B3, ?_, ?_⟩
  · have h12 : ((#(B1 ∪ B2) : ℕ) : ℝ) ≤ ((#B1 : ℕ) : ℝ) + ((#B2 : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_union_le B1 B2
    have h123 : ((#(B1 ∪ B2 ∪ B3) : ℕ) : ℝ) ≤ ((#(B1 ∪ B2) : ℕ) : ℝ) + ((#B3 : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_union_le (B1 ∪ B2) B3
    have hUWn : (0 : ℝ) ≤ (#U : ℝ) * (#W : ℝ) := by positivity
    nlinarith [hB1card, hB2card, hB3card]
  · intro e he hnb
    have hn1 : e ∉ B1 := fun h => hnb (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hn2 : e ∉ B2 := fun h => hnb (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hn3 : e ∉ B3 := fun h => hnb (Finset.mem_union_right _ h)
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hadj : T.Adj x y := (pair_mem_cliqueFinset_two T hxy).mp he
    have hpc : ({x, y} : Finset V) = {y, x} := Finset.pair_comm x y
    have hcross : crossAdj U W X x y := hadj.2
    rcases hcross with ⟨hxU, hyW⟩ | ⟨hxW, hyU⟩ | ⟨hxU, hyX⟩ | ⟨hxX, hyU⟩ | ⟨hxW, hyX⟩ | ⟨hxX, hyW⟩
    · obtain ⟨h1, h2⟩ := hB1 x hxU y hyW hadj hn1
      exact ⟨by linarith, by linarith⟩
    · rw [hpc]
      rw [hpc] at hn1
      obtain ⟨h1, h2⟩ := hB1 y hyU x hxW hadj.symm hn1
      exact ⟨by linarith, by linarith⟩
    · have hadj2 : (tripleGraph G U X W).Adj x y := by rw [hT2]; exact hadj
      obtain ⟨h1, h2⟩ := hB2 x hxU y hyX hadj2 hn2
      rw [edgeTriangleDegree_congr_graph hT2] at h1 h2
      rw [hcXW] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · rw [hpc]
      rw [hpc] at hn2
      have hadj2 : (tripleGraph G U X W).Adj y x := by rw [hT2]; exact hadj.symm
      obtain ⟨h1, h2⟩ := hB2 y hyU x hxX hadj2 hn2
      rw [edgeTriangleDegree_congr_graph hT2] at h1 h2
      rw [hcXW] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · have hadj3 : (tripleGraph G W X U).Adj x y := by rw [hT3]; exact hadj
      obtain ⟨h1, h2⟩ := hB3 x hxW y hyX hadj3 hn3
      rw [edgeTriangleDegree_congr_graph hT3] at h1 h2
      rw [hcWU, hcXU] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · rw [hpc]
      rw [hpc] at hn3
      have hadj3 : (tripleGraph G W X U).Adj y x := by rw [hT3]; exact hadj.symm
      obtain ⟨h1, h2⟩ := hB3 y hyW x hxX hadj3 hn3
      rw [edgeTriangleDegree_congr_graph hT3] at h1 h2
      rw [hcWU, hcXU] at h1 h2
      exact ⟨by linarith, by linarith⟩

end Nibble.AX1
