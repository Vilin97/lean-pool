/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.LegalFiring
public import Mathlib.Tactic

/-!
# The burned set, without Dhar's algorithm

Dhar's burning algorithm takes `(G, D, q)` and returns the maximal valid set
`A ⊆ V(G) \ {q}`; the *burned* vertices are the complement of `A`.  Every use of
the algorithm in the divisorial-gonality literature is a use of exactly two of
its properties — maximality of `A`, and the rule "a vertex with fewer chips than
burned incident edges burns" — and both are available without running anything.

The dependency's `legal_set_union` says legal sets are closed under union,
so the maximal legal subset of `V \ {q}` is a `Finset.sup` over a powerset:

* `maximalLegal G D q` — the join of every legal `U ⊆ univ.erase q`;
* `burned G D q := (maximalLegal G D q)ᶜ` — the burned set.

The API below is the whole of Dhar that the tricycle campaign
(the accompanying analysis §4.1) ever uses:

* `legalSet_maximalLegal`, `subset_maximalLegal_of_legal` — maximality;
* `mem_burned_self`, `mem_burned_of_lt`, `mem_burned_of_subset_lt`,
  `mem_burned_of_mem_burned_adj` — the burning rule;
* `sum_burned_le_of_not_mem_burned` — the *converse* rule, which is what turns
  "`v` is unburned" into a chip count;
* `qReduced_iff_maximalLegal_eq_empty` — the fire consumes everything exactly
  when `D` is `q`-reduced;
* `mem_maximalLegal_of_qReduced` — **Lemma 3.5(a)** of van Dobben de
  Bruyn–Smit–van der Wegen, in full generality: a `q`-reduced divisor's own
  `q` is never burned by a fire started anywhere else.

No algorithm, no termination proof, no fuel.  `maximalLegal` is `noncomputable`
and is only ever used propositionally; never `decide` it (blueprint risk R2).
-/

@[expose] public section

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

/-! ## The maximal legal set -/

open Classical in
/-- **The maximal legal subset of `V \ {q}`**: the join of all of them.  It is
legal because legal sets are closed under union (`legal_set_union`). -/
noncomputable def maximalLegal (G : CFGraph) (D : CFDiv G) (q : G.V) :
    Finset G.V :=
  (((Finset.univ.erase q).powerset).filter (fun U => legalSet G D U)).sup id

/-- The burned set of `(G, D, q)`: the complement of the maximal legal set.
This is what Dhar's burning algorithm computes. -/
noncomputable def burned (G : CFGraph) (D : CFDiv G) (q : G.V) : Finset G.V :=
  (maximalLegal G D q)ᶜ

variable {D : CFDiv G} {q : G.V}

theorem maximalLegal_subset : maximalLegal G D q ⊆ Finset.univ.erase q := by
  classical
  refine Finset.sup_le ?_
  intro U hU
  simp only [Finset.mem_filter, Finset.mem_powerset] at hU
  exact hU.1

/-- The join of legal sets is legal. -/
theorem legalSet_maximalLegal : legalSet G D (maximalLegal G D q) := by
  classical
  refine Finset.sup_induction (legal_set_empty G D) (fun a ha b hb => legal_set_union G ha hb) ?_
  intro U hU
  simp only [Finset.mem_filter, Finset.mem_powerset] at hU
  exact hU.2

/-- Maximality: every legal set avoiding `q` is contained in `maximalLegal`. -/
theorem subset_maximalLegal_of_legal {U : Finset G.V} (hU : legalSet G D U)
    (hq : U ⊆ Finset.univ.erase q) : U ⊆ maximalLegal G D q := by
  classical
  refine Finset.le_sup (f := id) ?_
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hq, hU⟩

theorem not_mem_maximalLegal_self : q ∉ maximalLegal G D q := by
  intro hq
  have := maximalLegal_subset (D := D) (q := q) hq
  simp at this

/-! ## The burned set -/

@[simp] theorem mem_burned_iff (v : G.V) :
    v ∈ burned G D q ↔ v ∉ maximalLegal G D q := by
  simp [burned]

/-- The source of the fire is burned. -/
theorem mem_burned_self : q ∈ burned G D q := by
  simp [not_mem_maximalLegal_self]

/-- The edges from `v` into the burned set, as an integer. -/
theorem outdeg_maximalLegal (v : G.V) :
    outdegreeSet G (maximalLegal G D q) v
      = ∑ w ∈ burned G D q, (numEdges G v w : ℤ) := rfl

/-- **The converse burning rule.**  An unburned vertex can afford every one of
its edges into the fire. -/
theorem sum_burned_le_of_not_mem_burned {v : G.V} (hv : v ∉ burned G D q) :
    ∑ w ∈ burned G D q, (numEdges G v w : ℤ) ≤ D v := by
  have hmem : v ∈ maximalLegal G D q := by simpa using hv
  exact legalSet_maximalLegal v hmem

/-- **The burning rule.**  A vertex with fewer chips than burned incident edges
burns.  This is all of Dhar's algorithm that any proof here needs. -/
theorem mem_burned_of_lt {v : G.V}
    (h : D v < ∑ w ∈ burned G D q, (numEdges G v w : ℤ)) : v ∈ burned G D q := by
  by_contra hv
  exact absurd (sum_burned_le_of_not_mem_burned hv) (not_le.mpr h)

/-- The burning rule against any subset of the fire. -/
theorem mem_burned_of_subset_lt {v : G.V} {S : Finset G.V}
    (hS : S ⊆ burned G D q) (h : D v < ∑ w ∈ S, (numEdges G v w : ℤ)) :
    v ∈ burned G D q := by
  refine mem_burned_of_lt (lt_of_lt_of_le h ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Int.natCast_nonneg _

/-- The burning rule against one burned neighbour. -/
theorem mem_burned_of_mem_burned_adj {u v : G.V} (hu : u ∈ burned G D q)
    (h : D v < (numEdges G v u : ℤ)) : v ∈ burned G D q := by
  refine mem_burned_of_subset_lt (S := {u}) ?_ ?_
  · simpa using hu
  · simpa using h

/-- The burning rule against two distinct burned neighbours. -/
theorem mem_burned_of_two_adj {u u' v : G.V} (hu : u ∈ burned G D q)
    (hu' : u' ∈ burned G D q) (hne : u ≠ u')
    (h : D v < (numEdges G v u : ℤ) + (numEdges G v u' : ℤ)) :
    v ∈ burned G D q := by
  classical
  refine mem_burned_of_subset_lt (S := {u, u'}) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rwa [Finset.sum_pair hne]

/-! ## The fire consumes everything exactly on `q`-reduced divisors -/

theorem maximalLegal_eq_empty_iff :
    maximalLegal G D q = ∅ ↔
      ∀ S : Finset G.V, S ⊆ Finset.univ.erase q → S.Nonempty → ¬ legalSet G D S := by
  constructor
  · intro hEmpty S hS hSne hLegal
    have := subset_maximalLegal_of_legal hLegal hS
    rw [hEmpty] at this
    obtain ⟨x, hx⟩ := hSne
    simpa using this hx
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact h _ maximalLegal_subset ⟨x, hx⟩ legalSet_maximalLegal

/-- The `q`-reduced predicate of the chip-firing dependency says, verbatim, that
no nonempty subset of `V \ {q}` is legal.  Hence: the fire started at `q`
consumes the whole graph exactly when `D` is `q`-reduced. -/
theorem qReduced_iff_maximalLegal_eq_empty (hEff : qEffective q D) :
    qReduced G q D ↔ maximalLegal G D q = ∅ := by
  classical
  rw [maximalLegal_eq_empty_iff]
  constructor
  · rintro ⟨-, hred⟩ S hS hSne
    apply hred S (by
      intro hqS
      have := hS hqS
      simp at this) hSne
  · intro h
    refine ⟨hEff, ?_⟩
    intro S hS hSne
    exact h S (by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hxq
      exact hS (hxq ▸ hx)) hSne

theorem burned_eq_univ_iff (hEff : qEffective q D) :
    burned G D q = Finset.univ ↔ qReduced G q D := by
  rw [qReduced_iff_maximalLegal_eq_empty hEff, burned]
  constructor
  · intro h
    have := congrArg (fun S : Finset G.V => Sᶜ) h
    simpa using this
  · intro h
    rw [h, Finset.compl_empty]

/-! ## Lemma 3.5(a) of van Dobben de Bruyn–Smit–van der Wegen -/

/-- If the fire started at `w` leaves anything unburned, then a `q`-reduced
divisor's own base point `q` is among the survivors.

This is Lemma 3.5(a) of van Dobben de Bruyn–Smit–van der Wegen, in the
generality in which it is true: the maximal legal set is legal and nonempty, and
a `q`-reduced divisor admits no nonempty legal set avoiding `q`. -/
theorem mem_maximalLegal_of_qReduced (hred : qReduced G q D) {w : G.V}
    (hne : (maximalLegal G D w).Nonempty) : q ∈ maximalLegal G D w := by
  classical
  by_contra hq
  exact hred.2 (maximalLegal G D w) hq hne legalSet_maximalLegal

/-- The fire started at a chip-free vertex of a positive-rank divisor never
consumes the whole graph. -/
theorem maximalLegal_nonempty_of_rank_ge_one
    (hEff : effective D) (hrank : rank G D ≥ 1) {w : G.V} (hw : D w = 0) :
    (maximalLegal G D w).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  have hqEff : qEffective w D := fun v _ => hEff v
  have hred : qReduced G w D :=
    (qReduced_iff_maximalLegal_eq_empty hqEff).mpr hEmpty
  have := one_le_apply_of_q_reduced_of_rank_geq_one hred hrank
  omega

/-- **Lemma 3.5(a)**, assembled: for a positive-rank `q`-reduced divisor and a
chip-free vertex `w`, the vertex `q` is not burned by the fire started at `w`. -/
theorem not_mem_burned_of_qReduced
    (hEff : effective D) (hred : qReduced G q D) (hrank : rank G D ≥ 1)
    {w : G.V} (hw : D w = 0) : q ∉ burned G D w := by
  simpa using
    mem_maximalLegal_of_qReduced hred
      (maximalLegal_nonempty_of_rank_ge_one hEff hrank hw)

/-! ## Opacity

`maximalLegal` is a `Finset.sup` over the powerset of `univ.erase q`.  Left
reducible, any `isDefEq` check between two `x ∈ burned G D q` types whose
vertices are *closed* terms (a `Fin` numeral, a `Sum.inl`, a `Fin.mk`) falls
through congruence and starts evaluating `Finset.univ`, `List.erase` and
`instDecidableEqSum.decEq` on the subdivision vertex type. Since the
whole point of the design is that `maximalLegal` is used *propositionally only*
sealing both definitions costs nothing and makes every such
comparison structural.  Everything above this line is stated and proved before
the seal; nothing below may unfold either definition. -/

attribute [irreducible] maximalLegal burned

end Utilities.Gonality
