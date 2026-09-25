/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.BurnedSet
public import Mathlib.Tactic

/-!
# A linear non-existence certificate for positive rank

Every gonality *upper* bound in this repository is witnessed by a divisor and a
firing script.  This module supplies the missing other half: a small, checkable
witness that a given divisor **does not** have positive rank.

The obstacle is that `qReduced` (in the chip-firing dependency) quantifies over
*all* subsets of `V \ {q}`, so deciding it directly costs `2^{n-1}`.  A
**burning order** replaces that quantifier by an `n`-step linear check:

> a list `π = (q = u₀, u₁, …)` containing every vertex, in which every entry
> after the first satisfies `D(uⱼ) < Σ_{i<j} numEdges G uⱼ uᵢ`.

Soundness (`qReduced_of_burningOrder`): given a nonempty `S ⊆ V \ {q}`, the
*least* index `j` with `uⱼ ∈ S` has all its predecessors outside `S`, so the
displayed inequality already exhibits a vertex of `S` that cannot afford to
fire.  The order is exactly a run of Dhar's burning algorithm recorded as data,
but nothing about the algorithm — termination, maximality, or otherwise — is
needed to check it.

The full certificate refuting `rank G D ≥ 1` is the triple `(v, x, π)`:

* a vertex `v`;
* a firing script `x` carrying `D` to `D' := D + prin G x`;
* a burning order `π` for `(D', v)`;

together with `D' ≥ 0 off v` and `D' v ≤ 0`
(`not_rank_ge_one_of_burningOrder`).  Every component is `decide`-shaped:
`BurningOrder` quantifies over `Fin π.length` and `G.V`, both finite.
-/

@[expose] public section

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

/-! ## Burning orders -/

/-- **A burning order** for `(D, v)`: a list of vertices whose head is `v`,
containing every vertex, in which every entry after the first has strictly fewer
chips than it has edges to its predecessors.

Repetitions are harmless; only the *first* occurrence of each vertex matters to
the soundness proof. -/
def BurningOrder (G : CFGraph) (D : CFDiv G) (v : G.V) (order : List G.V) :
    Prop :=
  order.head? = some v ∧ (∀ w : G.V, w ∈ order) ∧
    ∀ i : Fin order.length, 0 < i.val →
      D (order.get i) <
        ∑ w ∈ (order.take i.val).toFinset, (numEdges G (order.get i) w : ℤ)

instance (D : CFDiv G) (v : G.V) (order : List G.V) :
    Decidable (BurningOrder G D v order) := by
  unfold BurningOrder
  infer_instance

/-- **Soundness of a burning order.**  It certifies `q`-reducedness, replacing
the `2^{n-1}` subset quantifier of `qReduced` by an `n`-step check. -/
theorem qReduced_of_burningOrder {D : CFDiv G} {v : G.V} {order : List G.V}
    (hEff : qEffective v D) (h : BurningOrder G D v order) :
    qReduced G v D := by
  classical
  obtain ⟨hHead, hAll, hStep⟩ := h
  refine ⟨hEff, ?_⟩
  intro S hS hSne hLegal
  -- The head of the list is `v`.
  have hget0 : ∀ h0 : 0 < order.length, order[0]'h0 = v := by
    intro h0
    have hsome : order[0]? = some v := by
      rw [← List.head?_eq_getElem?]; exact hHead
    rw [List.getElem?_eq_getElem h0] at hsome
    exact Option.some.inj hsome
  -- `S` meets the list, so there is a least index at which it does.
  have hExists : ∃ i : ℕ, ∃ h : i < order.length, order[i]'h ∈ S := by
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp (hAll x)
    exact ⟨i, hi, by rw [hget]; exact hx⟩
  let P : ℕ → Prop := fun i => ∃ h : i < order.length, order[i]'h ∈ S
  have hP : ∃ i, P i := hExists
  obtain ⟨hjlt, hjS⟩ : P (Nat.find hP) := Nat.find_spec hP
  -- The head is `v`, which is not in `S`, so the least index is positive.
  have hjpos : 0 < Nat.find hP := by
    rcases Nat.eq_zero_or_pos (Nat.find hP) with hzero | hpos
    · exfalso
      have hmem := hjS
      have hidx : order[Nat.find hP]'hjlt = order[0]'(by omega) := by
        congr 1
      rw [hidx, hget0] at hmem
      have := hS hmem
      simp at this
    · exact hpos
  -- Every predecessor of the least index lies outside `S`, by minimality.
  have hPred : (order.take (Nat.find hP)).toFinset
      ⊆ Finset.univ.filter (fun x => x ∉ S) := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hi
    have hilt : i < Nat.find hP := lt_of_lt_of_le hi (min_le_left _ _)
    have hiOrder : i < order.length := lt_of_lt_of_le hi (min_le_right _ _)
    have hgetEq : order[i]'hiOrder = x := by
      rw [← hget, List.getElem_take]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hxS
    exact absurd ⟨hiOrder, by rw [hgetEq]; exact hxS⟩ (Nat.find_min hP hilt)
  have hstep := hStep ⟨Nat.find hP, hjlt⟩ hjpos
  simp only [List.get_eq_getElem] at hstep
  have hlt : D (order[Nat.find hP]'hjlt) < outdegreeSet G S (order[Nat.find hP]'hjlt) := by
    rw [outdeg_S_eq_sum_filter]
    exact lt_of_lt_of_le hstep
      (Finset.sum_le_sum_of_subset_of_nonneg hPred fun _ _ _ => Int.natCast_nonneg _)
  exact (not_lt_of_ge (hLegal _ hjS)) hlt

/-! ## The non-existence certificate -/

/-- **The certificate refuting positive rank.**  A vertex `v`, a script `x`, and
a burning order for `D + prin G x` at `v` whose divisor is effective off `v` and
carries no chip at `v`.

The proof is two lines of divisor bookkeeping on top of
`qReduced_of_burningOrder`: linear equivalence preserves rank, and a `q`-reduced
divisor of positive rank carries a chip at `q`
(`one_le_apply_of_q_reduced_of_rank_geq_one`). -/
theorem not_rank_ge_one_of_burningOrder
    {D : CFDiv G} {v : G.V} {x : firingScript G} {order : List G.V}
    (hEff : qEffective v (D + prin G x))
    (hOrder : BurningOrder G (D + prin G x) v order)
    (hzero : (D + prin G x) v ≤ 0) : ¬ (rank G D ≥ 1) := by
  intro hrank
  have hequiv : linearEquiv G D (D + prin G x) := by
    show (D + prin G x) - D ∈ principalDivisors G
    rw [principal_iff_eq_prin]
    exact ⟨x, by ring⟩
  have hrank' : rank G (D + prin G x) ≥ 1 := by
    rwa [← Utilities.rank_eq_of_linear_equiv G hequiv]
  have hred : qReduced G v (D + prin G x) := qReduced_of_burningOrder hEff hOrder
  have := one_le_apply_of_q_reduced_of_rank_geq_one hred hrank'
  omega

/-- Packaged form: the data of a certificate, bundled so that a generated table
can carry one row per divisor. -/
structure RankZeroCertificate (G : CFGraph) (D : CFDiv G) where
  /-- The base point of the reduction. -/
  vertex : G.V
  /-- The firing script carrying `D` to its `vertex`-reduced representative. -/
  script : firingScript G
  /-- A burning order recording a run of Dhar's algorithm as data. -/
  order : List G.V

namespace RankZeroCertificate

variable {D : CFDiv G} (c : RankZeroCertificate G D)

/-- The reduced divisor the certificate claims to produce. -/
def reduced : CFDiv G := D + prin G c.script

/-- Everything the certificate must satisfy, as one decidable proposition. -/
def Valid : Prop :=
  qEffective c.vertex c.reduced ∧
    BurningOrder G c.reduced c.vertex c.order ∧
    c.reduced c.vertex ≤ 0

instance : Decidable c.Valid := by
  unfold Valid qEffective
  infer_instance

theorem not_rank_ge_one (h : c.Valid) :
    ¬ (rank G D ≥ 1) :=
  not_rank_ge_one_of_burningOrder h.1 h.2.1 h.2.2

end RankZeroCertificate

end Utilities.Gonality
