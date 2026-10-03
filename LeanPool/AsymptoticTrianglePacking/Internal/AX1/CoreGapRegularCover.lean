/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the *covering* criterion for a near-regular family, and the cluster structure

`Nibble.AX1.HasNearRegularFamily G ε μ η d₀` (`Nibble.CoreGapRegularFamily`) mentions the fractional
optimum `ν₃*(G)`.  This file supplies the tool that discharges that bookkeeping for a construction:
it is enough to *cover* the edges of `G` that lie in a triangle, all but `ε|V|²` of them, by an
edge-disjoint family of near-regular subgraphs.

* `Nibble.AX1.triangleSupport` — the subgraph of the edges lying in at least one triangle.  It has
  the same triangles as `G`, hence the same fractional optimum
  (`Nibble.AX1.nu3star_triangleSupport`).
* `Nibble.AX1.unionFamily` — the union of a family; for an edge-disjoint family its edge count is
  the sum of the members' edge counts (`Nibble.AX1.card_cliqueFinset_two_unionFamily`).
* `Nibble.AX1.hasNearRegularFamily_of_cover` — **the covering criterion**: `ν₃*` of the union of the
  family is at most a third of its edge count (`Nibble.YusterE.nu3star_le`), and the uncovered edges
  cost at most their number (`Nibble.AX1.nu3star_le_add_deleted`).  So a near-regular family
  covering all but `ε|V|²` of the triangle-carrying edges is a near-regular family in the sense of
  `Nibble.AX1.HasNearRegularFamily`, with **no reference to `ν₃*` in the hypotheses**.  Note that
  this criterion is only *sufficient*: see the discussion at the end of the file for why demanding
  such a covering of the whole triangle support is in general too strong, so that the residual
  itself must keep `ν₃*`.
* `Nibble.AX1.GoodTriple`, `Nibble.AX1.regularityReduced_triangle_parts`,
  `Nibble.AX1.triangleSupport_regularityReduced_goodTriple` — the cluster structure the residual has
  to exploit: every triangle of a regularity-reduced graph has its three vertices in three distinct
  parts, pairwise uniform and dense, and every edge of its triangle support joins two clusters of
  such a good triple.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularFamily

/-! # CoreGapRegularCover -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The triangle support -/

/-- The spanning subgraph of the edges of `G` that lie in at least one triangle. -/
@[expose]
noncomputable def triangleSupport (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V :=
  edgeSelect G (fun e => 0 < edgeTriangleDegree G e)

noncomputable instance instDecidableRelTriangleSupport (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (triangleSupport G).Adj :=
  instDecidableRelEdgeSelect G _

theorem triangleSupport_le (G : SimpleGraph V) [DecidableRel G.Adj] : triangleSupport G ≤ G :=
  edgeSelect_le _ _

/-- The triangle support has the same triangles as `G`: each edge of a triangle lies in one. -/
theorem cliqueFinset_three_triangleSupport (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleSupport G).cliqueFinset 3 = G.cliqueFinset 3 := by
  classical
  refine Finset.Subset.antisymm (SimpleGraph.cliqueFinset_mono _ (triangleSupport_le G)) ?_
  intro t ht
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht ⊢
  refine ⟨?_, ht.card_eq⟩
  intro a ha b hb hab
  refine ⟨ht.1 ha hb hab, ?_⟩
  refine Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr
    ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ht, ?_⟩⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

/-- Equal triangle hypergraphs give equal fractional optima. -/
theorem nu3star_congr_hypergraph (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj]
    [DecidableRel G₂.Adj] (h : triangleHypergraphE G₁ = triangleHypergraphE G₂) :
    nu3star G₁ = nu3star G₂ := by
  unfold nu3star
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨hnn, hzero, hcon⟩, rfl⟩
    exact ⟨w, ⟨hnn, by rwa [h] at hzero, by rwa [h] at hcon⟩, by rw [h]⟩
  · rintro ⟨w, ⟨hnn, hzero, hcon⟩, rfl⟩
    exact ⟨w, ⟨hnn, by rwa [← h] at hzero, by rwa [← h] at hcon⟩, by rw [h]⟩

/-- **The triangle support carries the whole fractional optimum.** -/
theorem nu3star_triangleSupport (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star (triangleSupport G) = nu3star G := by
  refine nu3star_congr_hypergraph _ _ ?_
  unfold triangleHypergraphE
  rw [cliqueFinset_three_triangleSupport]

/-! ### The union of a family -/

/-- The union of the first `k` members of a family of graphs. -/
def unionFamily (H : ℕ → SimpleGraph V) (k : ℕ) : SimpleGraph V where
  Adj x y := ∃ i, i < k ∧ (H i).Adj x y
  symm := ⟨by
    rintro x y ⟨i, hi, hadj⟩
    exact ⟨i, hi, hadj.symm⟩⟩
  loopless := ⟨by
    rintro x ⟨i, -, hadj⟩
    exact (H i).irrefl hadj⟩

noncomputable instance instDecidableRelUnionFamily (H : ℕ → SimpleGraph V) (k : ℕ) :
    DecidableRel (unionFamily H k).Adj := fun _ _ => Classical.dec _

omit [Fintype V] [DecidableEq V] in
theorem unionFamily_le {G : SimpleGraph V} {H : ℕ → SimpleGraph V} {k : ℕ}
    (hle : ∀ i < k, H i ≤ G) : unionFamily H k ≤ G := by
  rintro x y ⟨i, hi, hadj⟩
  exact hle i hi hadj

open Classical in
/-- The `2`-cliques of a union are the union of the `2`-cliques. -/
theorem cliqueFinset_two_unionFamily (H : ℕ → SimpleGraph V) (k : ℕ) :
    (unionFamily H k).cliqueFinset 2
      = (Finset.range k).biUnion (fun i => (H i).cliqueFinset 2) := by
  classical
  ext e
  constructor
  · intro he
    have hcard : e.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨i, hi, hadj⟩ := (pair_mem_cliqueFinset_two (unionFamily H k) hxy).mp he
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_range.mpr hi, (pair_mem_cliqueFinset_two (H i) hxy).mpr hadj⟩
  · intro he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    have hcard : e.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp hei).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    exact (pair_mem_cliqueFinset_two (unionFamily H k) hxy).mpr
      ⟨i, Finset.mem_range.mp hi, (pair_mem_cliqueFinset_two (H i) hxy).mp hei⟩

open Classical in
/-- For an edge-disjoint family, the edge count of the union is the sum of the edge counts. -/
theorem card_cliqueFinset_two_unionFamily (H : ℕ → SimpleGraph V) (k : ℕ)
    (hdisj : EdgeDisjointFamily H k) :
    (((unionFamily H k).cliqueFinset 2).card : ℝ)
      = ∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) := by
  classical
  have hd : ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => (H i).cliqueFinset 2) := by
    intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hei hej
    have hcard : e.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp hei).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij x y
      ((pair_mem_cliqueFinset_two (H i) hxy).mp hei)
      ((pair_mem_cliqueFinset_two (H j) hxy).mp hej)
  rw [cliqueFinset_two_unionFamily, Finset.card_biUnion hd]
  push_cast
  ring

/-! ### The covering criterion -/

open Classical in
/-- **The covering criterion.**  An edge-disjoint family of near-regular subgraphs of the triangle
support of `G`, covering all but at most `ε|V|²` of the edges of that support, is a near-regular
family for `G` in the sense of `Nibble.AX1.HasNearRegularFamily`.

Indeed the fractional optimum of `G` is that of its triangle support
(`Nibble.AX1.nu3star_triangleSupport`); passing from the support to the union of the family costs at
most the number of uncovered edges (`Nibble.AX1.nu3star_le_add_deleted`); and the fractional optimum
of the union is at most a third of its edge count (`Nibble.YusterE.nu3star_le`), which for an
edge-disjoint family is a third of the sum of the members' edge counts. -/
theorem hasNearRegularFamily_of_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ : ℝ} {k : ℕ} {H : ℕ → SimpleGraph V} {d : ℕ → ℝ} {D : Finset (Finset V)}
    (hle : ∀ i < k, H i ≤ triangleSupport G)
    (hdisj : EdgeDisjointFamily H k)
    (hd : ∀ i < k, d₀ ≤ d i)
    (hhi : ∀ i < k, ∀ e ∈ (H i).cliqueFinset 2,
      (edgeTriangleDegree (H i) e : ℝ) ≤ (1 + μ) * d i)
    (hlo : ∀ i < k, ∃ Exc : Finset (Finset V),
      (Exc.card : ℝ) ≤ η * (((H i).cliqueFinset 2).card : ℝ) ∧
      ∀ e ∈ (H i).cliqueFinset 2, e ∉ Exc →
        (1 - μ) * d i ≤ (edgeTriangleDegree (H i) e : ℝ))
    (hcov : ∀ e ∈ (triangleSupport G).cliqueFinset 2,
      e ∈ D ∨ ∃ i < k, e ∈ (H i).cliqueFinset 2)
    (hD : (D.card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    HasNearRegularFamily G ε μ η d₀ := by
  classical
  set W : SimpleGraph V := unionFamily H k with hW
  have hWle : W ≤ triangleSupport G := unionFamily_le hle
  have hsub : (triangleSupport G).cliqueFinset 2 \ W.cliqueFinset 2 ⊆ D := by
    intro e he
    rw [Finset.mem_sdiff] at he
    rcases hcov e he.1 with h | ⟨i, hi, hei⟩
    · exact h
    · exact absurd (by
        rw [cliqueFinset_two_unionFamily]
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hei⟩) he.2
  have hcnt : (((triangleSupport G).cliqueFinset 2 \ W.cliqueFinset 2).card : ℝ) ≤
      (D.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hdel := nu3star_le_add_deleted (triangleSupport G) W hWle
  have hWval : nu3star W ≤ ((W.cliqueFinset 2).card : ℝ) / 3 := nu3star_le W
  have hWcard := card_cliqueFinset_two_unionFamily H k hdisj
  have hsum : ((W.cliqueFinset 2).card : ℝ) / 3
      = ∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) / 3 := by
    rw [hWcard, Finset.sum_div]
  refine ⟨k, H, d, fun i hi => le_trans (hle i hi) (triangleSupport_le G), hdisj, hd, hhi, hlo, ?_⟩
  have hGS : nu3star (triangleSupport G) = nu3star G := nu3star_triangleSupport G
  rw [← hGS, ← hsum]
  linarith only [hD, hcnt, hdel, hWval]

/-! ### The cluster structure of a regularity-reduced graph -/

/-- A **good triple** of clusters: three distinct parts of `P`, pairwise `ep`-uniform in `G` with
density at least `de`.  These are the triples that can carry a triangle of the reduced graph. -/
@[expose]
def GoodTriple (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    (ep de : ℝ) (U W X : Finset V) : Prop :=
  U ∈ P.parts ∧ W ∈ P.parts ∧ X ∈ P.parts ∧ U ≠ W ∧ U ≠ X ∧ W ≠ X ∧
    G.IsUniform ep U W ∧ de ≤ G.edgeDensity U W ∧
    G.IsUniform ep U X ∧ de ≤ G.edgeDensity U X ∧
    G.IsUniform ep W X ∧ de ≤ G.edgeDensity W X

/-- **Every triangle of a regularity-reduced graph lives on a good triple of clusters**: its three
vertices lie in three distinct parts, which are pairwise uniform and dense. -/
theorem regularityReduced_triangle_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {x y z : V}
    (hxy : (G.regularityReduced P ep de).Adj x y)
    (hxz : (G.regularityReduced P ep de).Adj x z)
    (hyz : (G.regularityReduced P ep de).Adj y z) :
    ∃ U W X : Finset V, GoodTriple G P ep de U W X ∧ x ∈ U ∧ y ∈ W ∧ z ∈ X := by
  obtain ⟨-, U, hU, W, hW, hxU, hyW, hUW, huUW, hdUW⟩ := hxy
  obtain ⟨-, U', hU', X, hX, hxU', hzX, hUX, huUX, hdUX⟩ := hxz
  obtain ⟨-, W', hW', X', hX', hyW', hzX', hWX, huWX, hdWX⟩ := hyz
  cases P.disjoint.elim hU hU' (Finset.not_disjoint_iff.2 ⟨x, hxU, hxU'⟩)
  cases P.disjoint.elim hW hW' (Finset.not_disjoint_iff.2 ⟨y, hyW, hyW'⟩)
  cases P.disjoint.elim hX hX' (Finset.not_disjoint_iff.2 ⟨z, hzX, hzX'⟩)
  exact ⟨U, W, X, ⟨hU, hW, hX, hUW, hUX, hWX, huUW, hdUW, huUX, hdUX, huWX, hdWX⟩,
    hxU, hyW, hzX⟩

/-- **Every edge that the covering residual has to cover lies on a good triple.**  An edge of the
triangle support of a regularity-reduced graph joins two clusters of a good triple, the third
cluster containing a common neighbour. -/
theorem triangleSupport_regularityReduced_goodTriple (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {x y : V}
    (hxy : (triangleSupport (G.regularityReduced P ep de)).Adj x y) :
    ∃ U W X : Finset V, ∃ z : V, GoodTriple G P ep de U W X ∧ x ∈ U ∧ y ∈ W ∧ z ∈ X ∧
      (G.regularityReduced P ep de).Adj x z ∧ (G.regularityReduced P ep de).Adj y z := by
  classical
  set G' : SimpleGraph V := G.regularityReduced P ep de with hG'
  obtain ⟨hadj, hpos⟩ := hxy
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨hclique, hsub⟩ := ht
  have hx : x ∈ t := hsub (by simp)
  have hy : y ∈ t := hsub (by simp)
  have hxy' : x ≠ y := hadj.ne
  have hcard : ({x, y} : Finset V).card = 2 := Finset.card_pair hxy'
  obtain ⟨z, hzt, hz⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, by intro h; rw [h] at hcard; rw [hclique.card_eq] at hcard; norm_num at hcard⟩)
  have hzx : z ≠ x := by intro h; exact hz (by simp [h])
  have hzy : z ≠ y := by intro h; exact hz (by simp [h])
  have hxz : G'.Adj x z := hclique.1 hx hzt (Ne.symm hzx)
  have hyz : G'.Adj y z := hclique.1 hy hzt (Ne.symm hzy)
  obtain ⟨U, W, X, hgood, hxU, hyW, hzX⟩ :=
    regularityReduced_triangle_parts G P ep de hadj hxz hyz
  exact ⟨U, W, X, z, hgood, hxU, hyW, hzX, hxz, hyz⟩

/-! ### Why the covering criterion is not the residual

`Nibble.AX1.hasNearRegularFamily_of_cover` is a *sufficient* condition, and it is strictly stronger
than what is needed: requiring that *all but `ε|V|²`* of the triangle-carrying edges be covered by
near-regular classes is in general impossible.  Near-regularity forces a class inside a cluster
triple to carry roughly equally many edges in each of the triple's three pairs (the triangles of the
class are counted once from each pair), so a triple whose three pairs have very different densities
— say `1`, `1/10`, `1/10` — can have only about `3/10` of its edges covered, the rest of the dense
pair remaining uncovered even though each of its edges lies in a triangle.  For such a graph the
fractional optimum is correspondingly small, which is exactly why `Nibble.AX1.HasNearRegularFamily`
(and hence the residual `Nibble.AX1.ReducedFamilyResidual`) compares the covered edge count with
`ν₃*` rather than with the total number of edges.

The covering criterion remains useful as a *tool*: applied to a subgraph `G' ≤ G` together with
`Nibble.AX1.HasNearRegularFamily.mono_of_le`, it discharges the `ν₃*` bookkeeping whenever the
construction does cover the chosen subgraph. -/

end Nibble.AX1
