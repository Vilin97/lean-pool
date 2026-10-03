/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — Yuster (edge-based) : the triangle hypergraph for EDGE-disjoint packing

Standalone, Mathlib-only. The **correct** triangle hypergraph for the Yuster route to AX1
(`ν₃*−ν₃ = o(n²)`): Paper III §2.2 defines the fractional triangle packing by the per-edge
constraint
(total weight through every edge ≤ 1), so `ν₃` is the maximum number of **edge-disjoint** triangles.

Accordingly the ground set is the edges of `G`, represented as `2`-element vertex subsets, and
each triangle contributes the hyperedge of its three edges (`t.powersetCard 2`). A MATCHING of this
hypergraph is a set of triangles sharing no edge, i.e. an edge-disjoint triangle packing = `ν₃`.
(The earlier `Nibble.Yuster.triangleHypergraph = G.cliqueFinset 3` is the VERTEX-clique hypergraph,
whose matchings are vertex-disjoint triangles — a different quantity, superseded for AX1.)

Using `2`-subsets instead of `Sym2` keeps `3`-uniformity clean: `|t.powersetCard 2| = C(3,2) = 3`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Bound

/-! # Edge-based triangle hypergraph -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **edge-based triangle hypergraph**: ground set = edges of `G` (as `2`-subsets), hyperedges =
the three edges of each triangle. Its matchings are the edge-disjoint triangle packings (`ν₃`). -/
@[expose] def triangleHypergraphE : Finset (Finset (Finset V)) :=
  (G.cliqueFinset 3).image (fun t => t.powersetCard 2)

/-- **The edge-based triangle hypergraph is 3-uniform** (every triangle has exactly three edges). -/
theorem triangleHypergraphE_uniform : IsUniform (triangleHypergraphE G) 3 := by
  intro e he
  rw [triangleHypergraphE, Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  simp [Finset.card_powersetCard, ht.card_eq]

/-- **Y2 (edge-based) — codegree ≤ 1.** Two distinct edges lie in at most one common triangle (they
determine its three vertices), so the edge-based triangle hypergraph has codegree `≤ 1`. This is the
`CodegreeBounded H (μd)` input the nibble wants — here in its sharpest form. -/
theorem triangleHypergraphE_codegree_le_one {e e' : Finset V} (hne : e ≠ e') :
    codegree (triangleHypergraphE G) e e' ≤ 1 := by
  rw [codegree]
  have key : ∀ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T ∧ e' ∈ T),
      T = (e ∪ e').powersetCard 2 := by
    intro T hT
    rw [Finset.mem_filter, triangleHypergraphE, Finset.mem_image] at hT
    obtain ⟨⟨s, hs, rfl⟩, heT, he'T⟩ := hT
    rw [SimpleGraph.mem_cliqueFinset_iff] at hs
    rw [Finset.mem_powersetCard] at heT he'T
    have hsub : e ∪ e' ⊆ s := Finset.union_subset heT.1 he'T.1
    have hne_card : (e ∩ e').card < 2 := by
      rcases Nat.lt_or_ge (e ∩ e').card 2 with h | h
      · exact h
      · exfalso
        have h2 : (e ∩ e').card = 2 :=
          le_antisymm (heT.2 ▸ Finset.card_le_card Finset.inter_subset_left) h
        have hee : e ∩ e' = e :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [heT.2, h2])
        have hee' : e ∩ e' = e' :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [he'T.2, h2])
        exact hne (hee ▸ hee')
    have hcard3 : (e ∪ e').card = 3 := by
      have hle : (e ∪ e').card ≤ 3 := hs.card_eq ▸ Finset.card_le_card hsub
      have hadd := Finset.card_union_add_card_inter e e'
      rw [heT.2, he'T.2] at hadd
      omega
    have hes : e ∪ e' = s :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hs.card_eq, hcard3])
    rw [hes]
  rw [Finset.card_le_one]
  intro T hT T' hT'
  rw [key T hT, key T' hT']

omit [Fintype V] [DecidableEq V] in
/-- Membership in a set of card `≥ 2` is witnessed by a `2`-subset. -/
theorem mem_iff_mem_powersetCard_two {u : Finset V} (hu : 2 ≤ u.card) (x : V) :
    x ∈ u ↔ ∃ e ∈ u.powersetCard 2, x ∈ e := by
  classical
  constructor
  · intro hx
    have hne : (u.erase x).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega
    obtain ⟨y, hy⟩ := hne
    have hyu : y ∈ u := Finset.mem_of_mem_erase hy
    have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
    refine ⟨{x, y}, ?_, Finset.mem_insert_self x {y}⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hyu),
      Finset.card_pair hxy⟩
  · rintro ⟨e, he, hxe⟩
    exact (Finset.mem_powersetCard.mp he).1 hxe

omit [Fintype V] [DecidableEq V] in
/-- **Faithful representation.** The triangle→edges map `t ↦ t.powersetCard 2` is injective on sets
of card `≥ 2`; hence distinct triangles give distinct hyperedges, and matchings of
`triangleHypergraphE` correspond to edge-disjoint triangle packings. -/
theorem powersetCard_two_inj {s t : Finset V} (hs : 2 ≤ s.card) (ht : 2 ≤ t.card)
    (h : s.powersetCard 2 = t.powersetCard 2) : s = t := by
  classical
  ext x
  rw [mem_iff_mem_powersetCard_two hs, mem_iff_mem_powersetCard_two ht, h]

/-- **Y3-edge — degree = number of triangles through the edge.** The degree of a vertex `e`
(an edge)
in the edge-based triangle hypergraph equals the number of triangles of `G` having `e` among their
three edges. Szemerédi regularity makes these counts (nearly) uniform — the near-regularity input to
the nibble. -/
theorem triangleHypergraphE_degree (e : Finset V) :
    degree (triangleHypergraphE G) e
      = ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2)).card := by
  have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2)
      ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2) : Set (Finset V)) := by
    intro s hs t ht hst
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, SimpleGraph.mem_cliqueFinset_iff] at hs ht
    exact powersetCard_two_inj (by have := hs.1.card_eq; omega) (by have := ht.1.card_eq; omega) hst
  rw [Hypergraph.degree, ← Finset.card_image_of_injOn hinj]
  congr 1
  ext T
  simp only [Finset.mem_filter, triangleHypergraphE, Finset.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, heT⟩
    exact ⟨t, ⟨ht, heT⟩, rfl⟩
  · rintro ⟨t, ⟨ht, heT⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, heT⟩

/-- **Y4 — the integral triangle-packing number `ν₃(G)`**: the maximum size of a matching of the
edge-based triangle hypergraph, i.e. the maximum number of edge-disjoint triangles. -/
@[expose] noncomputable def nu3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact ((triangleHypergraphE G).powerset.filter
    (fun M => IsMatching (triangleHypergraphE G) M)).sup Finset.card

/-- **Y4 — the nibble output lower-bounds `ν₃`.** Any matching of the triangle hypergraph
witnesses a
lower bound on `ν₃`. `NibbleTheorem` produces a large matching, hence a large `ν₃`. -/
theorem nu3_ge {M : Finset (Finset (Finset V))}
    (hM : IsMatching (triangleHypergraphE G) M) : M.card ≤ nu3 G := by
  classical
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hM.subset, hM⟩

/-- A **fractional triangle packing**: nonnegative weights on the triangle hyperedges with total
weight through every edge `≤ 1` (Paper III §2.2). -/
@[expose] def IsFracPacking (w : Finset (Finset V) → ℝ) : Prop :=
  (∀ T, 0 ≤ w T) ∧ (∀ T ∉ triangleHypergraphE G, w T = 0)
    ∧ ∀ e : Finset V, ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T ≤ 1

/-- **Y4 — the fractional triangle-packing number `ν₃*(G)`.** -/
@[expose] noncomputable def nu3star (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {x : ℝ | ∃ w, IsFracPacking G w ∧ x = ∑ T ∈ triangleHypergraphE G, w T}

/-- The fractional-packing value set is bounded above by `|H|` (each weight is `≤ 1`). -/
theorem nu3star_bddAbove :
    BddAbove {x : ℝ | ∃ w, IsFracPacking G w ∧ x = ∑ T ∈ triangleHypergraphE G, w T} := by
  refine ⟨((triangleHypergraphE G).card : ℝ), ?_⟩
  rintro x ⟨w, ⟨hnn, _, hcon⟩, rfl⟩
  calc ∑ T ∈ triangleHypergraphE G, w T
      ≤ ∑ _T ∈ triangleHypergraphE G, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun T hT => ?_)
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t, ht, rfl⟩ := hT
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht
        -- pick an edge e ∈ t.powersetCard 2; then w T ≤ ∑ over T'∋e ≤ 1
        obtain ⟨e, he⟩ : (t.powersetCard 2).Nonempty := by
          rw [← Finset.card_pos, Finset.card_powersetCard, ht.card_eq]; decide
        refine le_trans (Finset.single_le_sum (f := w) (fun T' _ => hnn T') ?_) (hcon e)
        rw [Finset.mem_filter, triangleHypergraphE, Finset.mem_image]
        exact ⟨⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ht, rfl⟩, he⟩
    _ = ((triangleHypergraphE G).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Y4 — weak duality `ν₃ ≤ ν₃*`.** The indicator of a maximum matching is a fractional packing of
value `ν₃`, so `ν₃ ≤ ν₃*`. -/
theorem nu3_le_nu3star : (nu3 G : ℝ) ≤ nu3star G := by
  classical
  -- the maximum matching is attained
  have hne : ((triangleHypergraphE G).powerset.filter
      (fun M => IsMatching (triangleHypergraphE G) M)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨M, hMmem, hMsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hMmem
  have hMmatch : IsMatching (triangleHypergraphE G) M := hMmem.2
  -- indicator weight
  set w : Finset (Finset V) → ℝ := fun T => if T ∈ M then 1 else 0 with hw
  have hval : ∑ T ∈ triangleHypergraphE G, w T = (M.card : ℝ) := by
    simp only [hw]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hMmem.1]
  have hpack : IsFracPacking G w := by
    refine ⟨fun T => by simp only [hw]; split_ifs <;> norm_num, fun T hT => ?_, fun e => ?_⟩
    · have hnot : T ∉ M := fun h => hT (hMmem.1 h)
      simp [hw, hnot]
    · simp only [hw]
      rw [Finset.sum_boole]
      have : ((triangleHypergraphE G).filter (fun T => e ∈ T)).filter (fun T => T ∈ M)
          = M.filter (fun T => e ∈ T) := by
        ext T
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨_, heT⟩, hTM⟩; exact ⟨hTM, heT⟩
        · rintro ⟨hTM, heT⟩; exact ⟨⟨hMmem.1 hTM, heT⟩, hTM⟩
      rw [this]
      -- ≤ 1 : at most one matched hyperedge contains e
      have : (M.filter (fun T => e ∈ T)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [Finset.mem_filter] at hT hT'
        by_contra hne'
        exact (Finset.disjoint_left.mp (hMmatch.disjoint T hT.1 T' hT'.1 hne') hT.2) hT'.2
      exact_mod_cast this
  have hnu : (nu3 G : ℝ) = (M.card : ℝ) := by simp only [nu3]; rw [hMsup]
  rw [hnu, ← hval]
  exact le_csSup (nu3star_bddAbove G) ⟨w, hpack, rfl⟩

end Nibble.YusterE
