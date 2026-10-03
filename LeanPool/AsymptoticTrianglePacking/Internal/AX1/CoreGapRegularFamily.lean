/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the near-regular *family* form of the AX1 structural residual

`Nibble.AX1.RegularDecompAt` (`Nibble.CoreGapRegularDecomp`) asks for an edge *colouring* whose
colour classes have near-regular triangle degrees and together carry `3ν₃*(G) − o(|V|²)` edges.
Colourings are an awkward object to construct; what a regularity argument actually produces is a
*family of edge-disjoint subgraphs*.  This file

* defines `Nibble.AX1.HasNearRegularFamily G ε μ η d₀` — the same requirement, phrased for a family
  `H : ℕ → SimpleGraph V` of pairwise edge-disjoint subgraphs of `G`;
* turns such a family into a colouring (`Nibble.AX1.familyColoring`,
  `Nibble.AX1.colorPart_familyColoring`), so that
  `Nibble.AX1.regularDecompAt_of_family` reduces `RegularDecompAt` to the family form, and
  `Nibble.AX1.hasNearRegularFamily_of_regularDecomp` gives the converse: nothing is lost;
* records the two structural moves the regularity route needs:
  - `Nibble.AX1.HasNearRegularFamily.mono_of_le` — a family for a spanning subgraph `G' ≤ G` is a
    family for `G`, at a cost equal to the loss of `ν₃*`;
  - `Nibble.AX1.hasNearRegularFamily_of_few_triangles` — the empty family already works for
    triangle-poor graphs (Mathlib's triangle removal lemma, via
    `Nibble.AX1.nu3star_le_of_few_triangles`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapAX1
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal


/-! # CoreGapRemoval -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Counting the deleted edges -/

/-- The `2`-cliques lost when passing to a subgraph are at most the edges lost: the endpoint map
`Sym2 V → Finset V` sends the deleted edges onto the deleted `2`-cliques. -/
theorem card_clique2_sdiff_le (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ) := by
  classical
  have hsub : G'.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hle
  have hsurj : Set.SurjOn (fun e : Sym2 V => e.toFinset)
      ((G.edgeFinset \ G'.edgeFinset : Finset (Sym2 V)) : Set (Sym2 V))
      ((G.cliqueFinset 2 \ G'.cliqueFinset 2 : Finset (Finset V)) : Set (Finset V)) := by
    intro f hf
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff]
      at hf
    obtain ⟨hfG, hfG'⟩ := hf
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hfG.card_eq
    have hadj : G.Adj a b := hfG.1 (by simp) (by simp) hab
    have hnadj : ¬ G'.Adj a b := by
      intro h
      refine hfG' ⟨?_, Finset.card_pair hab⟩
      simpa using SimpleGraph.isClique_pair.mpr (fun _ => h)
    refine ⟨s(a, b), ?_, ?_⟩
    · simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      exact ⟨hadj, hnadj⟩
    · ext x; simp [Sym2.mem_toFinset]
  have hcard := Finset.card_le_card_of_surjOn _ hsurj
  have hsd : (G.edgeFinset \ G'.edgeFinset).card = G.edgeFinset.card - G'.edgeFinset.card :=
    Finset.card_sdiff_of_subset hsub
  have hle' : G'.edgeFinset.card ≤ G.edgeFinset.card := Finset.card_le_card hsub
  rw [hsd] at hcard
  have h2 : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ ((G.edgeFinset.card - G'.edgeFinset.card : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hle'] at h2
  exact h2

/-- A triangle-free graph has fractional triangle packing number `0`. -/
theorem nu3star_eq_zero_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) : nu3star G ≤ 0 := by
  have hemp : G.cliqueFinset 3 = ∅ := SimpleGraph.cliqueFinset_eq_empty_iff.mpr h
  have := nu3star_le_card_triangles G
  rwa [hemp, Finset.card_empty, Nat.cast_zero] at this

/-! ### The removal branch -/

/-- **The removal branch.**  A graph with fewer than `triangleRemovalBound(ε)·|V|³` triangles has
`ν₃* ≤ ε|V|²`.

Mathlib's triangle removal lemma produces a triangle-free spanning subgraph `G'` obtained by
deleting fewer than `ε|V|²` edges.  Since `G'` has no triangle, *every* triangle of `G` contains a
deleted edge, so the entire fractional packing is carried by the deleted edges, each of load at
most `1`. -/
theorem nu3star_le_of_few_triangles (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (hfew : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) :
    nu3star G ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hfew' : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℕ) ^ 3 := hfew
  obtain ⟨G', hle, hdec, hdel, hfree⟩ := SimpleGraph.triangle_removal (G := G) (ε := ε) hfew'
  have hzero : nu3star G' ≤ 0 := nu3star_eq_zero_of_cliqueFree G' hfree
  have hmain := nu3star_le_add_deleted G G' hle
  have hcnt := card_clique2_sdiff_le G G' hle
  have hdel' : (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ)
      < ε * (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast hdel
  linarith only [hzero, hmain, hcnt, hdel']

/-- **The removal branch, as a packing-gap bound.**  For every `ε > 0` there is `κ > 0` such that
every graph with fewer than `κ|V|³` triangles has packing gap at most `ε|V|²`. -/
theorem gap_le_of_few_triangles (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        ((G.cliqueFinset 3).card : ℝ) < κ * (Fintype.card V : ℝ) ^ 3 →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  refine ⟨SimpleGraph.triangleRemovalBound ε, SimpleGraph.triangleRemovalBound_pos hε, ?_⟩
  intro V _ _ G _ hfew
  have h1 := nu3star_le_of_few_triangles G hfew
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith only [h1]

/-! ### The residual, restricted to triangle-rich graphs -/

/-- **The core packing-gap statement at parameters `(ε, δ)`, for triangle-rich graphs.**  As
`Nibble.AX1.CoreGapAt ε δ`, but only for graphs with at least `κ|V|³` triangles. -/
def CoreGapAtRich (ε δ κ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    (∀ x : V, G.degree x = 0 ∨ δ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
    κ * (Fintype.card V : ℝ) ^ 3 ≤ ((G.cliqueFinset 3).card : ℝ) →
    ε * (Fintype.card V : ℝ) ^ 2 < nu3star G →
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual restricted to triangle-rich graphs**, at the removal-lemma threshold. -/
def CoreGapRichResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → CoreGapAtRich ε δ (SimpleGraph.triangleRemovalBound ε)

/-- Lowering the richness threshold strengthens the statement. -/
theorem CoreGapAtRich.mono_kappa {ε δ κ κ' : ℝ} (h : CoreGapAtRich ε δ κ) (hκ : κ ≤ κ') :
    CoreGapAtRich ε δ κ' := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, fun V _ _ G _ hV hdeg hrich hval => hmain V G hV hdeg ?_ hval⟩
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 := by positivity
  nlinarith only [hκ, hrich, hn]

/-- **The reduction.**  The full core residual follows from its triangle-rich restriction: the
triangle-poor instances are discharged outright by the removal branch. -/
theorem coreGapResidual_of_rich (h : CoreGapRichResidual) : CoreGapResidual := by
  intro ε hε δ hδ
  obtain ⟨n₀, hmain⟩ := h ε hε δ hδ
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg hval
  rcases lt_or_ge ((G.cliqueFinset 3).card : ℝ)
    (SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) with hfew | hrich
  · have h1 := nu3star_le_of_few_triangles G hfew
    have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
    linarith only [h1]
  · exact hmain V G hV hdeg hrich hval

/-- **The converse.**  The restricted residual is a weakening of the full one, so the two are
equivalent: no strength has been smuggled in. -/
theorem rich_of_coreGapResidual (h : CoreGapResidual) : CoreGapRichResidual := by
  intro ε hε δ hδ
  obtain ⟨n₀, hmain⟩ := h ε hε δ hδ
  exact ⟨n₀, fun V _ _ G _ hV hdeg _ hval => hmain V G hV hdeg hval⟩

/-- **AX1 from the triangle-rich residual.** -/
theorem ax1_of_coreGapRichResidual (h : CoreGapRichResidual) : AX1Statement :=
  ax1_of_coreGapResidual (coreGapResidual_of_rich h)

end Nibble.AX1

end






/-! # WeightedNibble -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The maximum in the definition of `ν₃` is attained: there is a triangle packing of size
exactly `ν₃ G`. -/
theorem exists_maximum_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset (Finset V)), IsMatching (triangleHypergraphE G) M ∧ M.card = nu3 G := by
  classical
  set S := (triangleHypergraphE G).powerset.filter
    (fun M => IsMatching (triangleHypergraphE G) M) with hS
  have hne : S.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨M, hMS, hsup⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  rw [hS, Finset.mem_filter] at hMS
  exact ⟨M, hMS.2, hsup.symm⟩

/-- Every triangle of `G` shares an edge with a maximum packing: otherwise it could be added. -/
theorem exists_mem_of_maximum_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (Finset V))} (hM : IsMatching (triangleHypergraphE G) M)
    (hcard : M.card = nu3 G) {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G) :
    ∃ e ∈ M.biUnion id, e ∈ T := by
  classical
  by_contra hcon
  push Not at hcon
  have hdisj : ∀ m ∈ M, Disjoint T m := by
    intro m hm
    rw [Finset.disjoint_left]
    intro e heT hem
    exact hcon e (Finset.mem_biUnion.mpr ⟨m, hm, hem⟩) heT
  have hTcard : T.card = 3 := triangleHypergraphE_uniform G T hT
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTM : T ∉ M := by
    intro hTM
    obtain ⟨e, he⟩ := hTne
    exact (Finset.disjoint_left.mp (hdisj T hTM) he) he
  have hM' : IsMatching (triangleHypergraphE G) (insert T M) := by
    refine ⟨Finset.insert_subset hT hM.subset, ?_⟩
    intro e he f hf hef
    rw [Finset.mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact absurd rfl hef
      · exact hdisj f hf
    · rcases hf with rfl | hf
      · exact (hdisj e he).symm
      · exact hM.disjoint e he f hf hef
  have hle : (insert T M).card ≤ nu3 G := nu3_ge G hM'
  rw [Finset.card_insert_of_notMem hTM, hcard] at hle
  omega

/-- **`ν₃* ≤ 3·ν₃`.**  The `3ν₃` edges covered by a maximum triangle packing form a triangle cover,
and the total weight of any fractional packing is at most the number of edges in a cover. -/
theorem nu3star_le_three_nu3 (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G ≤ 3 * (nu3 G : ℝ) := by
  classical
  obtain ⟨M, hM, hcard⟩ := exists_maximum_packing G
  set F : Finset (Finset V) := M.biUnion id with hF
  have hFcard : (F.card : ℝ) ≤ 3 * (nu3 G : ℝ) := by
    have h1 : F.card ≤ ∑ m ∈ M, (id m).card := Finset.card_biUnion_le
    have h2 : ∑ m ∈ M, (id m).card = 3 * M.card := by
      simp only [id_eq]
      rw [Finset.sum_congr rfl (fun m hm => triangleHypergraphE_uniform G m (hM.subset hm)),
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h2, hcard] at h1
    exact_mod_cast h1
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨hnn, -, hcon⟩ := hw
  have key : ∀ T ∈ triangleHypergraphE G,
      w T ≤ ∑ e ∈ F, (if e ∈ T then w T else 0) := by
    intro T hT
    obtain ⟨e₀, he₀F, he₀T⟩ := exists_mem_of_maximum_packing G hM hcard hT
    calc w T = (if e₀ ∈ T then w T else 0) := by simp [he₀T]
      _ ≤ ∑ e ∈ F, (if e ∈ T then w T else 0) := by
          refine Finset.single_le_sum (f := fun e => if e ∈ T then w T else 0) ?_ he₀F
          intro e _
          by_cases h : e ∈ T <;> simp [h, hnn T]
  calc ∑ T ∈ triangleHypergraphE G, w T
      ≤ ∑ T ∈ triangleHypergraphE G, ∑ e ∈ F, (if e ∈ T then w T else 0) :=
        Finset.sum_le_sum key
    _ = ∑ e ∈ F, ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ e ∈ F, ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T :=
        Finset.sum_congr rfl (fun e _ => by rw [Finset.sum_filter])
    _ ≤ ∑ _e ∈ F, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcon e)
    _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 3 * (nu3 G : ℝ) := hFcard

/-- `|E(G)| ≤ |V|²/2`, sharpening `Nibble.YusterE.edge_card_le_card_sq`. -/
theorem edge_card_le_half_card_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  classical
  have hle : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
    have hsub : (G.cliqueFinset 2).card ≤
        (Finset.univ.powersetCard 2 : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      rw [SimpleGraph.mem_cliqueFinset_iff] at he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, he.card_eq⟩
    rwa [Finset.card_powersetCard, Finset.card_univ] at hsub
  have hchoose : 2 * ((Fintype.card V).choose 2) ≤ (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    calc 2 * (Fintype.card V * (Fintype.card V - 1) / 2)
        ≤ Fintype.card V * (Fintype.card V - 1) := Nat.mul_div_le _ 2
      _ ≤ Fintype.card V * Fintype.card V := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h1 : (2 : ℝ) * ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : (2 * (G.cliqueFinset 2).card : ℝ) ≤ ((Fintype.card V) ^ 2 : ℝ) := by
      exact_mod_cast le_trans (Nat.mul_le_mul_left 2 hle) hchoose
    linarith
  linarith

/-- **An unconditional `n²/9` bound on the packing gap.**  Since a maximum packing covers a set of
`3ν₃` edges meeting every triangle, `ν₃* ≤ 3ν₃`, so the gap is at most `⅔ν₃*`; and
`ν₃* ≤ |E|/3 ≤ |V|²/6`. -/
theorem nu3star_sub_nu3_le_ninth (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G - (nu3 G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 9 := by
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have h2 := edge_card_le_half_card_sq G
  have h3 := nu3star_le_three_nu3 G
  linarith

/-- **`CoreGapAt ε δ` for every `ε ≥ 1/9`**, unconditionally — a genuine extension of the previously
proved range `ε ≥ 1/3` (`Nibble.AX1.coreGapAt_of_third`). -/
theorem AX1.coreGapAt_of_ninth {ε δ : ℝ} (hε : 1 / 9 ≤ ε) : AX1.CoreGapAt ε δ := by
  refine ⟨0, ?_⟩
  intro V _ _ G _ _ _ _
  have h := nu3star_sub_nu3_le_ninth G
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith

/-! ### The degree of the edge-based triangle hypergraph -/

/-- **The triangle hypergraph has maximum degree at most `|V|`**: a triangle through a fixed edge
`e` is `insert v e` for one of the `|V|` vertices `v`. -/
theorem triangleHypergraphE_degree_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) :
    (Hypergraph.degree (triangleHypergraphE G) e : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  rw [triangleHypergraphE_degree]
  have hsub : ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2))
      ⊆ Finset.univ.image (fun v : V => insert v e) := by
    intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff, Finset.mem_powersetCard] at ht
    obtain ⟨ht3, hesub, hecard⟩ := ht
    have hne : (t \ e).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hesub, ht3.card_eq, hecard]
      norm_num
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_sdiff] at hv
    have hins : insert v e ⊆ t := Finset.insert_subset hv.1 hesub
    have hcard : (insert v e).card = t.card := by
      rw [Finset.card_insert_of_notMem hv.2, hecard, ht3.card_eq]
    have heq : insert v e = t := Finset.eq_of_subset_of_card_le hins (le_of_eq hcard.symm)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, heq⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image (fun v : V => insert v e)).card ≤ Fintype.card V := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset V)) (f := fun v => insert v e)
  exact_mod_cast le_trans h1 h2

/-- `ν₃* ≥ 0`. -/
theorem nu3star_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ nu3star G :=
  le_csSup (nu3star_bddAbove G) ⟨fun _ => 0, isFracPacking_zero G, by simp⟩

/-! ### A proved instance of the weighted nibble: the near-regular case -/

/-- **Every fractional matching of an `r`-uniform hypergraph has total weight at most `|W|/r`.** -/
theorem fracMatching_sum_le {W : Type} [Fintype W] [DecidableEq W] {H : Finset (Finset W)}
    {r : ℕ} (hr : IsUniform H r) {w : Finset W → ℝ}
    (hcon : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) :
    (r : ℝ) * (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) := by
  classical
  have expand : ∀ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) = (r : ℝ) * w T := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hr T hT, nsmul_eq_mul]
  calc (r : ℝ) * (∑ T ∈ H, w T)
      = ∑ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T hT => (expand T hT).symm)
    _ = ∑ v : W, ∑ T ∈ H, (if v ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
        Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
    _ ≤ ∑ _v : W, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hcon v)
    _ = (Fintype.card W : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]

/-- **The weighted nibble holds for nearly regular hypergraphs**, as an immediate consequence of the
proved regular nibble `Nibble.nibbleTheoremMostCeil_holds`: the matching it produces already covers
all but a `β`-fraction of the ground set, and *every* fractional matching has total weight at most
`|W|/r`. This conclusion relies on the stated near-regularity hypotheses. -/
theorem fracNibble_nearlyRegular (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ) (d : ℝ),
        0 < d → d₀ ≤ d → IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : W, (Hypergraph.degree H x : ℝ) ≤ (1 + μ) * d) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro W _ _ H w d hd hd0 hunif hreg hcod hceil hnn hcon
  obtain ⟨M, hM, hMcard⟩ := hmain H d hd hd0 hunif hreg hcod hceil
  refine ⟨M, hM, ?_⟩
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hsum : (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) / r := by
    rw [le_div_iff₀ hrpos, mul_comm]
    exact fracMatching_sum_le hunif hcon
  rcases le_or_gt β 1 with h1 | h1
  · exact le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hMcard
  · have hnn' : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hnn T)
    have : (1 - β) * (∑ T ∈ H, w T) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn'
    exact le_trans this (Nat.cast_nonneg _)

end Nibble

end


/-! # CoreGapNearComplete -/

public section

open Finset SimpleGraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Edge counting -/

/-- The number of `2`-cliques is at most the number of edges. -/
theorem card_clique2_le_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueFinset 2).card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  have hsurj : Set.SurjOn (fun e : Sym2 V => e.toFinset) (G.edgeFinset : Set (Sym2 V))
      ((G.cliqueFinset 2 : Finset (Finset V)) : Set (Finset V)) := by
    intro f hf
    simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at hf
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hf.card_eq
    have hadj : G.Adj a b := hf.1 (by simp) (by simp) hab
    refine ⟨s(a, b), ?_, ?_⟩
    · simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      exact hadj
    · ext x; simp [Sym2.mem_toFinset]
  exact_mod_cast Finset.card_le_card_of_surjOn _ hsurj

omit [DecidableEq V] in
/-- **Few vertices of low degree in an edge-rich graph.**  With `L` the set of vertices of degree
below `t`, one has `|L|·(|V| − t) ≤ |V|² − 2|E|`. -/
theorem card_lowDeg_mul_le (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) :
    (((univ : Finset V).filter (fun v => (G.degree v : ℝ) < t)).card : ℝ)
        * ((Fintype.card V : ℝ) - t)
      ≤ (Fintype.card V : ℝ) ^ 2 - 2 * (G.edgeFinset.card : ℝ) := by
  classical
  set L : Finset V := (univ : Finset V).filter (fun v => (G.degree v : ℝ) < t) with hL
  have hsum : ∑ v : V, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have := SimpleGraph.sum_degrees_eq_twice_card_edges G
    have h2 : ((∑ v : V, G.degree v : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at h2
    simpa using h2
  have hsplit : ∑ v ∈ L, (G.degree v : ℝ) + ∑ v ∈ Lᶜ, (G.degree v : ℝ)
      = ∑ v : V, (G.degree v : ℝ) := by
    rw [← Finset.sum_add_sum_compl L (fun v => (G.degree v : ℝ))]
  have hL1 : ∑ v ∈ L, (G.degree v : ℝ) ≤ (L.card : ℝ) * t := by
    calc ∑ v ∈ L, (G.degree v : ℝ) ≤ ∑ _v ∈ L, t := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          exact le_of_lt (Finset.mem_filter.mp hv).2
      _ = (L.card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
  have hdegle : ∀ v : V, (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro v
    have := SimpleGraph.degree_lt_card_verts (G := G) v
    exact le_of_lt (by exact_mod_cast this)
  have hL2 : ∑ v ∈ Lᶜ, (G.degree v : ℝ) ≤ ((Lᶜ).card : ℝ) * (Fintype.card V : ℝ) := by
    calc ∑ v ∈ Lᶜ, (G.degree v : ℝ) ≤ ∑ _v ∈ Lᶜ, (Fintype.card V : ℝ) :=
          Finset.sum_le_sum (fun v _ => hdegle v)
      _ = ((Lᶜ).card : ℝ) * (Fintype.card V : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcompl : ((Lᶜ).card : ℝ) = (Fintype.card V : ℝ) - (L.card : ℝ) := by
    have : (Lᶜ).card = Fintype.card V - L.card := by
      rw [Finset.card_compl]
    have hle : L.card ≤ Fintype.card V := Finset.card_le_univ L
    rw [this, Nat.cast_sub hle]
  rw [hcompl] at hL2
  linarith only [hsum, hsplit, hL1, hL2]

/-! ### The deletion at a set of vertices -/

/-- Deleting all edges at the vertices of `L` destroys at most `|L|·|V|` edges. -/
theorem card_deleted_restrictAway_le (G : SimpleGraph V) [DecidableRel G.Adj] (L : Finset V) :
    ((G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card : ℝ)
      ≤ (L.card : ℝ) * (Fintype.card V : ℝ) := by
  classical
  have hsub : G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2
      ⊆ L.biUnion (fun v => (G.neighborFinset v).image (fun u => ({v, u} : Finset V))) := by
    intro e he
    rw [Finset.mem_sdiff, SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he1.card_eq
    have hadj : G.Adj a b := he1.1 (by simp) (by simp) hab
    have hnadj : ¬ (restrictAway G L).Adj a b := by
      intro h
      refine he2 (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
      simpa using SimpleGraph.isClique_pair.mpr (fun _ => h)
    have hmem : a ∈ L ∨ b ∈ L := by
      by_contra hcon
      push Not at hcon
      exact hnadj ⟨hadj, hcon.1, hcon.2⟩
    rw [Finset.mem_biUnion]
    rcases hmem with h | h
    · exact ⟨a, h, Finset.mem_image.mpr ⟨b, by simpa using hadj, rfl⟩⟩
    · refine ⟨b, h, Finset.mem_image.mpr ⟨a, by simpa using hadj.symm, ?_⟩⟩
      exact Finset.pair_comm b a
  have hcard := Finset.card_le_card hsub
  have hbu : (L.biUnion (fun v => (G.neighborFinset v).image (fun u => ({v, u} : Finset V)))).card
      ≤ ∑ v ∈ L, G.degree v := by
    refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum (fun v _ => ?_))
    exact le_trans (Finset.card_image_le) (le_of_eq (SimpleGraph.card_neighborFinset_eq_degree G v))
  have hdeg : ∑ v ∈ L, G.degree v ≤ L.card * Fintype.card V := by
    calc ∑ v ∈ L, G.degree v ≤ ∑ _v ∈ L, Fintype.card V := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          exact le_of_lt (SimpleGraph.degree_lt_card_verts (G := G) v)
      _ = L.card * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul]
  have : (G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card
      ≤ L.card * Fintype.card V := le_trans hcard (le_trans hbu hdeg)
  exact_mod_cast this

/-- Deleting the edges at `L` lowers each degree outside `L` by at most `|L|`. -/
theorem degree_restrictAway_ge (G : SimpleGraph V) [DecidableRel G.Adj] {L : Finset V} {x : V}
    (hx : x ∉ L) :
    (G.degree x : ℝ) - (L.card : ℝ) ≤ ((restrictAway G L).degree x : ℝ) := by
  classical
  have hsub : G.neighborFinset x \ L ⊆ (restrictAway G L).neighborFinset x := by
    intro y hy
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    exact SimpleGraph.mem_neighborFinset _ _ _ |>.mpr ⟨hy.1, hx, hy.2⟩
  have h1 : (G.neighborFinset x \ L).card ≤ (restrictAway G L).degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  have h2 : G.degree x ≤ (G.neighborFinset x \ L).card + L.card := by
    have := Finset.card_le_card_sdiff_add_card (s := G.neighborFinset x) (t := L)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at this
    exact this
  have h3 : (G.degree x : ℝ) ≤ ((G.neighborFinset x \ L).card : ℝ) + (L.card : ℝ) := by
    exact_mod_cast h2
  have h4 : (((G.neighborFinset x \ L).card : ℕ) : ℝ) ≤ ((restrictAway G L).degree x : ℝ) := by
    exact_mod_cast h1
  linarith only [h3, h4]

/-! ### The near-complete branch -/

/-- **The near-complete branch.**  For every `ε > 0` there is `η > 0` such that every large graph
with at least `(1/2 − η)|V|²` edges has packing gap at most `ε|V|²`. -/
theorem gap_le_of_near_complete (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (1 / 2 - η) * (Fintype.card V : ℝ) ^ 2 ≤ ((G.cliqueFinset 2).card : ℝ) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨θ, hθ0, hθ1, n₀, hdense⟩ := nibbleGap_of_dense_core ε hε
  set θ₂ : ℝ := (1 + θ) / 2 with hθ₂def
  have hθ₂lo : θ < θ₂ := by rw [hθ₂def]; linarith only [hθ1]
  have hθ₂hi : θ₂ < 1 := by rw [hθ₂def]; linarith only [hθ₂def, hθ₂lo]
  have hgap2 : 0 < 1 - θ₂ := by linarith only [hθ₂hi]
  have hp1 : (0 : ℝ) < (1 - θ₂) * ε / 8 := by
    apply div_pos (mul_pos hgap2 hε); norm_num
  have hp2 : (0 : ℝ) < (1 - θ₂) * (1 - θ) / 4 := by
    apply div_pos (mul_pos hgap2 (by linarith)); norm_num
  refine ⟨min ((1 - θ₂) * ε / 8) ((1 - θ₂) * (1 - θ) / 4), lt_min hp1 hp2, max n₀ 1, ?_⟩
  set η : ℝ := min ((1 - θ₂) * ε / 8) ((1 - θ₂) * (1 - θ) / 4) with hηdef
  have hη1 : η ≤ (1 - θ₂) * ε / 8 := min_le_left _ _
  have hη2 : η ≤ (1 - θ₂) * (1 - θ) / 4 := min_le_right _ _
  have hηpos : 0 < η := lt_min hp1 hp2
  intro V _ _ G _ hV hedge
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : 1 ≤ Fintype.card V := le_trans (le_max_right n₀ 1) hV
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith only [hn1]
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  -- the low-degree set
  set L : Finset V := (univ : Finset V).filter (fun v => (G.degree v : ℝ) < θ₂ * n) with hLdef
  have hcount := card_lowDeg_mul_le G (θ₂ * n)
  have hE : ((G.cliqueFinset 2).card : ℝ) ≤ (G.edgeFinset.card : ℝ) :=
    card_clique2_le_card_edgeFinset G
  have hL : (L.card : ℝ) * ((1 - θ₂) * n) ≤ 2 * η * n ^ 2 := by
    have h1 : n - θ₂ * n = (1 - θ₂) * n := by ring
    rw [h1] at hcount
    linarith only [hcount, hE, hedge]
  have hLcard : (L.card : ℝ) ≤ 2 * η * n / (1 - θ₂) := by
    rw [le_div_iff₀ hgap2]
    nlinarith only [hL, hnpos]
  -- the deletion is small
  have hdel : ((G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card : ℝ)
      ≤ (ε / 4) * n ^ 2 := by
    have h1 := card_deleted_restrictAway_le G L
    have h2 : (L.card : ℝ) * n ≤ (2 * η * n / (1 - θ₂)) * n := by
      apply mul_le_mul_of_nonneg_right hLcard (le_of_lt hnpos)
    have h3 : (2 * η * n / (1 - θ₂)) * n ≤ (ε / 4) * n ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hgap2]
      nlinarith only [hη1, hnpos]
    linarith only [h1, h2, h3]
  -- the core is dense
  have hdeg : ∀ x : V, (restrictAway G L).degree x = 0 ∨
      θ * n ≤ ((restrictAway G L).degree x : ℝ) := by
    intro x
    by_cases hx : x ∈ L
    · exact Or.inl (restrictAway_degree_eq_zero G hx)
    · refine Or.inr ?_
      have hdx : θ₂ * n ≤ (G.degree x : ℝ) := by
        by_contra hcon
        push Not at hcon
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcon⟩)
      have hlow := degree_restrictAway_ge G (L := L) hx
      have hLsmall : (L.card : ℝ) ≤ (1 - θ) * n / 2 := by
        have : 2 * η * n / (1 - θ₂) ≤ (1 - θ) * n / 2 := by
          rw [div_le_div_iff₀ hgap2 (by norm_num : (0:ℝ) < 2)]
          nlinarith only [hη2, hnpos]
        linarith [hLcard]
      have hθ₂eq : θ₂ * n = θ * n + (1 - θ) * n / 2 := by rw [hθ₂def]; ring
      linarith only [hdx, hlow, hLsmall, hθ₂eq]
  exact hdense V G (le_trans (le_max_left n₀ 1) hV) (restrictAway G L) _ (restrictAway_le G L)
    hdel hdeg

/-! ### A universal constant below `1/9` -/

/-- **A universal packing-gap constant below `1/9`.**  There is `c < 1/9` with
`ν₃* − ν₃ ≤ c|V|²` for every large graph: near-complete graphs are handled by
`Nibble.AX1.gap_le_of_near_complete`, all others by `ν₃* ≤ |E|/3` together with `ν₃* ≤ 3ν₃`. -/
theorem exists_gap_const_lt_ninth :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 9 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → nu3star G - (nu3 G : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨η, hη, n₀, hnear⟩ := gap_le_of_near_complete (1 / 10) (by norm_num)
  refine ⟨max (1 / 10) (1 / 9 - 2 * η / 9), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_,
    n₀, ?_⟩
  · exact max_lt (by norm_num) (by linarith)
  intro V _ _ G _ hV
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  rcases le_or_gt ((1 / 2 - η) * (Fintype.card V : ℝ) ^ 2) (((G.cliqueFinset 2).card : ℝ))
    with hcase | hcase
  · have := hnear V G hV hcase
    have hle : (1 / 10 : ℝ) ≤ max (1 / 10) (1 / 9 - 2 * η / 9) := le_max_left _ _
    nlinarith only [this, hle]
  · have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
    have h2 : nu3star G ≤ 3 * (nu3 G : ℝ) := Nibble.nu3star_le_three_nu3 G
    have hle : (1 / 9 - 2 * η / 9 : ℝ) ≤ max (1 / 10) (1 / 9 - 2 * η / 9) := le_max_right _ _
    nlinarith only [hcase, h1, h2, hle]

/-- **`CoreGapAt ε δ` for every `δ` and every `ε` above a constant `c < 1/9`**, strictly improving
`Nibble.AX1.coreGapAt_of_ninth`. -/
theorem coreGapAt_of_lt_ninth :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 9 ∧ ∀ ε δ : ℝ, c ≤ ε → CoreGapAt ε δ := by
  obtain ⟨c, hc0, hc9, n₀, hmain⟩ := exists_gap_const_lt_ninth
  refine ⟨c, hc0, hc9, fun ε δ hε => ⟨n₀, ?_⟩⟩
  intro V _ _ G _ hV _ _
  have h := hmain V G hV
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hε) hnn]

end Nibble.AX1

end


/-! # CoreGapRegularDegrees -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The **triangle degree of an edge**: the number of triangles of `G` containing it. -/
@[expose]
def edgeTriangleDegree (G : SimpleGraph V) [DecidableRel G.Adj] (e : Finset V) : ℕ :=
  ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).card

/-- The triangle degree of an edge is its degree in the edge-based triangle hypergraph. -/
theorem edgeTriangleDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E = edgeTriangleDegree G E.val :=
  triangleHypergraphSub_degree_eq G E

/-- **The near-regular branch.**  For every `ε > 0` there are `μ, η > 0` and `d₀ > 0` such that any
graph whose edges all have triangle degree at most `(1+μ)d`, and at least `(1−μ)d` outside an
exceptional set of at most `η|E|` edges, for some `d ≥ d₀`, has packing gap at most `ε|V|²`.

The triangle hypergraph is `3`-uniform with codegree at most `1 ≤ μd`, so these hypotheses are
exactly the input of the unconditional nibble `Nibble.nibbleTheoremMostCeil_holds`; the resulting
matching covers all but a `3ε`-fraction of the edges, which is the packing-gap accounting
`Nibble.AX1.gap_le_of_sub_matching`. -/
theorem gap_le_of_regular_triangle_degrees (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ) (Exc : Finset (Finset V)), d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  refine ⟨μ, hμ, η, hη, max d₀ (max (1 / μ) 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  intro V _ _ G _ d Exc hd hExc hhi hlo
  have hdd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : 1 / μ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hcodeg : (1 : ℝ) ≤ μ * d := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  -- the exceptional set, transported to the edge vertex type
  set Exc' : Finset (EdgeV G) := (univ : Finset (EdgeV G)).filter (fun E => E.val ∈ Exc)
    with hExc'def
  have hExc'card : Exc'.card ≤ Exc.card := by
    refine Finset.card_le_card_of_injOn (fun E => E.val) (fun E hE => ?_) ?_
    · exact (Finset.mem_filter.mp hE).2
    · intro E _ E' _ h
      exact Subtype.ext h
  have hcardEdge : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hExc' : (Exc'.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ) := by
    rw [hcardEdge]
    have : (Exc'.card : ℝ) ≤ (Exc.card : ℝ) := by exact_mod_cast hExc'card
    linarith
  have hhi' : ∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
    intro E
    rw [edgeTriangleDegree_eq G E]
    exact hhi E.val E.property
  have hlo' : ∀ E ∉ Exc', (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    intro E hE
    rw [edgeTriangleDegree_eq G E]
    refine hlo E.val E.property (fun hc => hE ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ E, hc⟩
  have hreg : NearlyRegularMost (triangleHypergraphSub G) d μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G Exc' hExc' hlo' (fun E _ => hhi' E)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * d) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hdpos hdd₀ (triangleHypergraphSub_uniform G) hreg hcod hhi'
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- **The near-regular branch, no exceptional edges.** -/
theorem gap_le_of_regular_triangle_degrees' (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ), d₀ ≤ d →
        (∀ e ∈ G.cliqueFinset 2, (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ) ∧
          (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := gap_le_of_regular_triangle_degrees ε hε
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ G _ d hd hwin
  refine hmain V G d ∅ hd ?_ (fun e he => (hwin e he).2) (fun e he _ => (hwin e he).1)
  rw [Finset.card_empty, Nat.cast_zero]
  positivity

/-- **The near-regular branch, up to a small deletion.**  If a graph becomes near-regular in its
triangle degrees after deleting at most `(ε/2)|V|²` edges, its packing gap is at most `ε|V|²`:
deleting `k` edges moves `ν₃*` by at most `k` and can only decrease `ν₃`
(`Nibble.AX1.gap_le_core_gap`).

This is to `Nibble.AX1.gap_le_of_regular_triangle_degrees` what
`Nibble.AX1.nibbleGap_of_dense_core` is to the dense branch. -/
theorem gap_le_of_regular_triangle_degrees_core (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (G' : SimpleGraph V) (_ : DecidableRel G'.Adj) (d : ℝ) (Exc : Finset (Finset V)),
        G' ≤ G →
        ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 →
        d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G'.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G'.cliqueFinset 2, (edgeTriangleDegree G' e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G'.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G' e : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := gap_le_of_regular_triangle_degrees (ε / 2) (by linarith)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro V _ _ G _ G' _ d Exc hle hdel hd hExc hhi hlo
  have hgap' := hmain V G' d Exc hd hExc hhi hlo
  have hstab := gap_le_core_gap G G' hle
  linarith only [hdel, hgap', hstab]

/-! ### The complementary branch: uniformly small triangle degrees -/

/-- **The small-degree branch.**  For every `ε > 0` there is `ρ > 0` such that a graph all of whose
edges lie in at most `ρ|V|` triangles has packing gap at most `ε|V|²`.

The handshake identity `∑_e t(e) = 3·#triangles` turns the degree bound into
`#triangles ≤ ρ|V|³/6`, which is the removal branch `Nibble.AX1.nu3star_le_of_few_triangles`.
Together with `Nibble.AX1.gap_le_of_regular_triangle_degrees` this leaves only the graphs whose
triangle degrees are simultaneously large somewhere and far from regular. -/
theorem gap_le_of_small_triangle_degrees (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ ρ * (Fintype.card V : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  refine ⟨SimpleGraph.triangleRemovalBound ε, SimpleGraph.triangleRemovalBound_pos hε, ?_⟩
  intro V _ _ G _ hdeg
  set ρ : ℝ := SimpleGraph.triangleRemovalBound ε with hρdef
  have hρ : 0 < ρ := SimpleGraph.triangleRemovalBound_pos hε
  have hnu3 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn0 | hnpos
  · -- no vertices: no triangles at all
    have htri : (G.cliqueFinset 3).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      have : t.Nonempty := by
        rw [← Finset.card_pos, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq]
        norm_num
      obtain ⟨x, -⟩ := this
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    have h1 := nu3star_le_card_triangles G
    rw [htri, Nat.cast_zero] at h1
    have : (0 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
    linarith only [h1, this]
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hnpos
  -- the handshake bound on the number of triangles
  have hsum : ∑ E : EdgeV G, degree (triangleHypergraphSub G) E = 3 * (G.cliqueFinset 3).card :=
    sum_degree_triangleHypergraphSub G
  have hsumR : (3 : ℝ) * ((G.cliqueFinset 3).card : ℝ)
      = ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hsum
    push_cast at this
    linarith only [this]
  have hbound : ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ)
      ≤ (Fintype.card (EdgeV G) : ℝ) * (ρ * (Fintype.card V : ℝ)) := by
    calc ∑ E : EdgeV G, (degree (triangleHypergraphSub G) E : ℝ)
        ≤ ∑ _E : EdgeV G, ρ * (Fintype.card V : ℝ) := by
          refine Finset.sum_le_sum (fun E _ => ?_)
          rw [edgeTriangleDegree_eq G E]
          exact hdeg E.val E.property
      _ = (Fintype.card (EdgeV G) : ℝ) * (ρ * (Fintype.card V : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hE : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
    Nibble.edge_card_le_half_card_sq G
  rw [hcardE] at hbound
  have hfew : ((G.cliqueFinset 3).card : ℝ) < ρ * (Fintype.card V : ℝ) ^ 3 := by
    have hpos : (0 : ℝ) < ρ * (Fintype.card V : ℝ) ^ 3 := by positivity
    have hstep : ((G.cliqueFinset 2).card : ℝ) * (ρ * (Fintype.card V : ℝ))
        ≤ ((Fintype.card V : ℝ) ^ 2 / 2) * (ρ * (Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    have hring : ((Fintype.card V : ℝ) ^ 2 / 2) * (ρ * (Fintype.card V : ℝ))
        = ρ * (Fintype.card V : ℝ) ^ 3 / 2 := by ring
    rw [hring] at hstep
    linarith only [hsumR, hbound, hstep, hpos]
  have h1 := nu3star_le_of_few_triangles G hfew
  linarith only [h1]

/-! ### Deleting the heavy edges -/

/-- `G` with every edge of triangle degree above `c` deleted. -/
def deleteHeavy (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c
  symm := ⟨by
    rintro x y ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [Finset.pair_comm]⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance instDecidableRelDeleteHeavy (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : ℝ) :
    DecidableRel (deleteHeavy G c).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c))

theorem deleteHeavy_adj (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (x y : V) :
    (deleteHeavy G c).Adj x y ↔ G.Adj x y ∧ (edgeTriangleDegree G {x, y} : ℝ) ≤ c := Iff.rfl

theorem deleteHeavy_le (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    deleteHeavy G c ≤ G := fun _ _ h => h.1

/-- The `2`-cliques deleted by `Nibble.AX1.deleteHeavy` are exactly heavy edges. -/
theorem deleted_subset_heavy (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    G.cliqueFinset 2 \ (deleteHeavy G c).cliqueFinset 2
      ⊆ (G.cliqueFinset 2).filter (fun e => c < (edgeTriangleDegree G e : ℝ)) := by
  intro e he
  rw [Finset.mem_sdiff] at he
  refine Finset.mem_filter.mpr ⟨he.1, ?_⟩
  obtain ⟨hmem, hnot⟩ := he
  have hcl := SimpleGraph.mem_cliqueFinset_iff.mp hmem
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcl.card_eq
  have hadj : G.Adj a b := hcl.1 (by simp) (by simp) hab
  by_contra hcon
  push Not at hcon
  refine hnot (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
  have hadj' : (deleteHeavy G c).Adj a b := (deleteHeavy_adj G c a b).mpr ⟨hadj, hcon⟩
  simpa using SimpleGraph.isClique_pair.mpr (fun _ => hadj')

/-- Triangle degrees only decrease when passing to a subgraph. -/
theorem edgeTriangleDegree_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) (e : Finset V) : edgeTriangleDegree G' e ≤ edgeTriangleDegree G e :=
  Finset.card_le_card
    (Finset.filter_subset_filter _ (SimpleGraph.cliqueFinset_mono G hle))

/-- **The few-heavy-edges branch.**  For every `ε > 0` there is `ρ > 0` such that if the edges lying
in more than `ρ|V|` triangles number at most `(ε/2)|V|²`, then the packing gap is at most `ε|V|²`:
delete them (which costs at most that many edges of the gap) and apply
`Nibble.AX1.gap_le_of_small_triangle_degrees` to what is left.

So the only graphs left open are those with at least `(ε/2)|V|²` edges each lying in more than
`ρ|V|` triangles. -/
theorem gap_le_of_few_heavy_edges (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card : ℝ)
          ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨ρ, hρ, hsmall⟩ := gap_le_of_small_triangle_degrees (ε / 2) (by linarith)
  refine ⟨ρ, hρ, ?_⟩
  intro V _ _ G _ hheavy
  set G' : SimpleGraph V := deleteHeavy G (ρ * (Fintype.card V : ℝ)) with hG'def
  have hle : G' ≤ G := deleteHeavy_le G _
  have hdel : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
      ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 := by
    have h1 : (G.cliqueFinset 2 \ G'.cliqueFinset 2).card
        ≤ ((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card :=
      Finset.card_le_card (deleted_subset_heavy G _)
    have h2 : ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ)
        ≤ (((G.cliqueFinset 2).filter
            (fun e => ρ * (Fintype.card V : ℝ) < (edgeTriangleDegree G e : ℝ))).card : ℝ) := by
      exact_mod_cast h1
    linarith only [hheavy, h2]
  have hdeg : ∀ e ∈ G'.cliqueFinset 2, (edgeTriangleDegree G' e : ℝ)
      ≤ ρ * (Fintype.card V : ℝ) := by
    intro e he
    rw [SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.card_eq
    have hadj : (deleteHeavy G (ρ * (Fintype.card V : ℝ))).Adj a b := he.1 (by simp) (by simp) hab
    have hmono : edgeTriangleDegree G' ({a, b} : Finset V)
        ≤ edgeTriangleDegree G ({a, b} : Finset V) := edgeTriangleDegree_mono G G' hle _
    have hbound : (edgeTriangleDegree G ({a, b} : Finset V) : ℝ) ≤ ρ * (Fintype.card V : ℝ) :=
      hadj.2
    have : (edgeTriangleDegree G' ({a, b} : Finset V) : ℝ)
        ≤ (edgeTriangleDegree G ({a, b} : Finset V) : ℝ) := by exact_mod_cast hmono
    linarith only [hbound, this]
  have hgap' := hsmall V G' hdeg
  have hstab := gap_le_core_gap G G' hle
  linarith only [hdel, hgap', hstab]

end Nibble.AX1

end


/-! # CoreGapRegularDecomp -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Colour classes of an edge colouring -/

/-- The spanning subgraph of `G` consisting of the edges `e` with `P e`. -/
@[expose] def edgeSelect (G : SimpleGraph V) (P : Finset V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ P {x, y}
  symm := ⟨by
    rintro x y ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [Finset.pair_comm]⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance instDecidableRelEdgeSelect (G : SimpleGraph V) (P : Finset V → Prop) :
    DecidableRel (edgeSelect G P).Adj := fun _ _ => Classical.dec _

omit [Fintype V] in
theorem edgeSelect_adj (G : SimpleGraph V) (P : Finset V → Prop) (x y : V) :
    (edgeSelect G P).Adj x y ↔ G.Adj x y ∧ P {x, y} := Iff.rfl

omit [Fintype V] in
theorem edgeSelect_le (G : SimpleGraph V) (P : Finset V → Prop) : edgeSelect G P ≤ G :=
  fun _ _ h => h.1

/-- The `i`-th colour class of the edge colouring `col`. -/
@[expose]
noncomputable def colorPart (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ) : SimpleGraph V :=
  edgeSelect G (fun e => col e = i)

noncomputable instance instDecidableRelColorPart (G : SimpleGraph V)
    (col : Finset V → ℕ) (i : ℕ) : DecidableRel (colorPart G col i).Adj :=
  instDecidableRelEdgeSelect G _

omit [Fintype V] in
theorem colorPart_le (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ) : colorPart G col i ≤ G :=
  edgeSelect_le G _

/-- Every edge of a triangle of the `i`-th colour class has colour `i`. -/
theorem colorPart_hyperedge_color (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ)
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE (colorPart G col i)) :
    ∀ e ∈ T, col e = i := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  intro e he
  rw [Finset.mem_powersetCard] at he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
  have hadj : (colorPart G col i).Adj a b :=
    ht.1 (he.1 (by simp)) (he.1 (by simp)) hab
  exact hadj.2

/-- Hyperedges of a triangle hypergraph are nonempty. -/
theorem triangleHypergraphE_nonempty_of_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G) : T.Nonempty := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [← Finset.card_pos, Finset.card_powersetCard, ht.card_eq]
  decide +kernel

/-- **Superadditivity of `ν₃` over the colour classes of an edge colouring.**
The colour classes are
edge-disjoint, so maximum packings of the classes unite to a packing of `G`. -/
theorem nu3_sum_colorParts_le (G : SimpleGraph V) [DecidableRel G.Adj] (col : Finset V → ℕ)
    (k : ℕ) : ∑ i ∈ Finset.range k, nu3 (colorPart G col i) ≤ nu3 G := by
  classical
  have hex : ∀ i : ℕ, ∃ M : Finset (Finset (Finset V)),
      IsMatching (triangleHypergraphE (colorPart G col i)) M ∧
        M.card = nu3 (colorPart G col i) := fun i => Nibble.exists_maximum_packing _
  choose Mf hMf hMcard using hex
  have hmemcol : ∀ (i : ℕ), ∀ T ∈ Mf i, ∀ e ∈ T, col e = i := by
    intro i T hT
    exact colorPart_hyperedge_color G col i ((hMf i).subset hT)
  have hmemne : ∀ (i : ℕ), ∀ T ∈ Mf i, T.Nonempty := by
    intro i T hT
    exact triangleHypergraphE_nonempty_of_mem _ ((hMf i).subset hT)
  have hdisj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i ≠ j → Disjoint (Mf i) (Mf j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro T hTi hTj
    obtain ⟨e, he⟩ := hmemne i T hTi
    have h1 := hmemcol i T hTi e he
    have h2 := hmemcol j T hTj e he
    exact hij (h1 ▸ h2 ▸ rfl)
  set M : Finset (Finset (Finset V)) := (Finset.range k).biUnion Mf with hMdef
  have hcard : M.card = ∑ i ∈ Finset.range k, (Mf i).card := Finset.card_biUnion hdisj
  have hMatch : IsMatching (triangleHypergraphE G) M := by
    constructor
    · intro T hT
      rw [hMdef, Finset.mem_biUnion] at hT
      obtain ⟨i, -, hTi⟩ := hT
      exact triangleHypergraphE_mono G (colorPart G col i) (colorPart_le G col i)
        ((hMf i).subset hTi)
    · intro T hT T' hT' hne
      rw [hMdef, Finset.mem_biUnion] at hT hT'
      obtain ⟨i, -, hTi⟩ := hT
      obtain ⟨j, -, hTj⟩ := hT'
      by_cases hij : i = j
      · subst hij
        exact (hMf i).disjoint T hTi T' hTj hne
      · rw [Finset.disjoint_left]
        intro e he he'
        exact hij ((hmemcol i T hTi e he) ▸ (hmemcol j T' hTj e he') ▸ rfl)
  calc ∑ i ∈ Finset.range k, nu3 (colorPart G col i)
      = ∑ i ∈ Finset.range k, (Mf i).card := by
        exact Finset.sum_congr rfl (fun i _ => (hMcard i).symm)
    _ = M.card := hcard.symm
    _ ≤ nu3 G := nu3_ge G hMatch

/-! ### The nibble, as a lower bound on `ν₃` -/

/-- **The nibble as an integral packing bound.**  For every `β > 0` there are `μ, η > 0` and `d₀`
such that a graph with near-regular triangle degrees at a scale `d ≥ d₀` has
`ν₃ ≥ (1−β)|E|/3`. -/
theorem nu3_ge_of_regular_triangle_degrees (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ) (Exc : Finset (Finset V)), d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) →
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds 3 (by norm_num) β hβ
  refine ⟨μ, hμ, η, hη, max d₀ (max (1 / μ) 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  intro V _ _ G _ d Exc hd hExc hhi hlo
  have hdd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : 1 / μ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hcodeg : (1 : ℝ) ≤ μ * d := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  set Exc' : Finset (EdgeV G) := (univ : Finset (EdgeV G)).filter (fun E => E.val ∈ Exc)
    with hExc'def
  have hExc'card : Exc'.card ≤ Exc.card := by
    refine Finset.card_le_card_of_injOn (fun E => E.val) (fun E hE => ?_) ?_
    · exact (Finset.mem_filter.mp hE).2
    · intro E _ E' _ h
      exact Subtype.ext h
  have hcardEdge : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hExc' : (Exc'.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ) := by
    rw [hcardEdge]
    have : (Exc'.card : ℝ) ≤ (Exc.card : ℝ) := by exact_mod_cast hExc'card
    linarith
  have hhi' : ∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
    intro E
    rw [edgeTriangleDegree_eq G E]
    exact hhi E.val E.property
  have hlo' : ∀ E ∉ Exc', (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    intro E hE
    rw [edgeTriangleDegree_eq G E]
    refine hlo E.val E.property (fun hc => hE ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ E, hc⟩
  have hreg : NearlyRegularMost (triangleHypergraphSub G) d μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G Exc' hExc' hlo' (fun E _ => hhi' E)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * d) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hdpos hdd₀ (triangleHypergraphSub_uniform G) hreg hcod hhi'
  have hle : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have hMcard' : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
    have := hMcard
    rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num] at this
    rwa [hcardEdge] at this
  linarith

/-! ### The structural residual -/

/-- **A near-regular decomposition at parameters `(ε, μ, η, d₀)`.**  Every large graph carries an
edge colouring whose colour classes have near-regular triangle degrees — each at its own scale
`d i ≥ d₀`, with the lower bound allowed to fail on at most an `η`-fraction of that class's edges —
and whose total edge count is at least `3ν₃*(G) − 3ε|V|²`. -/
def RegularDecompAt (ε μ η d₀ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ (k : ℕ) (col : Finset V → ℕ) (d : ℕ → ℝ),
      (∀ i < k, d₀ ≤ d i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * d i) ∧
      (∀ i < k, ∃ Exc : Finset (Finset V),
        (Exc.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2

/-- **The structural residual**: a near-regular decomposition at every window of parameters. -/
@[expose] def RegularDecompResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    RegularDecompAt ε μ η d₀

/-- **The reduction.**  A near-regular decomposition of every large graph implies the AX1 core
residual: the nibble packs each colour class up to a `(1−β)`-fraction of its edges
(`Nibble.AX1.nu3_ge_of_regular_triangle_degrees`), the classes are edge-disjoint so the packings
unite (`Nibble.AX1.nu3_sum_colorParts_le`), and the decomposition's edge count recovers `ν₃*`. -/
theorem coreGapResidual_of_regularDecomp (h : RegularDecompResidual) : CoreGapResidual := by
  intro ε hε δ _
  rcases le_or_gt (1 / 3 : ℝ) ε with hbig | hsmall
  · exact coreGapAt_of_third hbig
  -- `β = 3ε < 1`
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hnib⟩ := nu3_ge_of_regular_triangle_degrees (3 * ε) (by linarith)
  obtain ⟨n₀, hdec⟩ := h (ε / 2) (by linarith) μ hμ η hη d₀ hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV _ _
  obtain ⟨k, col, d, hd, hhi, hlo, hval⟩ := hdec V G hV
  -- each colour class is packed by the nibble
  have hpart : ∀ i ∈ Finset.range k,
      (1 - 3 * ε) * ((((colorPart G col i).cliqueFinset 2).card : ℝ) / 3)
        ≤ (nu3 (colorPart G col i) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    exact hnib V (colorPart G col i) (d i) Exc (hd i hi) hExc (hhi i hi) hlo'
  have hsum : (1 - 3 * ε) * (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3)
      ≤ ∑ i ∈ Finset.range k, (nu3 (colorPart G col i) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpart
  have hsuper : ∑ i ∈ Finset.range k, (nu3 (colorPart G col i) : ℝ) ≤ (nu3 G : ℝ) := by
    have := nu3_sum_colorParts_le G col k
    exact_mod_cast this
  -- assemble
  set S : ℝ := ∑ i ∈ Finset.range k, (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3 with hS
  have hSnn : 0 ≤ S := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    positivity
  have hstar : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have hEn : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
    Nibble.edge_card_le_half_card_sq G
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  have hstar6 : nu3star G ≤ (Fintype.card V : ℝ) ^ 2 / 6 := by linarith
  have hcoef : (0 : ℝ) < 1 - 3 * ε := by linarith
  have hS' : nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2 ≤ S := by linarith
  have h1 : (1 - 3 * ε) * (nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2)
      ≤ (1 - 3 * ε) * S := mul_le_mul_of_nonneg_left hS' hcoef.le
  have hA : (1 - 3 * ε) * (nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2) ≤ (nu3 G : ℝ) :=
    le_trans h1 (le_trans hsum hsuper)
  have hB : 3 * ε * nu3star G ≤ 3 * ε * ((Fintype.card V : ℝ) ^ 2 / 6) :=
    mul_le_mul_of_nonneg_left hstar6 (by positivity)
  have hC : (0 : ℝ) ≤ ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by positivity
  linarith only [hA, hB, hC]

/-- **AX1 from the structural residual.** -/
theorem ax1_of_regularDecomp (h : RegularDecompResidual) : AX1Statement :=
  ax1_of_coreGapResidual (coreGapResidual_of_regularDecomp h)

/-! ### The residual is satisfiable: the one-colour witness -/

omit [Fintype V] in
/-- Colouring every edge `0` leaves the graph unchanged. -/
theorem colorPart_const (G : SimpleGraph V) : colorPart G (fun _ => 0) 0 = G := by
  ext x y
  simp [colorPart, edgeSelect_adj]

/-- **The one-colour witness.**  A graph whose own triangle degrees are near-regular at a scale
`d ≥ d₀` satisfies the requirement of `Nibble.AX1.RegularDecompAt` with the trivial one-colour
decomposition.  So the structural residual is exactly the assertion that *every* large graph can be
edge-coloured into near-regular classes without losing more than `ε|V|²` of the fractional optimum:
it is a genuine statement about colourings, non-vacuous and satisfied by the regular graphs. -/
theorem regularDecomp_witness_of_regular (ε μ η d₀ : ℝ) (hε : 0 ≤ ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (Exc : Finset (Finset V)) (hd : d₀ ≤ d)
    (hExc : (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ))
    (hhi : ∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d)
    (hlo : ∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) :
    ∃ (k : ℕ) (col : Finset V → ℕ) (dd : ℕ → ℝ),
      (∀ i < k, d₀ ≤ dd i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * dd i) ∧
      (∀ i < k, ∃ Exc' : Finset (Finset V),
        (Exc'.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc' →
          (1 - μ) * dd i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hge : G ≤ colorPart G (fun _ => 0) 0 := by rw [colorPart_const]
  have hdeg : ∀ e, edgeTriangleDegree (colorPart G (fun _ => 0) 0) e = edgeTriangleDegree G e :=
    fun e => le_antisymm (edgeTriangleDegree_mono G _ (colorPart_le G _ 0) e)
      (edgeTriangleDegree_mono _ G hge e)
  have hsub : (colorPart G (fun _ => 0) 0).cliqueFinset 2 ⊆ G.cliqueFinset 2 :=
    SimpleGraph.cliqueFinset_mono _ (colorPart_le G (fun _ => 0) 0)
  have hsup : G.cliqueFinset 2 ⊆ (colorPart G (fun _ => 0) 0).cliqueFinset 2 :=
    SimpleGraph.cliqueFinset_mono _ hge
  have hcard : (((colorPart G (fun _ => 0) 0).cliqueFinset 2).card : ℝ)
      = ((G.cliqueFinset 2).card : ℝ) := by
    congr 2
    exact Finset.Subset.antisymm hsub hsup
  refine ⟨1, fun _ => 0, fun _ => d, fun i _ => hd, ?_, ?_, ?_⟩
  · intro i hi e he
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    rw [hdeg]
    exact hhi e (hsub he)
  · intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    refine ⟨Exc, by rw [hcard]; exact hExc, ?_⟩
    intro e he hne
    rw [hdeg]
    exact hlo e (hsub he) hne
  · have hstar : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
    have hnn : (0 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
    simp only [Finset.sum_range_one]
    rw [hcard]
    linarith

end Nibble.AX1

end


/-! # CoreGapRegularFamily -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Edge-disjoint families and the colouring they induce -/

/-- The first `k` members of the family `H` are pairwise edge-disjoint. -/
@[expose]
def EdgeDisjointFamily (H : ℕ → SimpleGraph V) (k : ℕ) : Prop :=
  ∀ i < k, ∀ j < k, i ≠ j → ∀ x y, (H i).Adj x y → ¬ (H j).Adj x y

/-- A pair `{x, y}` of distinct vertices is a `2`-clique of `H` iff `x` and `y` are adjacent. -/
theorem pair_mem_cliqueFinset_two (H : SimpleGraph V) [DecidableRel H.Adj] {x y : V} (hxy : x ≠ y) :
    ({x, y} : Finset V) ∈ H.cliqueFinset 2 ↔ H.Adj x y := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, Finset.card_pair hxy]
  simp [hxy]

/-- The `2`-cliques of two equal graphs agree, whatever the decidability instances. -/
theorem cliqueFinset_congr_graph {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj]
    [DecidableRel G₂.Adj] (h : G₁ = G₂) (n : ℕ) : G₁.cliqueFinset n = G₂.cliqueFinset n := by
  subst h; congr!

/-- Triangle degrees of two equal graphs agree, whatever the decidability instances. -/
theorem edgeTriangleDegree_congr_graph {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj]
    [DecidableRel G₂.Adj] (h : G₁ = G₂) (e : Finset V) :
    edgeTriangleDegree G₁ e = edgeTriangleDegree G₂ e := by
  subst h; congr!

open Classical in
/-- The edge colouring induced by an edge-disjoint family: an edge gets the index of the member of
the family containing it, and the junk colour `k` if there is none. -/
noncomputable def familyColoring (H : ℕ → SimpleGraph V) (k : ℕ) (e : Finset V) : ℕ :=
  if h : ∃ i, i < k ∧ e ∈ (H i).cliqueFinset 2 then Nat.find h else k

/-- The colour classes of `Nibble.AX1.familyColoring` are exactly the members of the family. -/
theorem colorPart_familyColoring (G : SimpleGraph V) (H : ℕ → SimpleGraph V)
    (k : ℕ) (hle : ∀ i < k, H i ≤ G) (hdisj : EdgeDisjointFamily H k) {i : ℕ} (hi : i < k) :
    colorPart G (familyColoring H k) i = H i := by
  classical
  ext x y
  rw [colorPart, edgeSelect_adj]
  constructor
  · rintro ⟨hG, hcol⟩
    have hxy : x ≠ y := hG.ne
    rw [familyColoring] at hcol
    by_cases hex : ∃ j, j < k ∧ ({x, y} : Finset V) ∈ (H j).cliqueFinset 2
    · rw [dite_eq_left hex] at hcol
      have hspec := Nat.find_spec hex
      rw [hcol] at hspec
      exact (pair_mem_cliqueFinset_two (H i) hxy).mp hspec.2
    · rw [dite_eq_right hex] at hcol
      exact absurd hcol.symm (Nat.ne_of_lt hi)
  · intro hHi
    have hxy : x ≠ y := hHi.ne
    refine ⟨hle i hi hHi, ?_⟩
    have hex : ∃ j, j < k ∧ ({x, y} : Finset V) ∈ (H j).cliqueFinset 2 :=
      ⟨i, hi, (pair_mem_cliqueFinset_two (H i) hxy).mpr hHi⟩
    rw [familyColoring, dite_eq_left hex]
    obtain ⟨hjk, hjmem⟩ := Nat.find_spec hex
    have hjadj : (H (Nat.find hex)).Adj x y :=
      (pair_mem_cliqueFinset_two (H (Nat.find hex)) hxy).mp hjmem
    by_contra hne
    exact hdisj (Nat.find hex) hjk i hi hne x y hjadj hHi

/-! ### The family form of the structural residual -/

open Classical in
/-- **A near-regular family for `G` at parameters `(ε, μ, η, d₀)`**: pairwise edge-disjoint
subgraphs `H 0, …, H (k−1)` of `G`, each with near-regular triangle degrees at its own scale
`d i ≥ d₀` (the lower bound being allowed to fail on at most an `η`-fraction of that member's
edges), whose total edge count is at least `3ν₃*(G) − 3ε|V|²`. -/
@[expose]
def HasNearRegularFamily (G : SimpleGraph V) [DecidableRel G.Adj] (ε μ η d₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (H : ℕ → SimpleGraph V) (d : ℕ → ℝ),
    (∀ i < k, H i ≤ G) ∧
    EdgeDisjointFamily H k ∧
    (∀ i < k, d₀ ≤ d i) ∧
    (∀ i < k, ∀ e ∈ (H i).cliqueFinset 2,
      (edgeTriangleDegree (H i) e : ℝ) ≤ (1 + μ) * d i) ∧
    (∀ i < k, ∃ Exc : Finset (Finset V),
      (Exc.card : ℝ) ≤ η * (((H i).cliqueFinset 2).card : ℝ) ∧
      ∀ e ∈ (H i).cliqueFinset 2, e ∉ Exc →
        (1 - μ) * d i ≤ (edgeTriangleDegree (H i) e : ℝ)) ∧
    nu3star G ≤ (∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) / 3)
      + ε * (Fintype.card V : ℝ) ^ 2

/-- Weakening the accuracy of a near-regular family. -/
theorem HasNearRegularFamily.mono_eps {G : SimpleGraph V} [DecidableRel G.Adj] {ε ε' μ η d₀ : ℝ}
    (h : HasNearRegularFamily G ε μ η d₀) (hεε' : ε ≤ ε') :
    HasNearRegularFamily G ε' μ η d₀ := by
  obtain ⟨k, H, d, hle, hdisj, hd, hhi, hlo, hval⟩ := h
  refine ⟨k, H, d, hle, hdisj, hd, hhi, hlo, ?_⟩
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith only [hεε', hval]

/-- **A family for a spanning subgraph is a family for the graph.**  If `G' ≤ G` and the fractional
optimum drops by at most `c|V|²` when passing to `G'`, a near-regular family for `G'` is one for
`G` at accuracy `ε + c`. -/
theorem HasNearRegularFamily.mono_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] {ε c μ η d₀ : ℝ} (hle : G' ≤ G)
    (hgap : nu3star G ≤ nu3star G' + c * (Fintype.card V : ℝ) ^ 2)
    (h : HasNearRegularFamily G' ε μ η d₀) :
    HasNearRegularFamily G (ε + c) μ η d₀ := by
  obtain ⟨k, H, d, hleH, hdisj, hd, hhi, hlo, hval⟩ := h
  refine ⟨k, H, d, fun i hi => le_trans (hleH i hi) hle, hdisj, hd, hhi, hlo, ?_⟩
  have : nu3star G ≤ nu3star G' + c * (Fintype.card V : ℝ) ^ 2 := hgap
  nlinarith [hval]

/-- **The triangle-poor branch.**  A graph with fewer than `triangleRemovalBound(ε)·|V|³` triangles
has `ν₃* ≤ ε|V|²`, so the *empty* family is already a near-regular family. -/
theorem hasNearRegularFamily_of_few_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ : ℝ} (hfew : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) :
    HasNearRegularFamily G ε μ η d₀ := by
  refine ⟨0, fun _ => ⊥, fun _ => d₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · simpa using nu3star_le_of_few_triangles G hfew

/-! ### From families to colourings -/

/-- A near-regular family gives the data required by `Nibble.AX1.RegularDecompAt`. -/
theorem regularDecomp_data_of_family (G : SimpleGraph V) [DecidableRel G.Adj] {ε μ η d₀ : ℝ}
    (h : HasNearRegularFamily G ε μ η d₀) :
    ∃ (k : ℕ) (col : Finset V → ℕ) (d : ℕ → ℝ),
      (∀ i < k, d₀ ≤ d i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * d i) ∧
      (∀ i < k, ∃ Exc : Finset (Finset V),
        (Exc.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨k, H, d, hle, hdisj, hd, hhi, hlo, hval⟩ := h
  have hcp : ∀ i < k, colorPart G (familyColoring H k) i = H i := fun i hi =>
    colorPart_familyColoring G H k hle hdisj hi
  have hclique : ∀ i < k,
      (colorPart G (familyColoring H k) i).cliqueFinset 2 = (H i).cliqueFinset 2 := fun i hi =>
    cliqueFinset_congr_graph (hcp i hi) 2
  have hdeg : ∀ i < k, ∀ e : Finset V,
      edgeTriangleDegree (colorPart G (familyColoring H k) i) e = edgeTriangleDegree (H i) e :=
    fun i hi e => edgeTriangleDegree_congr_graph (hcp i hi) e
  refine ⟨k, familyColoring H k, d, hd, ?_, ?_, ?_⟩
  · intro i hi e he
    rw [hdeg i hi]
    exact hhi i hi e ((hclique i hi) ▸ he)
  · intro i hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    refine ⟨Exc, by rw [hclique i hi]; exact hExc, ?_⟩
    intro e he hne
    rw [hdeg i hi]
    exact hlo' e ((hclique i hi) ▸ he) hne
  · have hsum : ∑ i ∈ Finset.range k,
        (((colorPart G (familyColoring H k) i).cliqueFinset 2).card : ℝ) / 3
        = ∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) / 3 :=
      Finset.sum_congr rfl (fun i hi => by rw [hclique i (Finset.mem_range.mp hi)])
    rw [hsum]
    exact hval

/-- **The reduction to the family form.**  If every large graph has a near-regular family, then the
structural residual `Nibble.AX1.RegularDecompAt` holds. -/
theorem regularDecompAt_of_family {ε μ η d₀ : ℝ}
    (h : ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → HasNearRegularFamily G ε μ η d₀) :
    RegularDecompAt ε μ η d₀ := by
  obtain ⟨n₀, hmain⟩ := h
  exact ⟨n₀, fun V _ _ G _ hV => regularDecomp_data_of_family G (hmain V G hV)⟩

/-- **The converse.**  A colour decomposition *is* an edge-disjoint family, so the family form is
equivalent to `Nibble.AX1.RegularDecompAt`: nothing has been smuggled in. -/
theorem hasNearRegularFamily_of_regularDecomp {ε μ η d₀ : ℝ} (h : RegularDecompAt ε μ η d₀) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → HasNearRegularFamily G ε μ η d₀ := by
  classical
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨k, col, d, hd, hhi, hlo, hval⟩ := hmain V G hV
  refine ⟨k, fun i => colorPart G col i, d, fun i _ => colorPart_le G col i, ?_, hd, ?_, ?_, ?_⟩
  · intro i _ j _ hij x y hxi hxj
    exact hij (hxi.2 ▸ hxj.2 ▸ rfl)
  · intro i hi e he
    exact hhi i hi e he
  · intro i hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    exact ⟨Exc, hExc, hlo'⟩
  · exact hval

/-! ### Cleaning: passing to the regularity-reduced graph -/

/-- **The cleaning step.**  Mathlib's `SimpleGraph.regularityReduced` keeps only the edges lying in
an `ε₁/8`-uniform pair of parts of density at least `ε₁/4`; for a uniform equipartition with enough
parts it discards fewer than `ε₁|V|²` edges
(`SimpleGraph.regularityReduced_edges_card_aux`), and deleting `m` edges costs the fractional
optimum at most `m` (`Nibble.AX1.nu3star_le_add_deleted`).  So a near-regular family for the reduced
graph is one for `G`, at accuracy `ε + ε₁`. -/
theorem hasNearRegularFamily_of_reduced [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε₁ μ η d₀ : ℝ} (hε₁ : 0 < ε₁) (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) (hPl : 4 / ε₁ ≤ (P.parts.card : ℝ))
    (hPu : P.IsUniform G (ε₁ / 8))
    (h : HasNearRegularFamily (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀) :
    HasNearRegularFamily G (ε + ε₁) μ η d₀ := by
  classical
  set G' : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hG'
  have hle : G' ≤ G := SimpleGraph.regularityReduced_le
  have hedges := SimpleGraph.regularityReduced_edges_card_aux (G := G) (P := P) (ε := ε₁)
    hε₁ hP hPu hPl
  have hedges' : (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ)
      < ε₁ * (Fintype.card V : ℝ) ^ 2 := by
    have hcast : ((Fintype.card V ^ 2 : ℕ) : ℝ) = (Fintype.card V : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at hedges
    linarith only [hedges]
  have hcnt := card_clique2_sdiff_le G G' hle
  have hgap : nu3star G ≤ nu3star G' + ε₁ * (Fintype.card V : ℝ) ^ 2 := by
    have := nu3star_le_add_deleted G G' hle
    linarith only [hedges', hcnt, this]
  exact HasNearRegularFamily.mono_of_le hle hgap h

/-! ### The reduced residual -/

/-- **The reduced residual at parameters `(ε, μ, η, d₀)` and regularity scale `ε₁`**: every
*regularity-reduced* graph — the subgraph of a large graph `G` consisting of the edges inside the
`ε₁/8`-uniform pairs of density at least `ε₁/4` of an `ε₁/8`-uniform equipartition `P` with a
bounded number of parts — which is triangle-rich carries a near-regular family recovering `3ν₃*`
up to `3ε|V|²`.

This is what remains of `Nibble.AX1.RegularDecompResidual` after Szemerédi regularity and the
triangle removal lemma have been applied: all pairs of parts carrying edges are uniform and dense,
so the missing mathematics is the Haxell–Rödl splitting of each uniform pair among the cluster
triples together with the sparsification making the triangle degrees of each triple concentrate at
a common scale. -/
@[expose]
def ReducedFamilyAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3
      ≤ ((((G.regularityReduced P (ε₁ / 8) (ε₁ / 4))).cliqueFinset 3).card : ℝ) →
    HasNearRegularFamily (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀

/-- **The reduced residual**: at every window of parameters, *for some* regularity scale `ε₁` as
small as one likes.  The scale is existentially quantified — the cleaning loss it causes is paid for
out of the accuracy `ε` — so a proof is free to run the regularity lemma as finely as it needs. -/
@[expose]
def ReducedFamilyResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ ReducedFamilyAt ε μ η d₀ ε₁

/-- **The reduction of the structural residual to the reduced one.**  Given `ε`, apply Szemerédi's
regularity lemma at the scale `ε₁ ≤ ε/2` supplied by the residual; the reduced graph is either
triangle-poor — and then the empty family already works, by the triangle removal lemma — or
triangle-rich, and then the reduced residual applies.  Cleaning costs at most `ε₁|V|² ≤ (ε/2)|V|²`
of the fractional optimum. -/
theorem regularDecompResidual_of_reducedFamily (h : ReducedFamilyResidual) :
    RegularDecompResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁le, hε₁one, n₀, hmain⟩ := h (ε / 2) (by linarith) μ hμ η hη d₀ hd₀
  refine regularDecompAt_of_family ⟨max n₀ (max ⌈4 / ε₁⌉₊ 1), ?_⟩
  intro V _ _ G _ hV
  have hV₀ : n₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hV
  have hVl : ⌈4 / ε₁⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hV
  have hV1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hV
  have hne : Nonempty V := Fintype.card_pos_iff.mp hV1
  obtain ⟨P, hP, hPl, hPb, hPu⟩ :=
    szemeredi_regularity G (ε := ε₁ / 8) (l := ⌈4 / ε₁⌉₊) (by positivity) hVl
  have hPl' : 4 / ε₁ ≤ (P.parts.card : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hPl
  have hPb' : (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hPb
  set G' : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hG'
  have hfam : HasNearRegularFamily G' (ε / 2) μ η d₀ := by
    rcases lt_or_ge (((G'.cliqueFinset 3).card : ℝ))
      (SimpleGraph.triangleRemovalBound (ε / 2) * (Fintype.card V : ℝ) ^ 3) with hpoor | hrich
    · exact hasNearRegularFamily_of_few_triangles G' hpoor
    · exact hmain V G P hV₀ hP hPl' hPb' hPu hrich
  have := hasNearRegularFamily_of_reduced G hε₁ P hP hPl' hPu hfam
  exact this.mono_eps (by linarith)

/-- **The converse.**  The reduced residual is a *weakening* of `Nibble.AX1.RegularDecompResidual`
(reduced graphs are graphs), so by `Nibble.AX1.regularDecompResidual_of_reducedFamily` the two are
equivalent: the passage to regularity-reduced graphs smuggles in no strength. -/
theorem reducedFamilyResidual_of_regularDecompResidual (h : RegularDecompResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨n₀, hmain⟩ := hasNearRegularFamily_of_regularDecomp (h ε hε μ hμ η hη d₀ hd₀)
  refine ⟨min ε 1, lt_min hε one_pos, min_le_left _ _, min_le_right _ _, n₀, ?_⟩
  exact fun V _ _ G _ P hV _ _ _ _ _ =>
    hmain V (G.regularityReduced P (min ε 1 / 8) (min ε 1 / 4)) hV

/-- **AX1 from the reduced residual.** -/
theorem ax1_of_reducedFamily (h : ReducedFamilyResidual) : AX1Statement :=
  ax1_of_regularDecomp (regularDecompResidual_of_reducedFamily h)

end Nibble.AX1
