/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 packing gap: the low-degree core reduction and the residual `CoreGapResidual`

`Nibble.AX1.NibbleGapResidual` (`Nibble.DenseGapAX1`) is the last assumed atom of AX1: the packing
gap `ν₃* − ν₃ ≤ ε|V|²` for graphs that fail the density threshold (some vertex of degree `< θ|V|`)
but are triangle-rich.  This file does two things.

* It **removes the density threshold entirely** by a genuine graph-theoretic reduction — the
  low-degree *core*.  Repeatedly deleting all edges at a vertex of positive degree below `t` costs
  at most `t` edges per step and permanently isolates the chosen vertex, so after at most `|V|`
  steps one is left with a spanning subgraph `G'` in which every vertex is isolated or has degree
  at least `t`, at a total cost of at most `t·|V|` edges (`Nibble.AX1.exists_core`).  Deleting `k`
  edges moves `ν₃*` by at most `k` (`Nibble.AX1.nu3star_le_add_deleted`) and can only decrease `ν₃`
  (`Nibble.AX1.nu3_mono`), so the packing gap is stable under the passage to the core
  (`Nibble.AX1.gap_le_core_gap`).  Taking `t = (ε/4)|V|` this reduces `NibbleGapResidual` to the
  packing gap for graphs whose vertices are all isolated or of degree `≥ δ|V|`.

* It **proves that residual outright in the whole range `δ ∈ [1 − μ(ε)/2, 1)`**: this is the dense
  branch, but now tolerating isolated vertices, which the original `Nibble.AX1.nibbleGap_dense`
  does not.  The point is that the triangle hypergraph lives on the EDGES of `G`, so isolated
  vertices are invisible to it: all degree and codegree estimates may be taken relative to the
  support `Nibble.AX1.posDeg G` instead of `V` (`Nibble.AX1.triangleSub_degree_le_support`,
  `Nibble.AX1.triangleSub_degree_ge_support`), and the nibble is then run at scale
  `d = |support|`.

## The statements

* `Nibble.AX1.CoreGapAt ε δ` — the packing gap `ν₃* − ν₃ ≤ ε|V|²` for large graphs in which every
  vertex is isolated or has degree `≥ δ|V|`, and which are fractionally rich (`ν₃* > ε|V|²`; without
  this the conclusion is trivial).
* `Nibble.AX1.CoreGapResidual` — `∀ ε > 0, ∀ δ > 0, CoreGapAt ε δ`.
* `Nibble.AX1.nibbleGapResidual_of_coreGapResidual`,
  `Nibble.AX1.nibbleGapHyp_of_coreGapResidual`, `Nibble.AX1.ax1_of_coreGapResidual` — the machine
  checked reductions `CoreGapResidual → NibbleGapResidual → NibbleGapHyp → AX1Statement`.
* `Nibble.AX1.coreGapResidual_of_nibbleGapResidual` — the converse: the two residuals are
  equivalent, so nothing has been lost (or smuggled in) by the reformulation.
* `Nibble.AX1.coreGapAt_dense` — **unconditional**: for every `ε > 0` there is `θ < 1` with
  `CoreGapAt ε θ`; with `Nibble.AX1.CoreGapAt.mono_delta` this proves `CoreGapAt ε δ` for every
  `δ ≥ θ(ε)`.
* `Nibble.AX1.coreGapAt_of_third` — `CoreGapAt ε δ` is trivially true for `ε ≥ 1/3`.

So the *only* open instances are `CoreGapAt ε δ` with `ε < 1/3` and `0 < δ < θ(ε)`; see
`RESIDUAL.md`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost
public import Mathlib.Analysis.RCLike.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import Mathlib.Algebra.Order.Ring.Star
public import LeanPool.AsymptoticTrianglePacking.Internal.TightSchedule
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRoundAssembly
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterFracUpper
public import Mathlib.Analysis.Convex.Cone.InnerDual


/-! # YusterNibbleApply -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y5 (scaffold) — nibble ⇒ large triangle packing.** Assuming `NibbleTheorem`, there is a
near-regularity tolerance `μ > 0` such that, whenever the edge-type triangle hypergraph is
`(1±μ)`-nearly `d`-regular with codegree `≤ μd`, it has a matching (edge-disjoint triangle
packing) of
size `≥ (1-β)·|E(G)|/3`. Direct application of `NibbleTheorem` to `triangleHypergraphSub G`, using
`card_EdgeV` to turn `Fintype.card (EdgeV G)` into `|E(G)| = |cliqueFinset 2|`. -/
theorem nibble_gives_triangleSub_matching (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := hNibble 3 (by norm_num) β hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hReg hCod
  refine ⟨M, hM, ?_⟩
  rwa [card_EdgeV] at hcard

/-- **Y5 (majority) — nibble ⇒ large triangle packing, tolerating an exceptional edge set.** The
`NibbleTheoremMost` version of `nibble_gives_triangleSub_matching`: assuming the majority interface,
there are tolerances `μ, η > 0` such that whenever the edge-type triangle hypergraph is
`NearlyRegularMost d μ η` (near-`d`-regular outside an `η`-fraction of edges) with codegree `≤
μd`, it
has an edge-disjoint triangle packing of size `≥ (1-β)·|E(G)|/3`. This is the version the
Szemerédi+counting reconstruction (which yields `NearlyRegularMost`, not strict) feeds. -/
theorem nibble_gives_triangleSub_matching_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNibble 3 (by norm_num) β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hReg hCod
  refine ⟨M, hM, ?_⟩
  rwa [card_EdgeV] at hcard

end Nibble.YusterE

end



/-! # YusterSubBridge -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Sub ↦ E bridge.** A matching of the edge-vertex-type triangle hypergraph lower-bounds `nu3`:
mapping each hyperedge `T` by the subtype embedding `EdgeV G ↪ Finset V` (`T ↦ T.map emb`) turns a
matching of `triangleHypergraphSub G` into a matching of `triangleHypergraphE G` of the same
cardinality (the embedding is injective — preserves card and disjointness — and recovers the
original
`2`-subsets of each triangle since they are all `2`-cliques). Then `nu3_ge`. -/
theorem sub_matching_card_le_nu3 {M : Finset (Finset (EdgeV G))}
    (hM : IsMatching (triangleHypergraphSub G) M) : M.card ≤ nu3 G := by
  set emb : EdgeV G ↪ Finset V := Function.Embedding.subtype (· ∈ G.cliqueFinset 2) with hemb
  -- each mapped hyperedge lands in triangleHypergraphE G
  have hmem : ∀ T ∈ M, T.map emb ∈ triangleHypergraphE G := by
    intro T hT
    have hTsub := hM.subset hT
    rw [triangleHypergraphSub, Finset.mem_image] at hTsub
    obtain ⟨t, ht, rfl⟩ := hTsub
    have hclique : G.IsNClique 3 t := (SimpleGraph.mem_cliqueFinset_iff).mp ht
    have hall : ∀ x ∈ t.powersetCard 2, x ∈ G.cliqueFinset 2 :=
      powersetCard_two_subset_cliqueFinset G hclique
    have hrec : ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)).map emb = t.powersetCard 2 := by
      rw [hemb]; exact Finset.subtype_map_of_mem hall
    rw [hrec, triangleHypergraphE, Finset.mem_image]
    exact ⟨t, ht, rfl⟩
  -- the image matching of triangleHypergraphE
  have hM' : IsMatching (triangleHypergraphE G) (M.image (fun T => T.map emb)) := by
    refine ⟨?_, ?_⟩
    · intro T' hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T, hT, rfl⟩ := hT'
      exact hmem T hT
    · intro a ha b hb hab
      rw [Finset.mem_image] at ha hb
      obtain ⟨T, hT, rfl⟩ := ha
      obtain ⟨T', hT', rfl⟩ := hb
      have hTT' : T ≠ T' := fun h => hab (by rw [h])
      rw [Finset.disjoint_map]
      exact hM.disjoint T hT T' hT' hTT'
  have hcard : (M.image (fun T => T.map emb)).card = M.card :=
    Finset.card_image_of_injective M (Finset.map_injective emb)
  calc M.card = (M.image (fun T => T.map emb)).card := hcard.symm
    _ ≤ nu3 G := nu3_ge G hM'

/-- **`ν₃` lower bound from the nibble.** Assuming `NibbleTheorem` and the Y3
near-regularity/codegree
interface on `triangleHypergraphSub G`, the integral triangle-packing number satisfies
`(1-β)·|E(G)|/3 ≤ ν₃ G`. Combines Y5 (`nibble_gives_triangleSub_matching`) with the Sub ↦
`nu3` bridge.
This is the quantitative half of Y6 (the other half is `ν₃* ≤` an upper bound). -/
theorem nu3_ge_nibble (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nibble_gives_triangleSub_matching G hNibble hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hmain hd hd0 hReg hCod
  exact le_trans hcard (by exact_mod_cast sub_matching_card_le_nu3 G hM)

end Nibble.YusterE

end



/-! # Reduction to duality and rounding -/

public section

open Finset SimpleGraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PaperIII `edgesIn`: edges of `G` contained in a vertex set `t`. -/
def edgesIn (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- PaperIII `IsFracCover`: nonneg edge weights, total ≥ 1 inside each triangle. -/
def IsFracCover (y : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ t ∈ G.cliqueFinset 3, 1 ≤ ∑ e ∈ edgesIn G t, y e

/-- PaperIII `τ₃*`: the fractional triangle-cover optimum (LP value). -/
noncomputable def tau3Star : ℝ :=
  sInf {x | ∃ y : Sym2 V → ℝ, IsFracCover G y ∧ x = ∑ e ∈ G.edgeFinset, y e}

/-- **AX1 statement** (PaperIII Layer X, verbatim): the fractional–integral triangle-packing gap is
`o(n²)`, uniformly over graphs, read cover-side (`τ₃* − ν₃`). -/
@[expose] def AX1Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The strong-duality obligation** (Aristotle core `b3ee717f`): `τ₃* ≤ ν₃*` for every graph
(the reverse of the proven weak duality; together they give `τ₃* = ν₃*`). -/
def StrongDualityHyp : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    tau3Star G ≤ nu3star G

/-- **The unconditional nibble-gap obligation** (`NibbleTheoremMost` + `second-stage`
near-regularity
discharged
for all large graphs): `ν₃* − ν₃ ≤ ε n²` uniformly. -/
@[expose] def NibbleGapHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **AX1 REDUCTION.** AX1 follows from the two remaining obligations: cover-side strong duality
(`τ₃* ≤ ν₃*`) and the unconditional nibble packing gap (`ν₃* − ν₃ ≤ ε n²`). The definitional bridges
`Nibble.{nu3,nu3star} ↔ PaperIII.{nu3,nu3Star}` (already proven) make these the SAME `ν₃, ν₃*`
as AX1's. -/
theorem ax1_of_strongDuality_and_nibbleGap
    (hdual : StrongDualityHyp) (hgap : NibbleGapHyp) : AX1Statement := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hgap ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have hg := hn₀ V G hV
  have hd := hdual G
  -- τ₃* − ν₃ ≤ ν₃* − ν₃ ≤ ε n²
  linarith

end Nibble.AX1

end





/-! # Finite packing-cover LP duality -/

public section

open Finset

namespace LPDuality

/- **Abstract finite packing/cover LP (0/1 incidence).** `O` = objects (e.g. triangles),
`C` = constraints (e.g. edges); `inc o` = the constraints incident to object `o`. -/
variable {O C : Type*} [Fintype O] [Fintype C] [DecidableEq C]

/-- A fractional PACKING: nonneg object weights, total ≤ 1 across each constraint. -/
def IsPacking (inc : O → Finset C) (w : O → ℝ) : Prop :=
  (∀ o, 0 ≤ w o) ∧ ∀ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ 1

/-- A fractional COVER: nonneg constraint weights, total ≥ 1 inside each object. -/
def IsCover (inc : O → Finset C) (y : C → ℝ) : Prop :=
  (∀ c, 0 ≤ y c) ∧ ∀ o : O, 1 ≤ ∑ c ∈ inc o, y c

/-- Packing optimum (LP value). -/
noncomputable def packOpt (inc : O → Finset C) : ℝ :=
  sSup {x | ∃ w, IsPacking inc w ∧ x = ∑ o, w o}

/-- Cover optimum (LP value). -/
noncomputable def coverOpt (inc : O → Finset C) : ℝ :=
  sInf {x | ∃ y, IsCover inc y ∧ x = ∑ c, y c}

omit [Fintype C] in
private lemma zero_isPacking (inc : O → Finset C) : IsPacking inc (0 : O → ℝ) := by
  constructor <;> simp

omit [Fintype C] in
private lemma packValues_nonempty (inc : O → Finset C) :
    {x : ℝ | ∃ w, IsPacking inc w ∧ x = ∑ o, w o}.Nonempty := by
  refine ⟨0, 0, zero_isPacking inc, ?_⟩
  simp

omit [Fintype C] in
private lemma packValues_bddAbove [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) :
    BddAbove {x : ℝ | ∃ w, IsPacking inc w ∧ x = ∑ o, w o} := by
  have : Fintype C := Fintype.ofFinite C
  refine ⟨Fintype.card C, ?_⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  -- Double counting: ∑ c, ∑ o ∈ {o | c ∈ inc o}, w o = ∑ o, (inc o).card * w o
  have h1 : ∑ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ (Fintype.card C : ℝ) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset C)
      (fun c => ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) 1
    simp only [mem_univ, forall_const, card_univ, nsmul_eq_mul, mul_one] at this
    exact this (fun c => hw.2 c)
  -- Rewrite double sum: ∑ c, ∑ o ∈ {o | c ∈ inc o}, w o = ∑ o, (inc o).card * w o
  have h2 : ∑ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o = ∑ o, (inc o).card * w o := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [mul_comm]
  -- Since (inc o).card ≥ 1 and w o ≥ 0, we have w o ≤ (inc o).card * w o
  have h3 : ∑ o, w o ≤ ∑ o, (inc o).card * w o := by
    apply Finset.sum_le_sum
    intro o _
    have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
    have hwo : 0 ≤ w o := hw.1 o
    nlinarith only [hcard, hwo]
  linarith only [h1, h2, h3]

omit [Fintype C] in
private lemma packing_value_le_packOpt [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {w : O → ℝ} (hw : IsPacking inc w) :
    ∑ o, w o ≤ packOpt inc := by
  apply le_csSup (packValues_bddAbove inc hinc)
  exact ⟨w, hw, rfl⟩

omit [Fintype O] [DecidableEq C] in
private lemma coverOpt_le_value (inc : O → Finset C) {y : C → ℝ}
    (hy : IsCover inc y) : coverOpt inc ≤ ∑ c, y c := by
  unfold coverOpt
  apply csInf_le
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hx
    exact Finset.sum_nonneg fun c _ => hz.1 c
  · exact ⟨y, hy, rfl⟩

private abbrev PrimalIndex (O C : Type*) := C ⊕ O ⊕ Unit
private abbrev ConstraintIndex (O : Type*) := O ⊕ Unit
private abbrev PrimalSpace (O C : Type*) := EuclideanSpace ℝ (PrimalIndex O C)
private abbrev ConstraintSpace (O : Type*) := EuclideanSpace ℝ (ConstraintIndex O)

/-- The homogeneous map used to encode cover feasibility.  Its three nonnegative coordinate
blocks are cover weights, row slacks, and objective slack. -/
private noncomputable def coverMap (inc : O → Finset C) :
    PrimalSpace O C →L[ℝ] ConstraintSpace O :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun i => match i with
      | Sum.inl o => (∑ c ∈ inc o, x.ofLp (Sum.inl c)) - x.ofLp (Sum.inr (Sum.inl o))
      | Sum.inr _ => (∑ c, x.ofLp (Sum.inl c)) + x.ofLp (Sum.inr (Sum.inr ())))
    map_add' := by
      intros x y
      apply WithLp.ofLp_injective
      ext i
      cases i with
      | inl o => simp [Finset.sum_add_distrib]; ring
      | inr u => simp [Finset.sum_add_distrib]; ring
    map_smul' := by
      intros m x
      apply WithLp.ofLp_injective
      ext i
      cases i with
      | inl o => simp [← Finset.mul_sum]; ring
      | inr u => simp [← Finset.mul_sum]; ring }

omit [DecidableEq C] in
private lemma coverMap_apply_row (inc : O → Finset C) (x : PrimalSpace O C) (o : O) :
    (coverMap inc x).ofLp (Sum.inl o) =
      (∑ c ∈ inc o, x.ofLp (Sum.inl c)) - x.ofLp (Sum.inr (Sum.inl o)) := rfl

omit [DecidableEq C] in
private lemma coverMap_apply_value (inc : O → Finset C) (x : PrimalSpace O C) :
    (coverMap inc x).ofLp (Sum.inr ()) =
      (∑ c, x.ofLp (Sum.inl c)) + x.ofLp (Sum.inr (Sum.inr ())) := rfl

private def coverRhs (a : ℝ) : ConstraintSpace O := WithLp.toLp 2 (fun i =>
  match i with
  | Sum.inl _ => 1
  | Sum.inr _ => a)

private def nonnegativePointed (I : Type*) :
    PointedCone ℝ (EuclideanSpace ℝ I) := PointedCone.ofConeComb
  {x | ∀ i, 0 ≤ x.ofLp i} ⟨0, by simp⟩ (by
    intro x hx y hy a ha b hb i
    simpa only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      using add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)))

private lemma nonnegative_isClosed (I : Type*) :
    IsClosed ({x : EuclideanSpace ℝ I | ∀ i, 0 ≤ x.ofLp i}) := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le continuous_const
  fun_prop

private noncomputable def nonnegativeCone (I : Type*) :
    ProperCone ℝ (EuclideanSpace ℝ I) where
  toSubmodule := nonnegativePointed I
  isClosed' := nonnegative_isClosed I

private lemma mem_nonnegativeCone {I : Type*}
    {x : EuclideanSpace ℝ I} : x ∈ nonnegativeCone I ↔ ∀ i, 0 ≤ x.ofLp i := Iff.rfl

private def IsCoverCertificate (inc : O → Finset C) (q : ConstraintSpace O) : Prop :=
  (∀ o, q.ofLp (Sum.inl o) ≤ 0) ∧
  0 ≤ q.ofLp (Sum.inr ()) ∧
  ∀ c, 0 ≤ q.ofLp (Sum.inr ()) +
    ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q.ofLp (Sum.inl o)

/-- Testing the adjoint-dual condition on coordinate vectors gives the familiar sign and
transpose inequalities for a Farkas certificate. -/
private lemma adjoint_mem_innerDual_implies_certificate (inc : O → Finset C)
    (q : ConstraintSpace O)
    (hq : (ContinuousLinearMap.adjoint (coverMap inc)) q ∈
      ProperCone.innerDual (nonnegativeCone (PrimalIndex O C) : Set (PrimalSpace O C))) :
    IsCoverCertificate inc q := by
  classical
  unfold IsCoverCertificate
  rw [ProperCone.mem_innerDual] at hq
  constructor
  · -- ∀ o, q.ofLp (Sum.inl o) ≤ 0
    intro o
    -- Test with unit vector at position Sum.inr (Sum.inl o)
    let x : PrimalSpace O C := EuclideanSpace.single (Sum.inr (Sum.inl o)) 1
    have hx : x ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [x, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have h := hq hx
    -- Use adjointness: inner x ((coverMap).adjoint q) = inner (coverMap x) q
    rw [ContinuousLinearMap.adjoint_inner_right] at h
    -- Compute coverMap inc x for x = single (inr (inl o)) 1
    -- Compute (coverMap inc x).ofLp for our test vector
    have hx_inl : ∀ c : C, x.ofLp (Sum.inl c) = 0 := by
      intro c
      simp [x]
    have hx_inr_inl : ∀ o' : O, x.ofLp (Sum.inr (Sum.inl o')) = if o' = o then 1 else 0 := by
      intro o'
      classical
      simp [x]
    have hx_inr_inr : x.ofLp (Sum.inr (Sum.inr ())) = 0 := by simp [x]
    have hcm_inl : ∀ o' : O, (coverMap inc x).ofLp (Sum.inl o') = -if o' = o then 1 else 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hx_inl, hx_inr_inl]
    have hcm_inr : (coverMap inc x).ofLp (Sum.inr ()) = 0 := by
      rw [coverMap_apply_value]
      simp [hx_inl, hx_inr_inr]
    -- Compute inner (coverMap inc x) q = -q.ofLp (Sum.inl o)
    have hinner : inner ℝ (coverMap inc x) q = -q.ofLp (Sum.inl o) := by
      simp [inner, hcm_inl, hcm_inr]
    linarith only [h, hinner]
  constructor
  · -- 0 ≤ q.ofLp (Sum.inr ())
    -- Test with unit vector at position Sum.inr (Sum.inr ())
    let y : PrimalSpace O C := EuclideanSpace.single (Sum.inr (Sum.inr ())) 1
    have hy : y ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [y, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have hyq := hq hy
    rw [ContinuousLinearMap.adjoint_inner_right] at hyq
    -- coverMap inc y has value 1 at Sum.inr () and 0 elsewhere
    have hyv_inl : ∀ c : C, y.ofLp (Sum.inl c) = 0 := by
      intro c
      simp [y]
    have hyv_inr_inl : ∀ o' : O, y.ofLp (Sum.inr (Sum.inl o')) = 0 := by
      intro o'
      simp [y]
    have hyv_inr_inr : y.ofLp (Sum.inr (Sum.inr ())) = 1 := by simp [y]
    have hymv : (coverMap inc y).ofLp (Sum.inr ()) = 1 := by
      rw [coverMap_apply_value]
      simp [hyv_inl, hyv_inr_inr]
    have hymv' : ∀ o' : O, (coverMap inc y).ofLp (Sum.inl o') = 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hyv_inl, hyv_inr_inl]
    simp only [inner, star_trivial, RCLike.mul_re, RCLike.re_to_real,
      RCLike.im_to_real, mul_zero, sub_zero, Fintype.sum_sum_type, hymv',
      sum_const_zero, univ_unique, PUnit.default_eq_unit, hymv, mul_one,
      sum_singleton, zero_add] at hyq
    exact hyq
  · -- ∀ c, 0 ≤ q.ofLp (Sum.inr ()) + ∑ o with c ∈ inc o, q.ofLp (Sum.inl o)
    intro c₀
    -- Test with unit vector at position Sum.inl c₀
    let z : PrimalSpace O C := EuclideanSpace.single (Sum.inl c₀) 1
    have hz : z ∈ nonnegativeCone (PrimalIndex O C) := by
      rw [mem_nonnegativeCone]
      intro i
      simp only [z, EuclideanSpace.single]
      simp
      split_ifs <;> norm_num
    have hzq := hq hz
    rw [ContinuousLinearMap.adjoint_inner_right] at hzq
    -- Compute coverMap inc z
    have hz_inl : ∀ c : C, z.ofLp (Sum.inl c) = if c = c₀ then 1 else 0 := by
      intro c
      simp [z]
    have hz_inr_inl : ∀ o' : O, z.ofLp (Sum.inr (Sum.inl o')) = 0 := by
      intro o'
      simp [z]
    have hz_inr_inr : z.ofLp (Sum.inr (Sum.inr ())) = 0 := by simp [z]
    have hzv : (coverMap inc z).ofLp (Sum.inr ()) = 1 := by
      rw [coverMap_apply_value]
      simp [hz_inl, hz_inr_inr]
    have hzm : ∀ o' : O, (coverMap inc z).ofLp (Sum.inl o') = if c₀ ∈ inc o' then 1 else 0 := by
      intro o'
      rw [coverMap_apply_row]
      simp [hz_inl, hz_inr_inl]
    simp only [inner, star_trivial, RCLike.mul_re, RCLike.re_to_real,
      RCLike.im_to_real, mul_zero, sub_zero, Fintype.sum_sum_type, hzm,
      mul_ite, mul_one, univ_unique, PUnit.default_eq_unit, hzv,
      sum_singleton] at hzq
    convert hzq using 1
    simp [Finset.sum_filter]
    ring

omit [Fintype C] in
/-- The elementary normalization step: a certificate with positive last coordinate gives a
packing by `w o = -q o / q_last`; if that coordinate vanishes, nonempty rows force `q = 0`. -/
private lemma certificate_nonneg [Finite C] (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a)
    (q : ConstraintSpace O) (hq : IsCoverCertificate inc q) :
    0 ≤ inner ℝ (coverRhs a) q := by
  have : Fintype C := Fintype.ofFinite C
  -- Extract certificate properties
  obtain ⟨hq_neg, hq_last, hq_constraint⟩ := hq
  -- Set up abbreviations
  set q_last := q.ofLp (Sum.inr ()) with hq_last_def
  set q_o := fun o => q.ofLp (Sum.inl o) with hq_o_def
  -- Rewrite inner product
  simp only [inner]
  -- inner ℝ on ℝ is multiplication
  have h_inner : ∀ (r s : ℝ), inner ℝ r s = r * s := fun r s => mul_comm s r
  simp only [star_trivial, RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real,
    mul_zero, sub_zero, Fintype.sum_sum_type, univ_unique, PUnit.default_eq_unit,
    sum_singleton, ge_iff_le]
  -- Simplify coverRhs values
  have h_coverRhs_inl : ∀ o : O, (coverRhs a).ofLp (Sum.inl o) = 1 := by
    intro o; rfl
  have h_coverRhs_inr : (coverRhs a).ofLp (Sum.inr (α := O) ()) = a := by rfl
  simp only [h_coverRhs_inl, mul_one, h_coverRhs_inr, ge_iff_le]
    at hq_constraint hq_neg hq_last ⊢
  -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
  -- Note: Sum.inr PUnit.unit = Sum.inr () in ConstraintIndex = O ⊕ Unit
  have inr_eq : (Sum.inr PUnit.unit : O ⊕ Unit) = Sum.inr () := rfl
  rw [inr_eq]
  -- Case split on whether q_last = 0
  by_cases hq_last_zero : q_last = 0
  · -- Case q_last = 0: constraint sums must all be 0, so each q_o = 0
    -- First establish a ≥ 0
    have ha_nonneg : 0 ≤ a := by
      have h_packOpt_nonneg : 0 ≤ packOpt inc := by
        apply le_csSup (packValues_bddAbove inc hinc)
        exact ⟨0, zero_isPacking inc, by simp⟩
      linarith only [ha, h_packOpt_nonneg]
    rw [← hq_last_def, hq_last_zero, zero_mul]
    -- From hq_constraint and hq_neg: all q_o must be 0
    have h_q_o_zero : ∀ o, q.ofLp (Sum.inl o) = 0 := by
      intro o
      obtain ⟨c, hc⟩ := hinc o
      have hsum := hq_constraint c
      simp only [hq_last_zero, hq_o_def, zero_add] at hsum
      -- hsum : 0 ≤ ∑ o ∈ {o | c ∈ inc o}, q.ofLp (Sum.inl o)
      -- Each term is ≤ 0, so sum ≤ 0. Thus sum = 0.
      have hsum_neg : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q.ofLp (Sum.inl o) ≤ 0 := by
        apply Finset.sum_nonpos
        intro o _
        exact hq_neg o
      have hsum_eq : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o),
          q.ofLp (Sum.inl o) = 0 := by
        linarith only [hsum, hsum_neg]
      -- Since o is in the filter and sum = 0 with all terms ≤ 0, q.ofLp (Sum.inl o) = 0
      have ho_in_filter : o ∈ Finset.univ.filter (fun o => c ∈ inc o) := by simp [hc]
      have h_eq_zero := Finset.sum_eq_zero_iff_of_nonpos (fun o _ => hq_neg o) |>.mp hsum_eq
      exact h_eq_zero o ho_in_filter
    simp [h_q_o_zero]
  · -- Case q_last > 0: use sum of constraints
    have hq_last_pos : 0 < q_last := lt_of_le_of_ne hq_last (Ne.symm hq_last_zero)
    have ha_nonneg : 0 ≤ a := by
      have h_packOpt_nonneg : 0 ≤ packOpt inc := by
        apply le_csSup (packValues_bddAbove inc hinc)
        exact ⟨0, zero_isPacking inc, by simp⟩
      linarith only [ha, h_packOpt_nonneg]
    -- Rewrite goal using q_last
    rw [← hq_last_def]
    -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
    -- Sum constraint inequalities
    have h_sum_cons : ∑ c : C,
        (q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o) ≥ 0 := by
      apply Finset.sum_nonneg
      intro c _
      exact hq_constraint c
    -- Expand sum: C * q_last + ∑ c, ∑ o with c ∈ inc o, q_o o
    have h_expand : ∑ c : C, (q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o) =
        Fintype.card C * q_last +
          ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o := by
      simp [Finset.sum_add_distrib]
    -- Double sum: ∑ c, ∑ o with c ∈ inc o, q_o o = ∑ o, (inc o).card * q_o o
    have h_double_sum : ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o =
        ∑ o : O, (inc o).card * q_o o := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    -- Since (inc o).card ≥ 1 and q_o o ≤ 0: (inc o).card * q_o o ≤ q_o o
    have h_card_mul_le : ∑ o : O, (inc o).card * q_o o ≤ ∑ o : O, q_o o := by
      apply Finset.sum_le_sum
      intro o _
      have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
      nlinarith [hq_neg o]
    -- Therefore: C * q_last + ∑ o, q_o o ≥ C * q_last + ∑ o, (inc o).card * q_o o ≥ 0
    have h_bound : Fintype.card C * q_last + ∑ o : O, q_o o ≥ 0 := by
      linarith only [h_sum_cons, h_expand, h_double_sum, h_card_mul_le]
    -- packOpt inc ≤ Fintype.card C
    have h_packOpt_le_C : packOpt inc ≤ Fintype.card C := by
      rw [packOpt]
      apply csSup_le (packValues_nonempty inc)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hx
      -- Each constraint: ∑ o with c ∈ inc o, w o ≤ 1
      -- Summing: ∑ c, ∑ o with c ∈ inc o, w o ≤ C
      -- Double sum = ∑ o, (inc o).card * w o ≥ ∑ o, w o (since card ≥ 1 and w ≥ 0)
      have h_sum_cons : ∑ c : C,
          ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ Fintype.card C := by
        have := Finset.sum_le_card_nsmul Finset.univ
          (fun c => ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) 1
        simp only [mem_univ, forall_const, card_univ, nsmul_eq_mul, mul_one] at this
        exact this fun c => hw.2 c
      have h_double_sum : ∑ c : C, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o =
          ∑ o : O, (inc o).card * w o := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp [mul_comm]
      have h_le : ∑ o : O, w o ≤ ∑ o : O, (inc o).card * w o := by
        apply Finset.sum_le_sum
        intro o _
        have hcard : (1 : ℝ) ≤ (inc o).card := by exact_mod_cast Finset.card_pos.mpr (hinc o)
        nlinarith [hw.1 o]
      linarith only [h_sum_cons, h_double_sum, h_le]
    -- Now use that normalized certificate gives a packing with value ≤ packOpt inc < a
    -- Define normalized packing: w o = -q_o o / q_last
    let w : O → ℝ := fun o => -q_o o / q_last
    have hw_nonneg : ∀ o, 0 ≤ w o := by
      intro o
      simp only [w]
      apply div_nonneg
      · linarith only [hq_neg o]
      · exact hq_last
    have hw_constraint : ∀ c, ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o ≤ 1 := by
      intro c
      simp only [w]
      have hc := hq_constraint c
      -- hc : 0 ≤ q_last + ∑ o with c ∈ inc o, q_o o
      have : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), -q_o o / q_last =
          (-1 / q_last) * ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o := by
        rw [Finset.mul_sum]
        congr 1
        ext o
        ring
      rw [this]
      -- Need: (-1 / q_last) * S ≤ 1 where S = ∑ o with c ∈ inc o, q_o o
      -- From hc: q_last + S ≥ 0, so S ≥ -q_last
      -- So (-1/q_last) * S ≤ (-1/q_last) * (-q_last) = 1 (since q_last > 0)
      have hc' : q_last + ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o ≥ 0 := hc
      have hS_ge : ∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), q_o o ≥ -q_last := by
        linarith only [hc']
      have hq_last_ne : q_last ≠ 0 := ne_of_gt hq_last_pos
      field_simp
      nlinarith only [hS_ge]
    have hw : IsPacking inc w := ⟨hw_nonneg, hw_constraint⟩
    have h_w_value : ∑ o : O, w o ≤ packOpt inc := packing_value_le_packOpt inc hinc hw
    -- h_w_value : ∑ o, -q_o o / q_last ≤ packOpt inc
    -- i.e., -∑ o, q_o o / q_last ≤ packOpt inc
    -- i.e., ∑ o, q_o o ≥ -packOpt inc * q_last
    have h_sum_rewrite : ∑ o : O, w o = (-1 / q_last) * ∑ o : O, q_o o := by
      rw [Finset.mul_sum]
      congr 1
      ext o
      ring
    rw [h_sum_rewrite] at h_w_value
    -- h_w_value : (-1 / q_last) * ∑ o, q_o o ≤ packOpt inc
    -- Multiply by q_last: -∑ o, q_o o ≤ packOpt inc * q_last
    have hq_last_ne : q_last ≠ 0 := ne_of_gt hq_last_pos
    field_simp at h_w_value
    -- h_w_value : -∑ o, q_o o ≤ packOpt inc * q_last
    have h_lower_bound : ∑ o : O, q_o o ≥ -packOpt inc * q_last := by linarith only [h_w_value]
    -- Goal: 0 ≤ ∑ o, q_o o + q_last * a
    -- We have ∑ o, q_o o ≥ -packOpt inc * q_last
    -- So ∑ o, q_o o + q_last * a ≥ -packOpt inc * q_last + q_last * a,
    -- which is q_last * (a - packOpt inc) > 0.
    nlinarith only [ha, hq_last_pos, h_lower_bound]

/-- The Farkas certificate inequality.  This is the algebraic heart of duality: a certificate
against cover feasibility, after normalization by its last coordinate, is a packing. -/
private lemma cover_certificate_nonneg (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a)
    (q : ConstraintSpace O)
    (hq : (ContinuousLinearMap.adjoint (coverMap inc)) q ∈
      ProperCone.innerDual (nonnegativeCone (PrimalIndex O C) : Set (PrimalSpace O C))) :
    0 ≤ inner ℝ (coverRhs a) q := by
  exact certificate_nonneg inc hinc ha q (adjoint_mem_innerDual_implies_certificate inc q hq)

/-- Farkas' lemma puts the desired right-hand side in the closure of the image of the
nonnegative orthant. -/
private lemma coverRhs_mem_conic_closure (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a) :
    coverRhs a ∈ (nonnegativeCone (PrimalIndex O C)).map (coverMap inc) := by
  simp only [ProperCone.map]
  refine ProperCone.relative_hyperplane_separation.mpr ?_
  intro y hy
  exact cover_certificate_nonneg inc hinc ha y hy

omit [DecidableEq C] in
/-- A point of the conic image closure gives covers whose values approach the encoded objective.
The row error is repaired by scaling by `1 / (1 - ε)`. -/
private lemma coverOpt_le_ratio_of_mem_closure (inc : O → Finset C) {a ε : ℝ}
    (hmem : coverRhs a ∈ (nonnegativeCone (PrimalIndex O C)).map (coverMap inc))
    (hε : 0 < ε) (hε1 : ε < 1) :
    coverOpt inc ≤ (a + ε) / (1 - ε) := by
  rw [ProperCone.mem_map] at hmem
  -- hmem : coverRhs a ∈ closure of the image
  -- Use that closure is the topological closure
  let S := PointedCone.map (coverMap inc).toLinearMap
    (nonnegativeCone (PrimalIndex O C)).toPointedCone
  have hmem' : coverRhs a ∈ closure (S : Set (ConstraintSpace O)) := hmem
  rw [Metric.mem_closure_iff] at hmem'
  -- Choose δ small enough so that the error can be repaired by scaling
  set δ := min (ε / 2) (1 / 4) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨b, hb_S, hb_dist⟩ := hmem' δ hδ_pos
  -- b ∈ S means there exists x in nonnegativeCone with coverMap inc x = b
  obtain ⟨x, hx_cone, hx_eq⟩ := hb_S
  -- Define y c = x.ofLp (Sum.inl c), which is nonnegative
  let y : C → ℝ := fun c => x.ofLp (Sum.inl c)
  have hy_nonneg : ∀ c, 0 ≤ y c := by
    intro c
    have : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
    rw [mem_nonnegativeCone] at this
    exact this _
  -- From coverMap inc x = b and dist (coverRhs a) b < δ
  -- The row sums and value are close to those of coverRhs a
  have h_coord_bound : ∀ i, |(coverRhs a).ofLp i - b.ofLp i| < δ := by
    intro i
    have h1 : dist (coverRhs a) b < δ := hb_dist
    have h2 : |(coverRhs a).ofLp i - b.ofLp i| ≤ ‖(coverRhs a : ConstraintSpace O) - b‖ := by
      have hnn : ((coverRhs a).ofLp i - b.ofLp i) ^ 2 ≤
          ‖(coverRhs a : ConstraintSpace O) - b‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        have heq : ∀ j, ‖(coverRhs a - b).ofLp j‖ ^ 2 = ((coverRhs a).ofLp j - b.ofLp j) ^ 2 := by
          intro j
          simp [Real.norm_eq_abs]
        simp_rw [heq]
        apply Finset.single_le_sum (f := fun j => ((coverRhs a).ofLp j - b.ofLp j) ^ 2)
        · intros; positivity
        · simp
      have := Real.abs_le_sqrt hnn
      rwa [Real.sqrt_sq (norm_nonneg _)] at this
    rw [dist_eq_norm] at h1
    exact lt_of_le_of_lt h2 h1
  -- From coverMap inc x = b, derive bounds on row sums
  -- For each object o: row_sum o = 1 + x.ofLp (Sum.inr (Sum.inl o)) ≥ 1
  -- But b is close to coverRhs a, so row_sum o is close to 1
  have h_row_sum_bound : ∀ o, 1 - δ < ∑ c ∈ inc o, y c := by
    intro o
    have h1 : |(coverRhs a).ofLp (Sum.inl o) - b.ofLp (Sum.inl o)| < δ := h_coord_bound (Sum.inl o)
    have h2 : b.ofLp (Sum.inl o) = (∑ c ∈ inc o, y c) - x.ofLp (Sum.inr (Sum.inl o)) := by
      rw [← hx_eq]
      rfl
    rw [h2] at h1
    have hx_nonneg : 0 ≤ x.ofLp (Sum.inr (Sum.inl o)) := by
      have hx' : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
      rw [mem_nonnegativeCone] at hx'
      exact hx' _
    have h1' := abs_lt.mp h1
    simp at h1'
    have hca : (coverRhs a).ofLp (Sum.inl o) = 1 := rfl
    linarith only [hx_nonneg, h1', hca]
  -- Bound on the total sum
  have h_total_sum_bound : ∑ c, y c < a + δ := by
    have h1 : |(coverRhs a).ofLp (Sum.inr PUnit.unit) -
        b.ofLp (Sum.inr PUnit.unit)| < δ := h_coord_bound (Sum.inr PUnit.unit)
    have h2 : b.ofLp (Sum.inr PUnit.unit) = (∑ c, y c) + x.ofLp (Sum.inr (Sum.inr ())) := by
      rw [← hx_eq]
      rfl
    rw [h2] at h1
    have hx_nonneg : 0 ≤ x.ofLp (Sum.inr (Sum.inr ())) := by
      have hx' : x ∈ nonnegativeCone (PrimalIndex O C) := hx_cone
      rw [mem_nonnegativeCone] at hx'
      exact hx' _
    have h1' := abs_lt.mp h1
    simp at h1'
    have hca : (coverRhs a : ConstraintSpace O).ofLp (Sum.inr PUnit.unit) = a := by simp [coverRhs]
    linarith only [hx_nonneg, h1', hca]
  -- δ ≤ ε/2 < ε and δ ≤ 1/4 < 1
  have hδ_le : δ ≤ ε / 2 := min_le_left _ _
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num : (1 : ℝ) / 4 < 1)
  -- Since ∑ c, y c ≥ 0 and ∑ c, y c < a + δ, we have a > -δ ≥ -1/4 > -1
  have ha_gt : a > -δ := by
    have hy_sum_nonneg : 0 ≤ ∑ c, y c := Finset.sum_nonneg fun c _ => hy_nonneg c
    linarith [h_total_sum_bound]
  have ha_ge_neg1 : a ≥ -1 := by linarith only [hδ_lt1, ha_gt]
  -- Define scaled cover z = y / (1 - δ)
  set z : C → ℝ := fun c => y c / (1 - δ) with hz_def
  -- z is nonnegative
  have hz_nonneg : ∀ c, 0 ≤ z c := by
    intro c
    exact div_nonneg (hy_nonneg c) (by linarith)
  -- z is a valid cover: ∑ c ∈ inc o, z c > 1
  have hz_cover : ∀ o, 1 ≤ ∑ c ∈ inc o, z c := by
    intro o
    have := h_row_sum_bound o
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    calc 1 = (1 - δ) / (1 - δ) := by field_simp
      _ ≤ (∑ c ∈ inc o, y c) / (1 - δ) := by
        apply div_le_div_of_nonneg_right this.le (le_of_lt h1mδ_pos)
      _ = ∑ c ∈ inc o, y c / (1 - δ) := by rw [← Finset.sum_div]
      _ = ∑ c ∈ inc o, z c := by rfl
  -- z is a cover
  have hz_isCover : IsCover inc z := ⟨hz_nonneg, hz_cover⟩
  -- coverOpt inc ≤ ∑ c, z c
  have h_coverOpt_le : coverOpt inc ≤ ∑ c, z c := coverOpt_le_value inc hz_isCover
  -- ∑ c, z c = (∑ c, y c) / (1 - δ) < (a + δ) / (1 - δ)
  have h_sum_z_bound : ∑ c, z c < (a + δ) / (1 - δ) := by
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    calc ∑ c, z c = ∑ c, y c / (1 - δ) := by rfl
      _ = (∑ c, y c) / (1 - δ) := by rw [← Finset.sum_div]
      _ < (a + δ) / (1 - δ) := by apply div_lt_div_of_pos_right h_total_sum_bound h1mδ_pos
  -- (a + δ) / (1 - δ) ≤ (a + ε) / (1 - ε) since δ ≤ ε/2 < ε
  have h_ratio_bound : (a + δ) / (1 - δ) ≤ (a + ε) / (1 - ε) := by
    have h1mε_pos : 0 < 1 - ε := by linarith only [hε1]
    have h1mδ_pos : 0 < 1 - δ := by linarith only [hδ_lt1]
    field_simp
    nlinarith [hδ_le, ha_ge_neg1]
  linarith only [h_coverOpt_le, h_sum_z_bound, h_ratio_bound]

/-- Approximate conic feasibility can be repaired (by a uniform scaling) to an actual cover.
Consequently every strict upper bound on the packing optimum bounds the cover infimum. -/
private lemma coverOpt_le_of_packOpt_lt (inc : O → Finset C)
    (hinc : ∀ o, (inc o).Nonempty) {a : ℝ} (ha : packOpt inc < a) :
    coverOpt inc ≤ a := by
  by_contra h
  push Not at h
  -- coverRhs a is in the conic image
  have hmem := coverRhs_mem_conic_closure inc hinc ha
  -- For any ε ∈ (0,1), coverOpt inc ≤ (a + ε) / (1 - ε)
  have hbound : ∀ ε, 0 < ε → ε < 1 → coverOpt inc ≤ (a + ε) / (1 - ε) := by
    intros ε hε hε1
    exact coverOpt_le_ratio_of_mem_closure inc hmem hε hε1
  -- Choose ε small enough so that (a + ε) / (1 - ε) < coverOpt inc
  -- Since coverOpt inc ≥ 0 (covers are nonnegative), 1 + coverOpt inc > 0
  set c := coverOpt inc with hc_def
  have hc_nonneg : 0 ≤ c := by
    unfold coverOpt at hc_def
    apply Real.sInf_nonneg
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Finset.sum_nonneg fun _ _ => hy.1 _
  have h_one_plus_c : 0 < 1 + c := by linarith only [hc_nonneg]
  set δ := c - a with hδ_def
  have hδ : 0 < δ := by linarith only [h]
  -- Choose ε = min(1/2, (c - a) / (2 * (1 + c)))
  set ε := min (1/2) ((c - a) / (2 * (1 + c))) with hε_def
  have hε_pos : 0 < ε := by
    apply lt_min
    · norm_num
    · exact div_pos hδ (by linarith)
  have hε_lt_1 : ε < 1 := by
    have := min_le_left (1/2) ((c - a) / (2 * (1 + c)))
    linarith only [this]
  have hε_bound : ε * (1 + c) < δ := by
    have h1 : ε ≤ (c - a) / (2 * (1 + c)) := min_le_right _ _
    have h2 : ε * (1 + c) ≤ (c - a) / 2 := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ 1 + c)
      field_simp at this ⊢
      linarith only [this]
    linarith only [hδ, h2]
  -- Now derive contradiction
  have hc_le := hbound ε hε_pos hε_lt_1
  -- From hε_bound: ε * (1 + c) < c - a, we get (a + ε) / (1 - ε) < c
  have hcontra : (a + ε) / (1 - ε) < c := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 - ε)]
    ring_nf
    linarith only [hε_bound]
  linarith only [hc_le, hcontra]

omit [Fintype O] [DecidableEq C] in
private lemma coverOpt_eq_zero_of_empty_row (inc : O → Finset C) {o : O}
    (ho : inc o = ∅) : coverOpt inc = 0 := by
  unfold coverOpt
  have h_empty : {x | ∃ y, IsCover inc y ∧ x = ∑ c, y c} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨y, hy, _⟩
    have := hy.2 o
    rw [ho] at this
    simp at this
    linarith only [this]
  rw [h_empty]
  simp

/-- **THE ATOM — finite LP strong duality (packing = cover).** Machinery-free: pure finite LP.
This is the only genuinely hard step; everything downstream is instantiation. -/
theorem lp_strong_duality (inc : O → Finset C) :
    coverOpt inc ≤ packOpt inc := by
  by_cases hempty : ∃ o, inc o = ∅
  · obtain ⟨o, ho⟩ := hempty
    have hzero : coverOpt inc = 0 := @coverOpt_eq_zero_of_empty_row O C _ inc o ho
    rw [hzero]
    apply Real.sSup_nonneg
    rintro x ⟨w, hw, rfl⟩
    exact Finset.sum_nonneg fun o _ => hw.1 o
  · have hinc : ∀ o, (inc o).Nonempty := fun o => by simp_all [Finset.nonempty_iff_ne_empty]
    by_contra h
    push Not at h
    -- h : packOpt inc < coverOpt inc
    set a := (packOpt inc + coverOpt inc) / 2 with ha_def
    have ha : packOpt inc < a := by linarith only [h, ha_def]
    have hcover := @coverOpt_le_of_packOpt_lt O C _ _ _ inc hinc a ha
    linarith only [ha_def, ha, hcover]

/-- Every feasible packing value is at most every feasible cover value. -/
theorem weak_duality (inc : O → Finset C) {w : O → ℝ} {y : C → ℝ}
    (hw : IsPacking inc w) (hy : IsCover inc y) :
    ∑ o, w o ≤ ∑ c, y c := by
  classical
  calc
    ∑ o, w o ≤ ∑ o, w o * ∑ c ∈ inc o, y c := by
      refine Finset.sum_le_sum fun o _ => ?_
      calc w o = w o * 1 := by ring
        _ ≤ w o * ∑ c ∈ inc o, y c :=
          mul_le_mul_of_nonneg_left (hy.2 o) (hw.1 o)
    _ = ∑ o : O, ∑ c : C, if c ∈ inc o then w o * y c else 0 := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      simp
    _ = ∑ c : C, ∑ o : O, if c ∈ inc o then w o * y c else 0 := Finset.sum_comm
    _ = ∑ c, (∑ o ∈ Finset.univ.filter (fun o => c ∈ inc o), w o) * y c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ ∑ c, 1 * y c := by
      refine Finset.sum_le_sum fun c _ => ?_
      exact mul_le_mul_of_nonneg_right (hw.2 c) (hy.1 c)
    _ = ∑ c, y c := by simp

/-- Finite packing/cover weak duality at the optimum, when every object meets a constraint. -/
theorem packOpt_le_coverOpt (inc : O → Finset C) (hinc : ∀ o, (inc o).Nonempty) :
    packOpt inc ≤ coverOpt inc := by
  classical
  have hcover : {x : ℝ | ∃ y, IsCover inc y ∧ x = ∑ c, y c}.Nonempty := by
    refine ⟨Fintype.card C, (fun _ => 1), ?_, ?_⟩
    · constructor
      · intro c; norm_num
      · intro o
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_pos.mpr (hinc o)
    · simp
  unfold packOpt coverOpt
  refine csSup_le (packValues_nonempty inc) ?_
  rintro x ⟨w, hw, rfl⟩
  refine le_csInf hcover ?_
  rintro yval ⟨y, hy, rfl⟩
  exact weak_duality inc hw hy

end LPDuality

end



/-! # Strong duality for triangle packing and covering -/

public section

open Finset SimpleGraph Nibble.YusterE LPDuality

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Object type: the triangles of `G`. -/
abbrev Tri := {t : Finset V // t ∈ G.cliqueFinset 3}
/-- Constraint type: the edges of `G`. -/
abbrev Edg := {e : Sym2 V // e ∈ G.edgeFinset}

/-- Incidence: the edges contained in a triangle. -/
noncomputable def triInc (t : Tri G) : Finset (Edg G) :=
  Finset.univ.filter (fun e : Edg G => e.val ∈ edgesIn G t.val)

/-- Every triangle has an incident graph edge. -/
theorem triInc_nonempty (t : Tri G) : (triInc G t).Nonempty := by
  classical
  have ht := SimpleGraph.mem_cliqueFinset_iff.mp t.property
  obtain ⟨hc, hcard⟩ := ht
  obtain ⟨v, hv⟩ : t.val.Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; decide)
  have hc_erase : #(t.val.erase v) = 2 := by
    rw [Finset.card_erase_of_mem hv, hcard]
  obtain ⟨w, hw⟩ : (t.val.erase v).Nonempty :=
    Finset.card_pos.mp (by rw [hc_erase]; decide)
  have hvw : w ≠ v := (Finset.mem_erase.mp hw).1
  have hadj : G.Adj w v := hc (Finset.mem_of_mem_erase hw) hv hvw
  let e : Sym2 V := s(w, v)
  have heG : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact hadj
  have heIn : e ∈ edgesIn G t.val := by
    rw [edgesIn, Finset.mem_filter]
    refine ⟨heG, ?_⟩
    intro x hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_of_mem_erase hw
    · exact hv
  refine ⟨⟨e, heG⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heIn⟩

/-- **Bridge 1 (cover side).** The abstract cover optimum over the triangle–edge incidence equals
`τ₃*`. -/
theorem coverOpt_triInc_eq_tau3Star : coverOpt (triInc G) = tau3Star G := by
  -- Helper: edgesIn is nonempty for any triangle
  have edgesIn_ne : ∀ (t : Finset V), G.IsNClique 3 t → (edgesIn G t).Nonempty := fun t ht => by
    have ht' : t ∈ G.cliqueFinset 3 := by rwa [SimpleGraph.mem_cliqueFinset_iff]
    rw [edgesIn]
    -- The clique has 3 vertices
    have hCLIQUEN := SimpleGraph.mem_cliqueFinset_iff.mp ht'
    obtain ⟨hc, hcard⟩ := hCLIQUEN
    -- Get two distinct vertices from the clique
    have hne : t.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
    obtain ⟨v, hv⟩ := hne
    -- There exists another vertex (since card = 3 > 1)
    have hc_erase : #(t.erase v) = 2 := by rw [Finset.card_erase_of_mem hv, hcard]
    have hne2 : (t.erase v).Nonempty := Finset.card_pos.mp (by rw [hc_erase]; decide)
    obtain ⟨w, hw⟩ := hne2
    -- v and w are distinct and both in t
    have hvw : w ≠ v := by
      rw [Finset.mem_erase] at hw
      exact hw.1
    -- Since t is a clique, w and v are adjacent
    have hadj : G.Adj w v := hc (Finset.mem_of_mem_erase hw) hv hvw
    -- The edge {w, v} is in edgesIn G t
    let e : Sym2 V := s(w, v)
    have hmem : e ∈ {e ∈ G.edgeFinset | ∀ v ∈ e, v ∈ t} := by
      simp only [Finset.mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset]
        exact hadj
      · intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> [exact Finset.mem_of_mem_erase hw; exact hv]
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.ne_empty_of_mem hmem)
  apply le_antisymm
  · -- coverOpt ≤ tau3Star
    apply csInf_le_csInf
    · -- coverOpt set is bounded below
      refine ⟨0, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.sum_nonneg fun _ _ => hy.1 _
    · -- τ ∈ tau3Star set (to show nonempty)
      use ∑ _e ∈ G.edgeFinset, (1 : ℝ)
      use fun _ => (1 : ℝ)
      constructor
      · constructor
        · intro _; norm_num
        · intro t ht
          have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
          have hne : (edgesIn G t).Nonempty := by exact edgesIn_ne t ht'
          have : (1 : ℝ) ≤ ∑ _e ∈ edgesIn G t, (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp only [mul_one]
            exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hne)
          exact this
      · rfl
    · -- subset: tau3Star set ⊆ coverOpt set
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      use (fun (c : Edg G) => y c)
      constructor
      · constructor
        · intro ⟨e, _⟩; exact hy.1 e
        · intro ⟨t, ht⟩
          have h := hy.2 t ht
          have eq_sums :
              (@Finset.sum (Edg G) ℝ _ (@triInc V _ _ G _ ⟨t, ht⟩)
                (fun c : Edg G => y (c : Sym2 V))) = ∑ e ∈ edgesIn G t, y e := by
            rw [triInc]
            refine Finset.sum_bij (fun e _ => e.val) ?_ ?_ ?_ ?_
            · intro e he
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
              exact he
            · intro e₁ _ e₂ _ h; exact Subtype.ext h
            · intro e he
              have he' : e ∈ G.edgeFinset := Finset.filter_subset _ _ he
              use ⟨e, he'⟩
              simp [he]
            · intro b _; rfl
          rw [eq_sums]
          exact h
      · refine Finset.sum_bij (fun e (he : e ∈ G.edgeFinset) => ⟨e, he⟩) ?_ ?_ ?_ ?_
        · intro e _; exact Finset.mem_univ _
        · intro e₁ _ e₂ _ h; exact congrArg Subtype.val h
        · intro c _; use c.val; simp
        · intro e _; rfl
  · -- tau3Star ≤ coverOpt
    apply csInf_le_csInf
    · -- coverOpt set is bounded below
      refine ⟨0, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.sum_nonneg fun _ _ => hy.1 _
    · -- tau3Star set is nonempty
      refine ⟨∑ _e ∈ G.edgeFinset, (1 : ℝ), ?_⟩
      use fun _ => (1 : ℝ)
      constructor
      · refine ⟨fun _ => by norm_num, ?_⟩
        intro ⟨t, ht⟩
        have hne : (edgesIn G t).Nonempty := by
          exact edgesIn_ne t (SimpleGraph.mem_cliqueFinset_iff.mp ht)
        have hcard : #(triInc G ⟨t, ht⟩) = #(edgesIn G t) := by
          rw [triInc]
          refine Finset.card_bij (fun e _ => e.val) ?_ ?_ ?_
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
            exact he
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro e he
            simp only [edgesIn, Finset.mem_filter] at he
            have he' : e ∈ edgesIn G t := Finset.mem_filter.mpr ⟨he.1, he.2⟩
            use ⟨e, he.1⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp [he']
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
        exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hne)
      · symm
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_univ, Fintype.card_coe]
        simp
    · -- subset: coverOpt set ⊆ tau3Star set
      intro x hx
      -- x ∈ {x | ∃ y : Edg G → ℝ, IsCover (triInc G) y ∧ x = ∑ c, y c}
      obtain ⟨y, hy, rfl⟩ := hx
      -- y : Edg G → ℝ
      -- Extend y to Sym2 V by setting non-edges to 0
      let y' : Sym2 V → ℝ := fun e => if h : e ∈ G.edgeFinset then y ⟨e, h⟩ else 0
      use y'
      refine ⟨?_, ?_⟩
      · -- IsFracCover G y'
        constructor
        · intro e; simp only [y']; split_ifs with h <;> [exact hy.1 ⟨e, h⟩; norm_num]
        · intro t ht
          have h := hy.2 ⟨t, ht⟩
          have eq_sums : (@Finset.sum (Edg G) ℝ _ (@triInc V _ _ G _ ⟨t, ht⟩) y) =
              ∑ e ∈ (edgesIn G t).attach,
                y ⟨e.val, Finset.filter_subset (fun e => ∀ v ∈ e, v ∈ t)
                  G.edgeFinset e.prop⟩ := by
            rw [triInc]
            have toMem : ∀ c : Edg G,
                c ∈ Finset.univ.filter (fun e : Edg G => e.val ∈ edgesIn G t) →
                  c.val ∈ edgesIn G t := by simp
            refine Finset.sum_bij (fun c _ => ⟨c.val, toMem c ‹_›⟩) ?_ ?_ ?_ ?_
            · intro c _; simp
            · intro c₁ _ c₂ _ h; simpa using h
            · intro e he
              use ⟨e.val, Finset.filter_subset _ _ e.prop⟩
              simp
            · intro c _; rfl
          rw [← Finset.sum_attach]
          simp only [y']
          have h2 : ∀ x ∈ (edgesIn G t).attach,
              (if h : x.val ∈ G.edgeFinset then y ⟨x.val, h⟩ else 0) =
                y ⟨x.val, Finset.filter_subset (fun e => ∀ v ∈ e, v ∈ t)
                  G.edgeFinset x.prop⟩ := by
            intro x hx
            have hx' : x.val ∈ edgesIn G t := x.2
            rw [dite_eq_left (Finset.filter_subset _ _ hx')]
          rw [Finset.sum_congr rfl h2]
          rw [eq_sums.symm]
          exact h
      · symm
        refine Finset.sum_bij (fun e he => ⟨e, he⟩) ?_ ?_ ?_ ?_
        · intro e he; simp
        · intro e₁ he₁ e₂ he₂ h; simpa using h
        · intro c _; use c.val; simp
        · intro e he; simp only [y', he, dite_eq_left]

private theorem edge_toFinset_card (e : Edg G) : #(Sym2.toFinset e.val) = 2 := by
  rw [Sym2.toFinset]
  have hn : (Sym2.toMultiset e.val).Nodup := by
    simp only [Sym2.toMultiset]
    have hmem := e.property
    generalize hv : e.val = x
    induction x using Sym2.ind with
    | h a b =>
      have hab : s(a, b) ∈ G.edgeFinset := by rwa [hv] at hmem
      have hne : a ≠ b := by
        intro heq
        rw [heq] at hab
        simp at hab
      simp [Sym2.lift, hne]
  rw [Multiset.toFinset_card_of_nodup hn, Sym2.card_toMultiset]

/-- **Bridge 2 (packing side).** The abstract packing optimum over the triangle–edge
incidence equals
`ν₃*`. -/
theorem packOpt_triInc_eq_nu3star : packOpt (triInc G) = nu3star G := by
  unfold packOpt nu3star
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hinj : ∀ t1 t2 : Tri G, t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
      intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
      simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
      exact Subtype.ext
        (powersetCard_two_inj (by rw [ht1.card_eq]; omega)
          (by rw [ht2.card_eq]; omega) h)
    let w' : Finset (Finset V) → ℝ := fun T => if hT : T ∈ triangleHypergraphE G then
      w ⟨(Classical.choose (Finset.mem_image.mp hT)),
        (Classical.choose_spec (Finset.mem_image.mp hT)).1⟩
      else (0 : ℝ)
    refine ⟨w', ⟨?nneg, ?zero, ?cap⟩, ?sum⟩
    case nneg =>
      intro T
      simp only [w']
      split_ifs with hT
      · exact hw.1 _
      · exact le_refl 0
    case zero =>
      intro T hT
      simp [w', hT]
    case cap =>
      intro e
      by_cases he : e.card = 2
      · -- e is a 2-element finset, corresponding to an edge of G (as Sym2 V)
        -- Check if e corresponds to an edge of G
        -- Define: e is an edge iff there exists Sym2 edge with toFinset = e
        let isEdge : Finset V → Prop := fun f => ∃ e' ∈ G.edgeFinset, Sym2.toFinset e' = f
        by_cases he' : isEdge e
        · -- e corresponds to an edge; use packing constraint
          obtain ⟨e', he'_edge, he'_eq⟩ := he'
          -- e' is in G.edgeFinset, and Sym2.toFinset e' = e
          -- Construct the Edg G element
          let ec : Edg G := ⟨e', he'_edge⟩
          -- The constraint says: ∑ t ∈ {t | ec ∈ triInc t}, w t ≤ 1
          have hcon := hw.2 ec
          -- We need to show: ∑ T ∈ triangleHypergraphE G with e ∈ T, w' T ≤ 1
          -- These are the same set of triangles
          -- Rewrite "with" to filter form
          rw [Finset.sum_filter]
          rw [Finset.sum_filter] at hcon
          -- The two sums are equal: triangles containing e = triangles containing ec
          -- First, rewrite the sum over triangleHypergraphE G as a sum over Tri G
          have heq_sum : ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w' T else (0 : ℝ)) =
                         ∑ t : Tri G, (if e ∈ t.val.powersetCard 2 then w t else (0 : ℝ)) := by
            rw [triangleHypergraphE]
            rw [Finset.sum_image (fun x hx y hy hxy => by
              have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
              simpa using this)]
            rw [Finset.sum_subtype]
            · refine Finset.sum_congr rfl (fun t _ => ?_)
              have hT : t.val.powersetCard 2 ∈ triangleHypergraphE G := by
                rw [triangleHypergraphE, Finset.mem_image]
                exact ⟨t.val, t.prop, rfl⟩
              -- The choose gives the original triangle by injectivity
              have hcs := Classical.choose_spec (Finset.mem_image.mp hT)
              have hchoose : Classical.choose (Finset.mem_image.mp hT) = t.val :=
                Subtype.ext_iff.mp
                  (hinj ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩ t hcs.2)
              have hw_eq : w ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩ = w t := by
                congr 1
                exact Subtype.ext hchoose
              simp only [w', hT, hchoose]
              simp
            all_goals simp
          rw [heq_sum]
          -- Now show this equals the constraint sum
          have heq_sum2 : ∑ t : Tri G, (if e ∈ t.val.powersetCard 2 then w t else 0) =
                          ∑ t : Tri G, (if ec ∈ triInc G t then w t else 0) := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            simp only [triInc]
            -- Need: e ∈ t.val.powersetCard 2 ↔ ec.val ∈ edgesIn G t.val
            -- ec.val = e' where e'.toFinset = e, and e' ∈ G.edgeFinset
            -- Since he : e.card = 2, we have e ∈ t.val.powersetCard 2 ↔ e ⊆ t.val
            -- And ec.val ∈ edgesIn G t.val ↔ ec.val.toFinset ⊆ t.val (by definition of edgesIn)
            -- Since ec.val.toFinset = e, these are equivalent
            simp [edgesIn, Finset.mem_powersetCard]
            have h_equiv : (e ⊆ t.val ∧ e.card = 2) ↔ ∀ v ∈ ec.val, v ∈ t.val := by
              constructor
              · intro ⟨hsub, _⟩ v hv
                have hve : v ∈ e := by
                  rw [← he'_eq]
                  exact Sym2.mem_toFinset.mpr hv
                exact hsub hve
              · intro h
                exact ⟨by
                  intro v hv
                  rw [← he'_eq] at hv
                  exact h v (Sym2.mem_toFinset.mp hv), he⟩
            simp [h_equiv]
          rw [heq_sum2]
          exact hcon
        · -- e does not correspond to an edge; sum is empty
          have hdisj : ∀ t ∈ G.cliqueFinset 3, e ∉ t.powersetCard 2 := by
            intro t ht h
            rw [Finset.mem_powersetCard] at h
            obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp he
            apply he'
            use s(a, b)
            simp only [mem_edgeFinset, mem_edgeSet, Sym2.toFinset, heq]
            -- Need to show (a, b) is an edge of G
            -- Since e ⊆ t and t is a clique, a and b are adjacent
            have hsub := h.1
            rw [heq] at hsub
            have ha : a ∈ t := hsub (Finset.mem_insert_self a {b})
            have hb : b ∈ t := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
            refine ⟨?adj, ?finset⟩
            · have htc : G.IsNClique 3 t := by simpa using ht
              exact htc.isClique ha hb hab
            · simp [Sym2.toMultiset]
          have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
            rw [triangleHypergraphE]
            rw [Finset.filter_eq_empty_iff]
            intro T hT
            rw [Finset.mem_image] at hT
            obtain ⟨t, ht, rfl⟩ := hT
            exact hdisj t ht
          rw [hempty, Finset.sum_empty]
          exact zero_le_one
      · have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro T hT
          rw [triangleHypergraphE, Finset.mem_image] at hT
          obtain ⟨t, ht, rfl⟩ := hT
          simp only [SimpleGraph.mem_cliqueFinset_iff] at ht
          rw [Finset.mem_powersetCard]
          exact fun h => he h.2
        simp [hempty]
    case sum =>
      -- Need: ∑ t : Tri G, w t = ∑ T ∈ triangleHypergraphE G, w' T
      -- triangleHypergraphE G = (G.cliqueFinset 3).image (fun t => t.powersetCard 2)
      -- w' T = w ⟨choose(T), ...⟩ if T ∈ triangleHypergraphE G, else 0
      -- Since choose(T) is the unique t with t.powersetCard 2 = T, we get the equality
      rw [triangleHypergraphE]
      rw [Finset.sum_image (fun x hx y hy hxy => by
        have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simpa using this)]
      -- Now: ∑ t : Tri G, w t = ∑ x ∈ G.cliqueFinset 3, w' (x.powersetCard 2)
      -- Both sides are sums over the same index set
      -- Convert LHS to sum over G.cliqueFinset 3
      rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]
      refine Finset.sum_congr rfl ?_
      intro t ht
      -- Goal: w ⟨t.val, t.prop⟩ = w' (t.val.powersetCard 2)
      have hT : t.val.powersetCard 2 ∈ triangleHypergraphE G := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t.val, t.prop, rfl⟩
      change w ⟨t.val, t.prop⟩ = w' (t.val.powersetCard 2)
      change w ⟨t.val, t.prop⟩ = (if hT : t.val.powersetCard 2 ∈ triangleHypergraphE G then
        w ⟨(Classical.choose (Finset.mem_image.mp hT)),
          (Classical.choose_spec (Finset.mem_image.mp hT)).1⟩
        else (0 : ℝ))
      have hcs := Classical.choose_spec (Finset.mem_image.mp hT)
      have hchoose : Classical.choose (Finset.mem_image.mp hT) = t.val :=
        Subtype.ext_iff.mp
          (hinj ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩
            ⟨t.val, t.prop⟩ hcs.2)
      split_ifs
      · congr 1; exact Subtype.ext hchoose.symm
  · rintro ⟨w, hw, rfl⟩
    -- w is a fractional packing on the triangle hypergraph
    -- Define packing on triangles: w' t = w (t.val.powersetCard 2)
    let w' : Tri G → ℝ := fun t => w (t.val.powersetCard 2)
    use w'
    refine ⟨?hw', ?rfl⟩
    · constructor
      · intro t; exact hw.1 _
      · intro e
        -- Sum over triangles containing e equals sum over T ∈ triangleHypergraphE G with e ∈ T
        have he : #(Sym2.toFinset e.val) = 2 := edge_toFinset_card G e
        -- The sum ∑ t with e ∈ triInc t of w' t equals ∑ T ∈ filter (e.val ∈ ·) of w T
        have heq : ∑ o with e ∈ triInc G o, w' o =
                   ∑ T ∈ (triangleHypergraphE G).filter (fun T => e.val.toFinset ∈ T), w T := by
          simp only [Finset.sum_filter]
          rw [show (∑ o : Tri G, if e ∈ triInc G o then w' o else 0) =
              ∑ o ∈ Finset.univ, if e ∈ triInc G o then w' o else 0 from rfl]
          rw [triangleHypergraphE]
          rw [Finset.sum_image (fun x hx y hy hxy => by
            have hinj : ∀ t1 t2 : Tri G,
                t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
              intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
              simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
              exact Subtype.ext
                (powersetCard_two_inj (by rw [ht1.card_eq]; omega)
                  (by rw [ht2.card_eq]; omega) h)
            have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
            simpa using this)]
          rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]
          refine Finset.sum_congr rfl (fun t ht => ?_)
          by_cases h : e.val.toFinset ∈ t.val.powersetCard 2
          · -- pos: e.val.toFinset ∈ t.val.powersetCard 2, so e ∈ triInc t
            have hmem : e ∈ triInc G t := by
              simp only [triInc, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [edgesIn]
              rw [Finset.mem_powersetCard] at h
              exact Finset.mem_filter.mpr ⟨e.property, by simpa [Finset.subset_iff] using h.1⟩
            simp only [hmem, ↓reduceIte, h]
            rfl
          · -- neg: e.val.toFinset ∉ t.val.powersetCard 2, so e ∉ triInc t
            have hni : e ∉ triInc G t := by
              simp only [triInc, Finset.mem_filter, Finset.mem_univ, true_and]
              intro hc
              apply h
              rw [edgesIn] at hc
              have ⟨_, hsub⟩ := Finset.mem_filter.mp hc
              rw [Finset.mem_powersetCard]
              exact ⟨by simpa [Finset.subset_iff] using hsub, he⟩
            simp only [hni, ↓reduceIte, h]
        rw [heq]
        exact hw.2.2 e.val.toFinset
    · rw [triangleHypergraphE]
      rw [Finset.sum_image (fun x hx y hy hxy => by
        have hinj : ∀ t1 t2 : Tri G, t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
          intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
          simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
          exact Subtype.ext
            (powersetCard_two_inj (by rw [ht1.card_eq]; omega)
              (by rw [ht2.card_eq]; omega) h)
        have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simpa using this)]
      rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]

/-- **`StrongDualityHyp` — the instantiation.** `τ₃* ≤ ν₃*` follows from the abstract
finite LP strong
duality applied to the triangle–edge incidence, via the two value bridges. -/
theorem tau3Star_le_nu3star : tau3Star G ≤ nu3star G := by
  rw [← coverOpt_triInc_eq_tau3Star G, ← packOpt_triInc_eq_nu3star G]
  exact lp_strong_duality (triInc G)

/-- **`StrongDualityHyp` DISCHARGED** — the cover-side strong-duality obligation of
the AX1 chain is now a theorem (via the abstract finite LP duality + the
triangle–edge encoding bridges). One of the three AX1
obligations is closed, independently of the nibble. -/
theorem strongDualityHyp_holds : StrongDualityHyp :=
  fun {_} _ _ G _ => tau3Star_le_nu3star G

/-- Weak duality in the reverse direction for the triangle–edge incidence. -/
theorem nu3star_le_tau3Star : nu3star G ≤ tau3Star G := by
  rw [← packOpt_triInc_eq_nu3star G, ← coverOpt_triInc_eq_tau3Star G]
  exact packOpt_le_coverOpt (triInc G) (triInc_nonempty G)

/-- The cover-side AX1 statement yields the unconditional packing-gap formulation. -/
theorem nibbleGapHyp_of_ax1 (hAX1 : AX1Statement) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := hAX1 ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn
  have hcover := hmain V G hn
  have hweak := nu3star_le_tau3Star G
  linarith

/-- The remaining AX1 obligation is precisely the unconditional packing gap. -/
theorem ax1_of_nibbleGap (hgap : NibbleGapHyp) : AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap strongDualityHyp_holds hgap

end Nibble.AX1

end







/-! # YusterGap -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y6 capstone — integrality gap bound.** Assuming `NibbleTheorem` and the Y3 near-regularity /
codegree interface on `triangleHypergraphSub G`, the gap between the fractional and integral
triangle
packing numbers is at most `β·|E(G)|/3`. Combining `nu3_ge_nibble` and `nu3star_le`. As `β → 0` this
is `o(n²)` — AX1. -/
theorem nu3star_sub_nu3_le (hNibble : NibbleTheorem) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ β * ((G.cliqueFinset 2).card : ℝ) / 3 := by
  obtain ⟨μ, hμ, d₀, hd₀, hlb⟩ := nu3_ge_nibble G hNibble hβ
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have h1 := hlb hd hd0 hReg hCod
  have h2 := nu3star_le G
  have hring : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3)
      = ((G.cliqueFinset 2).card : ℝ) / 3 - β * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  rw [hring] at h1
  have hgoal : β * ((G.cliqueFinset 2).card : ℝ) / 3 = β * (((G.cliqueFinset 2).card : ℝ) / 3) := by
    ring
  rw [hgoal]
  linarith only [h1, h2]

end Nibble.YusterE

end


/-! # YusterAX1 -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Edge count bound** `|E(G)| ≤ |V(G)|²`. Each edge is a `2`-subset of the vertex set, so
`|E| ≤ C(|V|,2) ≤ |V|²`. -/
theorem edge_card_le_card_sq :
    ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hle : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
    have hsub : (G.cliqueFinset 2).card ≤
        (Finset.univ.powersetCard 2 : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      rw [SimpleGraph.mem_cliqueFinset_iff] at he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, he.card_eq⟩
    rwa [Finset.card_powersetCard, Finset.card_univ] at hsub
  have hchoose : (Fintype.card V).choose 2 ≤ (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul (le_refl _) (Nat.sub_le _ _))
  calc ((G.cliqueFinset 2).card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by exact_mod_cast hle
    _ ≤ ((Fintype.card V) ^ 2 : ℝ) := by exact_mod_cast hchoose
    _ = (Fintype.card V : ℝ) ^ 2 := by ring

/-- **AX1-form gap.** Assuming `NibbleTheorem` and the edge-based Y3 interface, the
integrality gap is
`≤ ε·|V(G)|²` — the shape AX1 states. Takes `β = 3ε` in `nu3star_sub_nu3_le` (so `β·|E|/3 =
ε·|E|`) and
bounds `|E| ≤ |V|²`. -/
theorem nu3star_sub_nu3_le_eps (hNibble : NibbleTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nu3star_sub_nu3_le G hNibble (by linarith : (0:ℝ) < 3 * ε)
  refine ⟨μ, hμ, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have hgap := hmain hd hd0 hReg hCod
  have hEq : (3 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 = ε * ((G.cliqueFinset 2).card : ℝ) := by
    ring
  rw [hEq] at hgap
  calc nu3star G - (nu3 G : ℝ)
      ≤ ε * ((G.cliqueFinset 2).card : ℝ) := hgap
    _ ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (edge_card_le_card_sq G) (le_of_lt hε)

end Nibble.YusterE

end


/-! # YusterMost -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Majority `ν₃` lower bound.** `NibbleTheoremMost` + the Y3-majority interface ⇒ `ν₃ ≥
(1-β)|E|/3`. -/
theorem nu3_ge_nibble_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibble_gives_triangleSub_matching_most G hNibble hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hmain hd hd0 hReg hCod
  exact le_trans hcard (by exact_mod_cast sub_matching_card_le_nu3 G hM)

/-- **Majority integrality-gap bound** `ν₃* − ν₃ ≤ β|E|/3`. -/
theorem nu3star_sub_nu3_le_most (hNibble : NibbleTheoremMost) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ β * ((G.cliqueFinset 2).card : ℝ) / 3 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hlb⟩ := nu3_ge_nibble_most G hNibble hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have h1 := hlb hd hd0 hReg hCod
  have h2 := nu3star_le G
  have hring : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3)
      = ((G.cliqueFinset 2).card : ℝ) / 3 - β * (((G.cliqueFinset 2).card : ℝ) / 3) := by ring
  rw [hring] at h1
  have hgoal : β * ((G.cliqueFinset 2).card : ℝ) / 3 = β * (((G.cliqueFinset 2).card : ℝ) / 3) := by
    ring
  rw [hgoal]
  linarith only [h1, h2]

/-- **Majority AX1-form gap** `ν₃* − ν₃ ≤ ε|V|²`. -/
theorem nu3star_sub_nu3_le_eps_most (hNibble : NibbleTheoremMost) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nu3star_sub_nu3_le_most G hNibble (by linarith : (0:ℝ) < 3 * ε)
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hReg hCod => ?_⟩
  have hgap := hmain hd hd0 hReg hCod
  have hEq : (3 * ε) * ((G.cliqueFinset 2).card : ℝ) / 3 = ε * ((G.cliqueFinset 2).card : ℝ) := by
    ring
  rw [hEq] at hgap
  calc nu3star G - (nu3 G : ℝ)
      ≤ ε * ((G.cliqueFinset 2).card : ℝ) := hgap
    _ ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (edge_card_le_card_sq G) (le_of_lt hε)

end Nibble.YusterE

end


/-! # NibbleGapReduction -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **Uniform nibble gap**: tolerances `μ, η` depending only on `ε` (NOT on `G`) such that
every graph that is near-`d`-regular (outside `η`-fraction) with bounded codegree has
`ν₃* − ν₃ ≤ ε n²`. This is the
`G`-uniform form of the proven per-graph `nu3star_sub_nu3_le_eps_most`. -/
def UniformNibbleGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] {d : ℝ}, 0 < d →
      NearlyRegularMost (triangleHypergraphSub G) d μ η →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **Near-regularity obligation** (the second-stage core): for tolerances `μ, η`, every
sufficiently large graph admits a near-regularity witness `d` with the free codegree bound.
This is exactly what a Szemerédi/Haxell–Rödl regularization must supply. -/
def NearRegObligation (μ η d₀ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      -- Second-stage global ceiling: every edge lies in ≤ (1+μ)d triangles, without an
      -- exceptional high-degree vertex. At δ≥(9/10+ε)|V| this is free; see
      -- `Nibble.YusterE.triangleSub_degree_window`.
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d)

/-- **Sized near-regularity obligation.** The corrected Freedman route also needs the triangle
hypergraph vertex count (`|E(G)|`) to be polynomially bounded by the regular degree scale `d`. -/
def NearRegObligationSized (μ η d₀ K : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card (EdgeV G) : ℝ) ≤ K * d ^ 2

/-- Dense-regime sized obligation in the natural graph-scale form: the base vertex count is linearly
controlled by the regular degree scale. -/
def NearRegObligationLinearSized (μ η d₀ L : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ d : ℝ, 0 < d ∧ d₀ ≤ d ∧ NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ e : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) e : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d

/-- The triangle-hypergraph vertex count is quadratically controlled by any linear base-size bound
`|V(G)| ≤ L d`. -/
theorem edgeV_card_le_sq_of_base_card_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {L d : ℝ}
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hbase : (Fintype.card V : ℝ) ≤ L * d) :
    (Fintype.card (EdgeV G) : ℝ) ≤ L ^ 2 * d ^ 2 := by
  have hE : (Fintype.card (EdgeV G) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [card_EdgeV]
    exact edge_card_le_card_sq G
  have hbase_sq : (Fintype.card V : ℝ) ^ 2 ≤ (L * d) ^ 2 := by
    have hn : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hLd : 0 ≤ L * d := mul_nonneg hL hd
    nlinarith only [hbase]
  calc (Fintype.card (EdgeV G) : ℝ)
      ≤ (Fintype.card V : ℝ) ^ 2 := hE
    _ ≤ (L * d) ^ 2 := hbase_sq
    _ = L ^ 2 * d ^ 2 := by ring

/-- A linear base-size second-stage obligation implies the polynomial hypergraph-size
obligation consumed by the sized nibble interface. -/
theorem nearRegSized_of_linearSized {μ η d₀ L : ℝ} (hL : 0 ≤ L)
    (h : NearRegObligationLinearSized μ η d₀ L) :
    NearRegObligationSized μ η d₀ (L ^ 2) := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil, hbase⟩ := hn₀ V G hV
  refine ⟨d, hd, hd0, hreg, hcod, hceil, ?_⟩
  exact edgeV_card_le_sq_of_base_card_le G hL (le_of_lt hd) hbase

/-- Linear size control for every positive constant implies the exact sized obligation for every
positive `K`, by taking `L = sqrt K`. -/
theorem nearRegSized_of_forall_linearSized {μ η d₀ K : ℝ} (hK : 0 < K)
    (h : ∀ L : ℝ, 0 < L → NearRegObligationLinearSized μ η d₀ L) :
    NearRegObligationSized μ η d₀ K := by
  have hsized := nearRegSized_of_linearSized (μ := μ) (η := η) (d₀ := d₀)
    (L := Real.sqrt K) (Real.sqrt_nonneg K) (h (Real.sqrt K) (Real.sqrt_pos.2 hK))
  simpa [Real.sq_sqrt hK.le] using hsized

/-- **NibbleGapHyp reduction.** The unconditional packing gap follows from the
`G`-uniform nibble gap plus the near-regularity obligation for its tolerances.
Bottoms the AX1 chain out at `NibbleTheoremMost`
(via `UniformNibbleGap`) and the second-stage regularization (via `NearRegObligation`). -/
theorem nibbleGap_of_uniform_and_regularity
    (hU : UniformNibbleGap)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    NibbleGapHyp := by
  intro ε hε
  obtain ⟨μ, hμ, η, hη, hgap⟩ := hU ε hε
  obtain ⟨n₀, hn₀⟩ := hReg μ η 1 hμ hη one_pos
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, _hd0, hreg, hcod, _hceil⟩ := hn₀ V G hV
  exact hgap G hd hreg hcod

/-- **NibbleGapHyp directly from `NibbleTheoremMost`.** Extracts the uniform tolerances
`μ, η` from the nibble interface once (at `r = 3`, `β = 3ε`), consumes the
near-regularity obligation, and inlines the
packing-gap arithmetic (`ν₃* ≤ |E|/3` and matching `≥ (1-3ε)|E|/3 ≤ ν₃`, so `ν₃*−ν₃ ≤ ε|E| ≤ ε n²`).
This bottoms the AX1 dependency chain out at exactly `NibbleTheoremMost` plus
the `second-stage` regularization. -/
theorem nibbleGap_of_nibbleTheorem (hNib : NibbleTheoremMost)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ hμ hη hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, _hceil⟩ := hn₀ V G hV
  obtain ⟨M, _hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G _hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- **NibbleGapHyp from the corrected ceiling-aware nibble theorem.** This is the same accounting as
`nibbleGap_of_nibbleTheorem`, but it keeps the second-stage global-degree ceiling supplied by
`NearRegObligation` and passes it into the nibble interface. -/
theorem nibbleGap_of_nibbleTheoremCeil (hNib : NibbleTheoremMostCeil)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    NibbleGapHyp := by
  dsimp [NibbleTheoremMostCeil] at hNib
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ hμ hη hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil⟩ := hn₀ V G hV
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod hceil
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- **NibbleGapHyp from the sized corrected nibble theorem.** This is the target shape for the
Freedman parameter route: all probabilistic plumbing is abstract, while the triangle-specific
regularization supplies both the global ceiling and the size-vs-degree bound. -/
theorem nibbleGap_of_nibbleTheoremCeilSized (hNib : NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      NearRegObligationSized μ η d₀ K) :
    NibbleGapHyp := by
  dsimp [NibbleTheoremMostCeilSized] at hNib
  intro ε hε
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, K, hK, hmain⟩ := hNib 3 (by norm_num) (3 * ε) (by linarith)
  obtain ⟨n₀, hn₀⟩ := hReg μ η d₀ K hμ hη hd₀ hK
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨d, hd, hd0, hreg, hcod, hceil, hsize⟩ := hn₀ V G hV
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hreg hcod hceil hsize
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hlb : (1 - 3 * ε) * (E / 3) ≤ (nu3 G : ℝ) := le_trans hMcard h1
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hlb, hεE]

/-- Version of `nibbleGap_of_nibbleTheoremCeilSized` consuming the dense-regime linear size
obligation. -/
theorem nibbleGap_of_nibbleTheoremCeilSized_linear (hNib : NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      NearRegObligationLinearSized μ η d₀ L) :
    NibbleGapHyp :=
  nibbleGap_of_nibbleTheoremCeilSized hNib
    (fun μ η d₀ _K hμ hη hd₀ hK =>
      nearRegSized_of_forall_linearSized hK (fun L hL => hReg μ η d₀ L hμ hη hd₀ hL))

/-- **The full AX1 reduction.** AX1 sorry-free follows from the three irreducible obligations. -/
theorem ax1_of_nibbleTheorem_strongDuality_regularity
    (hNib : NibbleTheoremMost) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheorem hNib hReg)

/-- **The full AX1 reduction, ceiling-aware form.** This is the corrected target for the Freedman
route: the second-stage regularization supplies the global degree ceiling consumed by
`NibbleTheoremMostCeil`. -/
theorem ax1_of_nibbleTheoremCeil_strongDuality_regularity
    (hNib : NibbleTheoremMostCeil) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheoremCeil hNib hReg)

/-- **The full AX1 reduction, sized ceiling-aware form.** This is the version aligned with the
Freedman parameter atom after exposing the necessary size control. -/
theorem ax1_of_nibbleTheoremCeilSized_strongDuality_regularity
    (hNib : NibbleTheoremMostCeilSized) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      NearRegObligationSized μ η d₀ K) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual (nibbleGap_of_nibbleTheoremCeilSized hNib hReg)

/-- Sized Freedman AX1 reduction consuming the linear dense-regime regularity condition. -/
theorem ax1_of_nibbleTheoremCeilSized_strongDuality_linearRegularity
    (hNib : NibbleTheoremMostCeilSized) (hdual : StrongDualityHyp)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      NearRegObligationLinearSized μ η d₀ L) :
    AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap hdual
    (nibbleGap_of_nibbleTheoremCeilSized_linear hNib hReg)

end Nibble.AX1

end


/-! # TightNibble -/

public section

open LeanPool.AsymptoticTrianglePacking.Internal

open Finset Hypergraph

namespace Nibble

/-- **The one-round covering oracle from the sharp round.**  Running the tight-band schedule
`Nibble.TightParams r β` gives, for every majority near-regular input with a global degree ceiling
and low codegree, a `HasRoundOracle H (γ/(16r)) β`. -/
theorem roundOracleExistsCeil_holds : RoundOracleExistsCeil := by
  classical
  intro r hr β hβ
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1` is vacuous: more than a `β`-fraction can never be uncovered
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, le_rfl, ?_⟩
    intro V _ _ H d _ _ _ _ _ _
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro H' S _ hlt
    exfalso
    have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨Pm⟩ := exists_tightParams r hr hβ hβ1
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨D₀, hD₀, c₀, hc₀, hround⟩ :=
    sharpRoundHyp_of_two_gamma_le_eps r hr Pm.gam Pm.eps Pm.exc (β / 2) Pm.gam_pos Pm.gam_le
      Pm.eps_le Pm.two_gam_le_eps Pm.exc_pos Pm.exc_le (by linarith) (by linarith)
  -- the parameters of the interface
  obtain ⟨mu, hmudef⟩ : ∃ m : ℝ,
      m = min Pm.wid (min (c₀ * Pm.lomin) (min (1 / (2 * (D₀ + 1))) (1 / 2))) := ⟨_, rfl⟩
  have hD1 : (0 : ℝ) < 2 * (D₀ + 1) := by linarith
  have hmupos : 0 < mu := by
    rw [hmudef]
    exact lt_min Pm.wid_pos (lt_min (mul_pos hc₀ Pm.lomin_pos)
      (lt_min (div_pos one_pos hD1) (by norm_num)))
  have hmu_wid : mu ≤ Pm.wid := by rw [hmudef]; exact min_le_left _ _
  have hmu_c0 : mu ≤ c₀ * Pm.lomin := by
    rw [hmudef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmu_D : mu ≤ 1 / (2 * (D₀ + 1)) := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmu_half : mu ≤ 1 / 2 := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcpos : (0 : ℝ) < Pm.gam / (16 * r) := div_pos Pm.gam_pos (by linarith)
  have hcle : Pm.gam / (16 * r) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [Pm.gam_le]
  refine ⟨mu, hmupos, Pm.eta, Pm.eta_pos, max 1 (D₀ / Pm.lomin),
    lt_of_lt_of_le one_pos (le_max_left _ _), Pm.gam / (16 * r), hcpos, hcle, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_max_left _ _) hd0
  have hDlo : D₀ ≤ d * Pm.lomin := by
    have h := le_trans (le_max_right (1 : ℝ) (D₀ / Pm.lomin)) hd0
    rw [div_le_iff₀ Pm.lomin_pos] at h
    exact h
  have hcodsmall : mu * d ≤ c₀ * (d * Pm.lomin) := by
    linarith only [mul_le_mul_of_nonneg_right hmu_c0 (show (0 : ℝ) ≤ d by linarith only [hd1])]
  -- the vertex count is at least the round's degree threshold
  have hNbig : 0 < (Fintype.card V : ℝ) → D₀ ≤ (Fintype.card V : ℝ) := by
    intro hNpos
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    have hetahalf : Pm.eta ≤ β / 2 := le_trans Pm.sig_init (Pm.sig_le 0 (Nat.zero_le _))
    have hExcnn : (0 : ℝ) ≤ (Exc.card : ℝ) := Nat.cast_nonneg _
    have hExclt : (Exc.card : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Exc := by
      by_contra hcon
      push Not at hcon
      have : Exc = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [this, Finset.card_univ] at hExclt
      exact absurd hExclt (lt_irrefl _)
    have hdeg := (hExcdeg v hv).1
    have hcg := card_ge_of_codegree huni hr1 hcodeg v
    have hdegnn : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
    by_contra hcon
    push Not at hcon
    have hmu_D' : mu * (2 * (D₀ + 1)) ≤ 1 := by
      rw [le_div_iff₀ hD1] at hmu_D
      linarith
    have hstep1 : d / 2 ≤ (degree H v : ℝ) := by nlinarith
    have hr1R : (1 : ℝ) ≤ (r : ℝ) - 1 := by linarith
    have hstep2 : (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hr1R hdegnn]
    have hstep3 : d / 2 ≤ ((Fintype.card V : ℝ) - 1) * (mu * d) := by linarith
    have hstep4 : (1 : ℝ) / 2 ≤ ((Fintype.card V : ℝ) - 1) * mu := by
      have hmul : d * (1 / 2) ≤ d * (((Fintype.card V : ℝ) - 1) * mu) := by
        linarith only [hstep3]
      exact le_of_mul_le_mul_left hmul hd
    nlinarith only [hstep4, hmu_D', hcon, hmupos,
      mul_pos hmupos (show (0 : ℝ) < D₀ - (Fintype.card V : ℝ) by linarith)]
  refine hasRoundOracle_of_scheduled_invariant H hcpos.le hcle Pm.T Pm.decay
    (fun j H' S => (∀ e ∈ H', Disjoint e S) ∧
      ∃ (K : Finset (Finset V)) (E : Finset V), K ⊆ H' ∧ IsUniform K r ∧
        (∀ e ∈ K, Disjoint e S) ∧
        (∀ v : V, (degree K v : ℝ) ≤ d * Pm.hi j) ∧
        (∀ v : V, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ)) ∧
        (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ mu * d) ∧
        (E.card : ℝ) ≤ Pm.sig j * (Fintype.card V : ℝ))
    ?_ (fun j H' S hP => hP.1) ?_
  · -- initialisation
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    refine ⟨fun e _ => Finset.disjoint_empty_right e, H, Exc, Finset.Subset.refl _, huni,
      fun e _ => Finset.disjoint_empty_right e, ?_, ?_, hcodeg, ?_⟩
    · intro v
      have h1 : (1 : ℝ) + mu ≤ Pm.hi 0 := by linarith [Pm.init_hi]
      have := hceil v
      nlinarith
    · intro v _ hvE
      have h1 : Pm.lo 0 ≤ 1 - mu := by linarith [Pm.init_lo]
      have := (hExcdeg v hvE).1
      nlinarith
    · have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      exact le_trans hExc (mul_le_mul_of_nonneg_right Pm.sig_init hNnn)
  · -- one round of the schedule
    rintro j hj H' S ⟨hH'disj, K, E, hKH', huniK, hKdisj, hhi, hlo, hcodK, hE⟩ hlt
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨R', hR'K, hcov, K', E', hK'res, huniK', hK'disj, hhi', hlo', hcodK', hE'⟩ :=
      tight_round_step hr Pm hc₀.le hround hd (mul_nonneg hmupos.le hd.le) hDlo hcodsmall
        (hNbig hNpos) hj huniK hKdisj hhi hlo hcodK hE hlt
    refine ⟨R', Finset.Subset.trans hR'K hKH', ⟨?_, K', E', ?_, huniK', hK'disj, hhi', hlo',
      hcodK', hE'⟩, hcov⟩
    · intro e he
      rw [Finset.disjoint_union_right]
      exact ⟨hH'disj e (Hypergraph.residual_subset H' R' he),
        Hypergraph.residual_disjoint_covered he⟩
    · exact Finset.Subset.trans hK'res (Finset.filter_subset_filter _ hKH')

/-- **`NibbleTheoremMostCeil`, unconditionally.** -/
theorem nibbleTheoremMostCeil_holds : NibbleTheoremMostCeil :=
  nibbleTheoremMostCeil_of_adaptiveOracleCeil
    (adaptiveOracleExistsCeil_of_roundOracleCeil roundOracleExistsCeil_holds)

/-- **`NibbleTheoremMostCeilSized`, unconditionally.**  The size hypothesis
`|V| ≤ K d²` is not needed by the tight-band route, so it is simply discarded. -/
theorem nibbleTheoremMostCeilSized_holds : NibbleTheoremMostCeilSized := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  exact ⟨μ, hμ, η, hη, d₀, hd₀, 1, one_pos,
    fun H d hd hd0 huni hreg hcod hceil _ => hmain H d hd hd0 huni hreg hcod hceil⟩

/-- **`NibbleTheorem`, unconditionally.** -/
theorem nibbleTheorem_holds : NibbleTheorem :=
  nibbleTheoremMostCeil_holds.nibbleTheorem

/-- **The nibble gap hypothesis**, via `Nibble.NibbleGapReduction`. -/
theorem AX1.nibbleGap_holds
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      AX1.NearRegObligationSized μ η d₀ K) :
    AX1.NibbleGapHyp :=
  AX1.nibbleGap_of_nibbleTheoremCeilSized nibbleTheoremMostCeilSized_holds hReg

/-- **AX1**, from strong duality and the sized near-regularity obligation. -/
theorem AX1.ax1_holds (hdual : AX1.StrongDualityHyp)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      AX1.NearRegObligationSized μ η d₀ K) :
    AX1.AX1Statement :=
  AX1.ax1_of_nibbleTheoremCeilSized_strongDuality_regularity
    nibbleTheoremMostCeilSized_holds hdual hReg

/-! ### Legacy interfaces

The schedule now supplies the sharp round itself (`Nibble.sharpRoundHyp_of_two_gamma_le_eps`, whose
regime `2γ ≤ ε` is exactly the schedule's own `ε = 4((r−1)/r)γ`), so `Nibble.SharpRoundHyp` is no
longer an input.  The following wrappers keep the earlier `_of_sharpRound` interfaces available. -/

/-- **The one-round covering oracle from the sharp round.** -/
theorem roundOracleExistsCeil_of_sharpRound (_hSharp : SharpRoundHyp) : RoundOracleExistsCeil :=
  roundOracleExistsCeil_holds

/-- **`NibbleTheoremMostCeil` from the sharp round.** -/
theorem nibbleTheoremMostCeil_of_sharpRound (_hSharp : SharpRoundHyp) : NibbleTheoremMostCeil :=
  nibbleTheoremMostCeil_holds

/-- **`NibbleTheoremMostCeilSized` from the sharp round.** -/
theorem nibbleTheoremMostCeilSized_of_sharpRound (_hSharp : SharpRoundHyp) :
    NibbleTheoremMostCeilSized :=
  nibbleTheoremMostCeilSized_holds

/-- **`NibbleTheorem` from the sharp round.** -/
theorem nibbleTheorem_of_sharpRound (_hSharp : SharpRoundHyp) : NibbleTheorem :=
  nibbleTheorem_holds

/-- **The nibble gap hypothesis from the sharp round**, via `Nibble.NibbleGapReduction`. -/
theorem AX1.nibbleGap_of_sharpRound (_hSharp : SharpRoundHyp)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      AX1.NearRegObligationSized μ η d₀ K) :
    AX1.NibbleGapHyp :=
  AX1.nibbleGap_holds hReg

/-- **AX1 from the sharp round**, together with strong duality and the sized near-regularity
obligation. -/
theorem AX1.ax1_of_sharpRound (_hSharp : SharpRoundHyp) (hdual : AX1.StrongDualityHyp)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      AX1.NearRegObligationSized μ η d₀ K) :
    AX1.AX1Statement :=
  AX1.ax1_holds hdual hReg

end Nibble

end






/-! # YusterSubDegree -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`|triangleHypergraphSub| = #triangles`.** The powerset-subtype map is injective on 3-cliques
(distinct triangles have distinct edge-sets), so the image has the same cardinality. -/
theorem triangleHypergraphSub_card :
    (triangleHypergraphSub G).card = (G.cliqueFinset 3).card := by
  rw [triangleHypergraphSub, Finset.card_image_of_injOn]
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  have h1 : t.powersetCard 2 = t'.powersetCard 2 := by
    have e1 := Finset.subtype_map_of_mem (powersetCard_two_subset_cliqueFinset G ht)
    have e2 := Finset.subtype_map_of_mem (powersetCard_two_subset_cliqueFinset G ht')
    rw [← e1, ← e2]
    exact congrArg (Finset.map _) heq
  exact powersetCard_two_inj (by rw [ht.card_eq]; norm_num) (by rw [ht'.card_eq]; norm_num) h1

/-- **Degree-sum (handshake) for the edge-based triangle hypergraph.** As `triangleHypergraphSub G`
is `3`-uniform, `∑_{E} deg_E = 3·|triangleHypergraphSub| = 3·#triangles`. The average edge
triangle-degree is `3·#triangles / |E(G)|`. -/
theorem sum_degree_triangleHypergraphSub :
    ∑ E : EdgeV G, degree (triangleHypergraphSub G) E = 3 * (G.cliqueFinset 3).card := by
  rw [Hypergraph.sum_degree (triangleHypergraphSub G) (triangleHypergraphSub_uniform G),
    triangleHypergraphSub_card]

end Nibble.YusterE

end


/-! # YusterSubDegreeChar -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem mem_image_of_triangle {t : Finset V} (E : EdgeV G) :
    E ∈ (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) ↔ E.val ⊆ t := by
  rw [Finset.mem_subtype, Finset.mem_powersetCard]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq⟩

private theorem triple_injOn :
    Set.InjOn (fun t => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2))
      (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  apply Finset.eq_of_subset_of_card_le _ (by rw [ht.card_eq, ht'.card_eq])
  intro a ha
  obtain ⟨b, hbt, hba⟩ : ∃ b ∈ t, b ≠ a := by
    have hne : (t.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht.card_eq]; omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, Finset.mem_of_mem_erase hb, Finset.ne_of_mem_erase hb⟩
  have hsub : ({a, b} : Finset V) ⊆ t := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hbt
  have hedge : ({a, b} : Finset V) ∈ G.cliqueFinset 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨ht.isClique.subset hsub, Finset.card_pair (Ne.symm hba)⟩
  have hmem : (⟨{a, b}, hedge⟩ : EdgeV G) ∈ (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) :=
    (mem_image_of_triangle G _).mpr hsub
  have heq' : (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)
      = (t'.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) := heq
  rw [heq'] at hmem
  have := (mem_image_of_triangle G _).mp hmem
  exact this (by simp)

theorem triangleHypergraphSub_degree_eq (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).card := by
  have hset : (triangleHypergraphSub G).filter (fun T => E ∈ T)
      = ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).image
          (fun t => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) := by
    ext T
    simp only [Finset.mem_filter, triangleHypergraphSub, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hE⟩
      exact ⟨t, ⟨ht, (mem_image_of_triangle G E).mp hE⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hsub⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, (mem_image_of_triangle G E).mpr hsub⟩
  rw [Hypergraph.degree, hset, Finset.card_image_of_injOn]
  exact (triple_injOn G).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))

/-- The number of triangles containing edge `E` equals the number of common neighbours `c` of `E`'s
endpoints (those `c ∉ E.val` with `insert c E.val` a triangle). -/
theorem triangles_on_edge_eq_commonNbr (E : EdgeV G) :
    ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).card
      = (Finset.univ.filter (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card := by
  have hE2 : E.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  symm
  apply Finset.card_bij (fun c _ => insert c E.val)
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨hc.2, Finset.subset_insert _ _⟩
  · intro c hc c' hc' heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    have hcmem : c ∈ insert c' E.val := heq ▸ Finset.mem_insert_self c E.val
    rw [Finset.mem_insert] at hcmem
    rcases hcmem with h | h
    · exact h
    · exact absurd h hc.1
  · intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    obtain ⟨htri, hsub⟩ := ht
    obtain ⟨c, hct, hcnotE⟩ : ∃ c ∈ t, c ∉ E.val := by
      by_contra h
      push Not at h
      have hts : t ⊆ E.val := fun x hx => h x hx
      have hle := Finset.card_le_card hts
      rw [htri.card_eq, hE2] at hle
      omega
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hcnotE, ?_⟩
      have : insert c E.val = t := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hct hsub
        · rw [htri.card_eq, Finset.card_insert_of_notMem hcnotE, hE2]
      rw [this]; exact htri
    · apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hct hsub
      · rw [htri.card_eq, Finset.card_insert_of_notMem hcnotE, hE2]

/-- **Second-stage bridge, graph form.** The hypergraph-degree of edge `E` in
`triangleHypergraphSub G` equals the number of common neighbours of its endpoints. -/
theorem triangleHypergraphSub_degree_eq_commonNbr (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = (Finset.univ.filter (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card := by
  rw [triangleHypergraphSub_degree_eq, triangles_on_edge_eq_commonNbr]

/-- **Second-stage mean codegree.** Summing the per-edge codegree (common-neighbour count)
over all edges gives
`3·#triangles`, so the average edge codegree is `3·#triangles / |E(G)|` — the target `d` for the
second-stage near-regularity window. -/
theorem sum_commonNbr_eq_three_mul_triangles :
    ∑ E : EdgeV G, (Finset.univ.filter
        (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card
      = 3 * (G.cliqueFinset 3).card := by
  rw [← sum_degree_triangleHypergraphSub G]
  exact Finset.sum_congr rfl fun E _ => (triangleHypergraphSub_degree_eq_commonNbr G E).symm

end Nibble.YusterE

end



/-! # YusterSubRegular -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Codegree side (trivial).** The edge-based triangle hypergraph has hypergraph-codegree `≤
1`, so it
is `CodegreeBounded C` for any `C ≥ 1` — in particular `C = μd` once `μd ≥ 1`. -/
theorem triangleHypergraphSub_codegreeBounded {C : ℝ} (hC : 1 ≤ C) :
    CodegreeBounded (triangleHypergraphSub G) C := by
  intro E E' hEE'
  calc (codegree (triangleHypergraphSub G) E E' : ℝ)
      ≤ 1 := by exact_mod_cast triangleHypergraphSub_codegree_le_one G hEE'
    _ ≤ C := hC

/-- **Majority near-regularity (packaging).** Given a per-edge degree window on all but an
exceptional
set `Exc` of size `≤ η|E(G)|`, the edge-based triangle hypergraph is `NearlyRegularMost d μ η`. The
per-edge bounds and the exceptional count are supplied by the edge counting (edge-counting
substep). -/
theorem triangleHypergraphSub_nearlyRegularMost_of_bounds {d μ η : ℝ}
    (Exc : Finset (EdgeV G))
    (hExc : (Exc.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ))
    (hlo : ∀ E ∉ Exc, (1 - μ) * d ≤ (degree (triangleHypergraphSub G) E : ℝ))
    (hhi : ∀ E ∉ Exc, (degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η :=
  ⟨Exc, hExc, fun E hE => ⟨hlo E hE, hhi E hE⟩⟩

end Nibble.YusterE

end


/-! # DenseNearRegular -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangle-hypergraph degree of an edge `{u,v}` is the number of common neighbours. -/
theorem triangleSub_degree_eq_inter (E : EdgeV G) (u v : V) (huv : E.val = ({u, v} : Finset V)) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have hE2 := SimpleGraph.mem_cliqueFinset_iff.mp E.2
  rw [huv] at hE2
  have huv_ne : u ≠ v := by
    rintro rfl
    have := hE2.card_eq
    simp at this
  have huv_adj : G.Adj u v :=
    hE2.1 (by simp : u ∈ ({u, v} : Finset V)) (by simp : v ∈ ({u, v} : Finset V)) huv_ne
  rw [triangleHypergraphSub_degree_eq_commonNbr]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, huv]
  constructor
  · rintro ⟨_, htri⟩
    rw [show insert c ({u, v} : Finset V) = ({c, u, v} : Finset V) from rfl,
      SimpleGraph.is3Clique_triple_iff] at htri
    exact ⟨htri.1.symm, htri.2.1.symm⟩
  · rintro ⟨hu, hv⟩
    have hcu : c ≠ u := by rintro rfl; simp at hu
    have hcv : c ≠ v := by rintro rfl; simp at hv
    refine ⟨by simp [hcu, hcv], ?_⟩
    rw [show insert c ({u, v} : Finset V) = ({c, u, v} : Finset V) from rfl,
      SimpleGraph.is3Clique_triple_iff]
    exact ⟨hu.symm, hv.symm, huv_adj⟩

/-- Every edge is a pair. -/
private theorem edgeV_eq_pair (E : EdgeV G) : ∃ u v : V, E.val = ({u, v} : Finset V) := by
  have h2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp h2
  exact ⟨u, v, huv⟩

/-- **second-stage ceiling (global upper bound).** Every edge lies in at most `|V|` triangles. -/
theorem triangleSub_degree_le_card (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E ≤ Fintype.card V := by
  obtain ⟨u, v, huv⟩ := edgeV_eq_pair G E
  rw [triangleSub_degree_eq_inter G E u v huv]
  calc (G.neighborFinset u ∩ G.neighborFinset v).card
      ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- **Second-stage floor (from a global min-degree bound).** If every vertex of `G` has degree
`≥ D`, then every edge lies in at least `2D − |V|` triangles by inclusion–exclusion. -/
theorem triangleSub_degree_ge_of_minDeg (E : EdgeV G) {D : ℕ} (hD : ∀ x, D ≤ G.degree x) :
    2 * D - Fintype.card V ≤ Hypergraph.degree (triangleHypergraphSub G) E := by
  obtain ⟨u, v, huv⟩ := edgeV_eq_pair G E
  rw [triangleSub_degree_eq_inter G E u v huv]
  have hincl : G.degree u + G.degree v - Fintype.card V
      ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
    have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    have hle : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree v]
    omega
  have hDu := hD u
  have hDv := hD v
  omega

/-- **Second-stage global near-regularity window (packaged).** With a global min-degree `D`
satisfying `|V| ≤ 2D`
(dense regime), every edge's triangle-degree lies in the window `[(1−μ)d, (1+μ)d]` provided
the window
covers `[2D−|V|, |V|]`. This is the global (no exceptional set) near-regularity the corrected nibble
consumes; at `δ ≥ (9/10+ε)|V|`, taking `D = (9/10+ε)|V|`, `d = (9/10)|V|`, `μ = 1/9` satisfies the
hypotheses. -/
theorem triangleSub_degree_window (E : EdgeV G) (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ d : ℝ}
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
      (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
  have hfloor := triangleSub_degree_ge_of_minDeg G E hD
  have hceil := triangleSub_degree_le_card G E
  have hcast : ((2 * D - Fintype.card V : ℕ) : ℝ) = 2 * (D : ℝ) - (Fintype.card V : ℝ) := by
    rw [Nat.cast_sub h2D]; push_cast; ring
  have hfloor' : 2 * (D : ℝ) - (Fintype.card V : ℝ)
      ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    rw [← hcast]; exact_mod_cast hfloor
  refine ⟨le_trans hlo hfloor', ?_⟩
  calc (Hypergraph.degree (triangleHypergraphSub G) E : ℝ)
      ≤ (Fintype.card V : ℝ) := by exact_mod_cast hceil
    _ ≤ (1 + μ) * d := hhi

/-- Dense-regime package for the corrected nibble input. A global degree window on every graph edge,
the trivial edge-hypergraph codegree bound, and a linear base-size estimate assemble the exact local
data required by `NearRegObligationLinearSized`. -/
theorem triangleSub_linearSized_data_of_window {μ η d L : ℝ}
    (hη : 0 ≤ η) (hcodeg : 1 ≤ μ * d) (hbase : (Fintype.card V : ℝ) ≤ L * d)
    (hwindow : ∀ E : EdgeV G,
      (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d := by
  refine ⟨?_, triangleHypergraphSub_codegreeBounded G hcodeg, ?_, hbase⟩
  · exact triangleHypergraphSub_nearlyRegularMost_of_bounds G ∅
      (by
        rw [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hη (Nat.cast_nonneg _))
      (fun E _ => (hwindow E).1)
      (fun E _ => (hwindow E).2)
  · intro E
    exact (hwindow E).2

/-- Dense-regime package specialized to a minimum-degree floor `D`: the inclusion-exclusion window
`triangleSub_degree_window` feeds the local linear-sized corrected nibble data. -/
theorem triangleSub_linearSized_data_of_minDeg (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ η d L : ℝ}
    (hη : 0 ≤ η) (hcodeg : 1 ≤ μ * d) (hbase : (Fintype.card V : ℝ) ≤ L * d)
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d := by
  exact triangleSub_linearSized_data_of_window G hη hcodeg hbase
    (fun E => triangleSub_degree_window G E D hD h2D hlo hhi)

end Nibble.YusterE

end


/-! # Tight.DenseRegDischarge -/

public section

open Finset Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Dense near-regularity, concrete window.**  For a graph whose minimum degree `D` satisfies
`9n ≤ 10D` (i.e. `δ(G) ≥ (9/10)n`) and `n ≥ 5`, the triangle hypergraph is nearly `d`-regular with
`d = n`, `μ = 1/5`, EMPTY exceptional set, codegree `≤ μd`, global ceiling `≤ (1+μ)d`, and the
linear
size bound `n ≤ 1·d`.  This is exactly the local data of `NearRegObligationLinearSized` with
`μ = 1/5, η = 0, L = 1, d = n`. -/
theorem triangleSub_dense_data (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, D ≤ G.degree x) (hDense : 9 * Fintype.card V ≤ 10 * D)
    (hn5 : 5 ≤ Fintype.card V) :
    NearlyRegularMost (triangleHypergraphSub G) (Fintype.card V : ℝ) (1 / 5) 0 ∧
      CodegreeBounded (triangleHypergraphSub G) ((1 / 5) * (Fintype.card V : ℝ)) ∧
      (∀ E : EdgeV G,
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + 1 / 5) * (Fintype.card V : ℝ)) ∧
      (Fintype.card V : ℝ) ≤ 1 * (Fintype.card V : ℝ) := by
  have h5 : (5 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn5
  have hDR : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (D : ℝ) := by exact_mod_cast hDense
  have h2D : Fintype.card V ≤ 2 * D := by
    have : (Fintype.card V : ℝ) ≤ 2 * (D : ℝ) := by linarith
    exact_mod_cast this
  refine triangleSub_linearSized_data_of_minDeg G D hD h2D (le_refl 0) ?_ ?_ ?_ ?_
  · -- hcodeg : 1 ≤ μ d = n/5
    nlinarith
  · -- hbase : n ≤ L d = 1·n
    rw [one_mul]
  · -- hlo : (1-μ) d = (4/5) n ≤ 2D - n
    nlinarith
  · -- hhi : n ≤ (1+μ) d = (6/5) n
    nlinarith

end Nibble.YusterE

end


/-! # DenseGapAX1 -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- **Packing-gap accounting.**  A matching of the triangle hypergraph of size at least
`(1 − 3ε)|E(G)|/3` forces `ν₃* − ν₃ ≤ ε|V|²`, using `ν₃* ≤ |E|/3` and `|E| ≤ |V|²`. -/
theorem gap_le_of_sub_matching {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ} (hε : 0 < ε)
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hMcard : (1 - 3 * ε) * ((Fintype.card (EdgeV G) : ℝ) / 3) ≤ (M.card : ℝ)) :
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  set E : ℝ := ((G.cliqueFinset 2).card : ℝ) with hE
  have hcardE : (Fintype.card (EdgeV G) : ℝ) = E := by rw [hE]; exact_mod_cast card_EdgeV G
  rw [hcardE] at hMcard
  have h1 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have h2 : nu3star G ≤ E / 3 := nu3star_le G
  have h3 : E ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have hεE : ε * E ≤ ε * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hε.le
  nlinarith only [h2, hMcard, h1, hεE]

/-- **The dense branch, unconditionally.**  For every `ε > 0` there is a density threshold `θ < 1`
and a size threshold `n₀` such that every graph on at least `n₀` vertices with minimum degree at
least `θ|V|` satisfies `ν₃* − ν₃ ≤ ε|V|²`.

At minimum degree `θ|V| = (1 − μ/2)|V|` the common neighbourhood of every edge has size in
`[(1−μ)|V|, |V|]`, so the triangle hypergraph is near-`|V|`-regular with an *empty* exceptional set,
bounded codegree and the global degree ceiling — precisely the hypotheses of the unconditional
nibble theorem `Nibble.nibbleTheoremMostCeil_holds`. -/
theorem nibbleGap_dense (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  have hmpos : 0 < min μ 1 := lt_min hμ one_pos
  have hm1 : min μ 1 ≤ 1 := min_le_right _ _
  have hmμ : min μ 1 ≤ μ := min_le_left _ _
  refine ⟨1 - min μ 1 / 2, by linarith, by linarith,
    ⌈max d₀ (max (1 / μ) 1)⌉₊, ?_⟩
  intro V _ _ G _ hV hdeg
  have hnR : max d₀ (max (1 / μ) 1) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hd0 : d₀ ≤ (Fintype.card V : ℝ) := le_trans (le_max_left _ _) hnR
  have hinv : 1 / μ ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnR
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnR
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := lt_of_lt_of_le one_pos hn1
  -- the integer minimum-degree floor
  set D : ℕ := ⌈(1 - min μ 1 / 2) * (Fintype.card V : ℝ)⌉₊ with hDdef
  have hD : ∀ x, D ≤ G.degree x := fun x => Nat.ceil_le.mpr (hdeg x)
  have hDR : (1 - min μ 1 / 2) * (Fintype.card V : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
  have h2DR : (Fintype.card V : ℝ) ≤ 2 * (D : ℝ) := by nlinarith
  have h2D : Fintype.card V ≤ 2 * D := by exact_mod_cast h2DR
  have hcodeg : (1 : ℝ) ≤ μ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hμ] at hinv
    linarith
  obtain ⟨hreg, hcod, hceil, -⟩ :=
    triangleSub_linearSized_data_of_minDeg (μ := μ) (η := η) (d := (Fintype.card V : ℝ)) (L := 1)
      G D hD h2D hη.le hcodeg (by rw [one_mul]) (by nlinarith) (by nlinarith)
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) (Fintype.card V : ℝ) hnpos hd0
      (triangleHypergraphSub_uniform G) hreg hcod hceil
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- Every fractional triangle packing has total weight at most the number of triangles: each single
weight is at most `1` by its own edge constraint. -/
theorem fracPacking_sum_le_card_triangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w : Finset (Finset V) → ℝ}
    (hw : IsFracPacking G w) :
    (∑ T ∈ triangleHypergraphE G, w T) ≤ ((G.cliqueFinset 3).card : ℝ) := by
  obtain ⟨hnn, -, hcon⟩ := hw
  have hone : ∀ T ∈ triangleHypergraphE G, w T ≤ 1 := by
    intro T hT
    have hcard : T.card = 3 := triangleHypergraphE_uniform G T hT
    obtain ⟨e, he⟩ : T.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
    refine le_trans (Finset.single_le_sum (f := w) (fun T' _ => hnn T') ?_) (hcon e)
    exact Finset.mem_filter.mpr ⟨hT, he⟩
  calc (∑ T ∈ triangleHypergraphE G, w T)
      ≤ ∑ _T ∈ triangleHypergraphE G, (1 : ℝ) := Finset.sum_le_sum hone
    _ = ((triangleHypergraphE G).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((G.cliqueFinset 3).card : ℝ) := by
        exact_mod_cast Finset.card_image_le (s := G.cliqueFinset 3)
          (f := fun t : Finset V => t.powersetCard 2)

/-- **`ν₃*` is at most the number of triangles.** -/
theorem nu3star_le_card_triangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G ≤ ((G.cliqueFinset 3).card : ℝ) := by
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  exact fracPacking_sum_le_card_triangles G hw

/-- **The triangle-poor branch, unconditionally.**  If `G` has at most `ε|V|²` triangles then the
packing gap is at most `ε|V|²`, because `ν₃* ≤ #triangles` and `ν₃ ≥ 0`. -/
theorem nibbleGap_fewTriangles {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (h : ((G.cliqueFinset 3).card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have h1 := nu3star_le_card_triangles G
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The residual.**  The packing gap for the graphs that neither branch above covers: those that
fail the density threshold (some vertex has degree below `θ|V|`) *and* are triangle-rich (more than
`ε|V|²` triangles).  Stated for every threshold `θ ∈ (0,1)` because the dense branch's threshold
depends on `ε`.

This is a *true* statement (a special case of the Haxell–Rödl theorem), unlike the previous blocker
`NearRegObligationSized`, which asserts near-regularity of the triangle hypergraph of an arbitrary
graph and is false. -/
def NibbleGapResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (∃ x : V, (G.degree x : ℝ) < θ * (Fintype.card V : ℝ)) →
      ε * (Fintype.card V : ℝ) ^ 2 < ((G.cliqueFinset 3).card : ℝ) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The reduction.**  `NibbleGapHyp` follows from the residual alone: the dense case is discharged
unconditionally by `nibbleGap_dense` and the triangle-poor case by `nibbleGap_fewTriangles`. -/
theorem nibbleGapHyp_of_residual (h : NibbleGapResidual) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨θ, hθ0, hθ1, n₁, hdense⟩ := nibbleGap_dense ε hε
  obtain ⟨n₂, hres⟩ := h ε hε θ hθ0 hθ1
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ _ G _ hV
  by_cases hmin : ∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)
  · exact hdense V G (le_trans (le_max_left _ _) hV) hmin
  push Not at hmin
  rcases le_or_gt ((G.cliqueFinset 3).card : ℝ) (ε * (Fintype.card V : ℝ) ^ 2) with hfew | hmany
  · exact nibbleGap_fewTriangles G hfew
  · exact hres V G (le_trans (le_max_right _ _) hV) hmin hmany

/-- **AX1 from the residual.**  Combines the reduction with the proved strong-duality input
`Nibble.AX1.strongDualityHyp_holds`. -/
theorem ax1_holds_of_residual (h : NibbleGapResidual) : AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap strongDualityHyp_holds (nibbleGapHyp_of_residual h)

end Nibble.AX1

end


/-! # CoreGapAX1 -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Monotonicity of the packing numbers under edge deletion -/

/-- The triangle hypergraph is monotone in the graph. -/
theorem triangleHypergraphE_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G' ≤ G) : triangleHypergraphE G' ⊆ triangleHypergraphE G := by
  unfold triangleHypergraphE
  exact Finset.image_subset_image (SimpleGraph.cliqueFinset_mono G h)

/-- **`ν₃` is monotone.**  Every edge-disjoint triangle packing of a spanning subgraph is one of the
graph itself. -/
theorem nu3_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G' ≤ G) :
    nu3 G' ≤ nu3 G := by
  classical
  unfold nu3
  refine Finset.sup_le ?_
  intro M hM
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact nu3_ge G ⟨hM.2.subset.trans (triangleHypergraphE_mono G G' h), hM.2.disjoint⟩

/-- A triangle of `G` that is not a triangle of the spanning subgraph `G'` has one of its three
edges among the deleted ones. -/
theorem exists_deleted_edge (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G)
    (hT' : T ∉ triangleHypergraphE G') :
    ∃ e ∈ G.cliqueFinset 2 \ G'.cliqueFinset 2, e ∈ T := by
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  by_contra hcon
  push Not at hcon
  refine hT' ?_
  rw [triangleHypergraphE, Finset.mem_image]
  refine ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, ht.card_eq⟩, rfl⟩
  intro a ha b hb hab
  have hmem : ({a, b} : Finset V) ∈ t.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hab⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h2 : ({a, b} : Finset V) ∈ G.cliqueFinset 2 :=
    powersetCard_two_subset_cliqueFinset G ht hmem
  have hin : ({a, b} : Finset V) ∈ G'.cliqueFinset 2 := by
    by_contra hc
    exact hcon _ (Finset.mem_sdiff.mpr ⟨h2, hc⟩) hmem
  rw [SimpleGraph.mem_cliqueFinset_iff] at hin
  exact hin.1 (by simp) (by simp) hab

/-- **`ν₃*` is stable under edge deletion.**  Deleting a set `D` of edges decreases the fractional
triangle packing number by at most `|D|`: the weight carried by the triangles that are destroyed is
at most the total edge load of `D`, which is at most `|D|`. -/
theorem nu3star_le_add_deleted (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    nu3star G ≤ nu3star G' + ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) := by
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨hnn, hzero, hcon⟩ := hw
  set D : Finset (Finset V) := G.cliqueFinset 2 \ G'.cliqueFinset 2 with hD
  set H : Finset (Finset (Finset V)) := triangleHypergraphE G with hH
  set H' : Finset (Finset (Finset V)) := triangleHypergraphE G' with hH'
  have hsub : H' ⊆ H := triangleHypergraphE_mono G G' hle
  set w' : Finset (Finset V) → ℝ := fun T => if T ∈ H' then w T else 0 with hw'def
  have hw'nn : ∀ T, 0 ≤ w' T := by
    intro T
    dsimp only [w', hw'def]
    split
    · exact hnn T
    · exact le_refl 0
  have hw' : IsFracPacking G' w' := by
    refine ⟨hw'nn, ?_, ?_⟩
    · intro T hT
      dsimp only [w', hw'def]
      rw [ite_eq_right hT]
    · intro e
      calc ∑ T ∈ H'.filter (fun T => e ∈ T), w' T
          = ∑ T ∈ H'.filter (fun T => e ∈ T), w T := by
            refine Finset.sum_congr rfl (fun T hT => ?_)
            dsimp only [w', hw'def]
            rw [ite_eq_left (Finset.mem_filter.mp hT).1]
        _ ≤ ∑ T ∈ H.filter (fun T => e ∈ T), w T :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ hsub) (fun T _ _ => hnn T)
        _ ≤ 1 := hcon e
  have hval : ∑ T ∈ H', w' T ≤ nu3star G' := le_csSup (nu3star_bddAbove G') ⟨w', hw', rfl⟩
  have heq : ∑ T ∈ H', w' T = ∑ T ∈ H', w T :=
    Finset.sum_congr rfl (fun T hT => by dsimp only [w', hw'def]; rw [ite_eq_left hT])
  have hsplit : ∑ T ∈ H \ H', w T + ∑ T ∈ H', w T = ∑ T ∈ H, w T := Finset.sum_sdiff hsub
  have hkey : ∑ T ∈ H \ H', w T ≤ (D.card : ℝ) := by
    have step1 : ∀ T ∈ H \ H', w T ≤ ∑ e ∈ D, (if e ∈ T then w T else 0) := by
      intro T hT
      rw [Finset.mem_sdiff] at hT
      obtain ⟨e, heD, heT⟩ := exists_deleted_edge G G' hT.1 hT.2
      calc w T = (if e ∈ T then w T else 0) := by rw [ite_eq_left heT]
        _ ≤ ∑ e ∈ D, (if e ∈ T then w T else 0) := by
            refine Finset.single_le_sum (f := fun e => if e ∈ T then w T else 0) ?_ heD
            intro i _
            split
            · exact hnn T
            · exact le_refl 0
    calc ∑ T ∈ H \ H', w T ≤ ∑ T ∈ H \ H', ∑ e ∈ D, (if e ∈ T then w T else 0) :=
          Finset.sum_le_sum step1
      _ = ∑ e ∈ D, ∑ T ∈ H \ H', (if e ∈ T then w T else 0) := Finset.sum_comm
      _ = ∑ e ∈ D, ∑ T ∈ (H \ H').filter (fun T => e ∈ T), w T := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ e ∈ D, ∑ T ∈ H.filter (fun T => e ∈ T), w T := by
          refine Finset.sum_le_sum (fun e _ => ?_)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ Finset.sdiff_subset) (fun T _ _ => hnn T)
      _ ≤ ∑ _e ∈ D, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcon e)
      _ = (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith only [hsplit, heq, hval, hkey]

/-- **The packing gap is stable under edge deletion.** -/
theorem gap_le_core_gap (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    nu3star G - (nu3 G : ℝ)
      ≤ (nu3star G' - (nu3 G' : ℝ)) + ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) := by
  have h1 := nu3star_le_add_deleted G G' hle
  have h2 : (nu3 G' : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast nu3_mono G G' hle
  linarith

/-! ### The low-degree core -/

/-- `G` with every edge at a vertex of `K` deleted. -/
@[expose] def restrictAway (G : SimpleGraph V) (K : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ K ∧ y ∉ K
  symm := ⟨by rintro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

instance instDecidableRelRestrictAway (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) :
    DecidableRel (restrictAway G K).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ x ∉ K ∧ y ∉ K))

omit [Fintype V] [DecidableEq V] in
theorem restrictAway_le (G : SimpleGraph V) (K : Finset V) : restrictAway G K ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
theorem restrictAway_mono (G : SimpleGraph V) {K K' : Finset V} (h : K ⊆ K') :
    restrictAway G K' ≤ restrictAway G K :=
  fun _ _ hx => ⟨hx.1, fun hc => hx.2.1 (h hc), fun hc => hx.2.2 (h hc)⟩

theorem cliqueFinset_two_restrictAway_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    (restrictAway G ∅).cliqueFinset 2 = G.cliqueFinset 2 := by
  ext e
  simp only [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · rintro ⟨hc, hcard⟩
    exact ⟨fun a ha b hb hab => (hc ha hb hab).1, hcard⟩
  · rintro ⟨hc, hcard⟩
    exact ⟨fun a ha b hb hab => ⟨hc ha hb hab, by simp, by simp⟩, hcard⟩

theorem restrictAway_degree_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] {K : Finset V} {v : V}
    (hv : v ∈ K) : (restrictAway G K).degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
  rintro ⟨-, h, -⟩
  exact h hv

/-- Isolating one more vertex destroys at most `deg v` edges. -/
theorem deleted_insert_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) :
    ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2).card
      ≤ (restrictAway G K).degree v := by
  have hsub : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
      ⊆ ((restrictAway G K).neighborFinset v).image (fun u => ({v, u} : Finset V)) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨he1, he2⟩ := he
    rw [SimpleGraph.mem_cliqueFinset_iff] at he1
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he1.card_eq
    have hadj : (restrictAway G K).Adj a b := he1.1 (by simp) (by simp) hab
    have hnadj : ¬ (restrictAway G (insert v K)).Adj a b := by
      intro hc
      refine he2 (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hc
      · exact hc.symm
      · exact absurd rfl hxy
    have hv : a = v ∨ b = v := by
      by_contra hcon
      push Not at hcon
      exact hnadj ⟨hadj.1, by simp [hadj.2.1, hcon.1], by simp [hadj.2.2, hcon.2]⟩
    rw [Finset.mem_image]
    rcases hv with rfl | rfl
    · exact ⟨b, by rw [SimpleGraph.mem_neighborFinset]; exact hadj, rfl⟩
    · exact ⟨a, by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm, by rw [Finset.pair_comm]⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_image_le ?_
  rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- The support of `G`: its non-isolated vertices. -/
def posDeg (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun x => 0 < G.degree x)

omit [DecidableEq V] in
theorem mem_posDeg_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    x ∈ posDeg G ↔ 0 < G.degree x := by
  simp only [posDeg, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq V] in
theorem card_posDeg_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    (posDeg G).card ≤ Fintype.card V := Finset.card_le_univ _

/-- **The core.**  Iteratively isolating the vertices of positive degree below `t` produces a
spanning subgraph in which every vertex is isolated or has degree at least `t`, at a cost of at
most `t·m` deleted edges, where `m` bounds the number of non-isolated vertices. -/
theorem exists_core_aux (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ∀ (m : ℕ) (K : Finset V), (posDeg (restrictAway G K)).card ≤ m →
    ∃ K' : Finset V, K ⊆ K' ∧
      (∀ x, (restrictAway G K').degree x = 0 ∨ t ≤ ((restrictAway G K').degree x : ℝ)) ∧
      (((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2).card : ℝ)
        ≤ t * m := by
  intro m
  induction m with
  | zero =>
      intro K hK
      refine ⟨K, Finset.Subset.refl _, ?_, by simp⟩
      intro x
      left
      by_contra hc
      have hx : x ∈ posDeg (restrictAway G K) := by
        rw [mem_posDeg_iff]
        omega
      have := Finset.card_pos.mpr ⟨x, hx⟩
      omega
  | succ m ih =>
      intro K hK
      by_cases hgood : ∀ x, (restrictAway G K).degree x = 0 ∨
          t ≤ ((restrictAway G K).degree x : ℝ)
      · refine ⟨K, Finset.Subset.refl _, hgood, ?_⟩
        simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
        positivity
      push Not at hgood
      obtain ⟨v, hv0, hvt⟩ := hgood
      have hvpos : 0 < (restrictAway G K).degree v := Nat.pos_of_ne_zero hv0
      have hvmem : v ∈ posDeg (restrictAway G K) := (mem_posDeg_iff _ v).mpr hvpos
      have hcard : (posDeg (restrictAway G (insert v K))).card ≤ m := by
        have hsub : posDeg (restrictAway G (insert v K)) ⊆
            (posDeg (restrictAway G K)).erase v := by
          intro x hx
          rw [mem_posDeg_iff] at hx
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · rintro rfl
            rw [restrictAway_degree_eq_zero G (Finset.mem_insert_self x K)] at hx
            omega
          · rw [mem_posDeg_iff]
            exact lt_of_lt_of_le hx
              (SimpleGraph.degree_le_of_le (restrictAway_mono G (Finset.subset_insert v K)))
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvmem] at hle
        omega
      obtain ⟨K', hKK', hprop, hdel⟩ := ih (insert v K) hcard
      refine ⟨K', Finset.Subset.trans (Finset.subset_insert v K) hKK', hprop, ?_⟩
      have hsplit : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2)
          ⊆ ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
            ∪ ((restrictAway G (insert v K)).cliqueFinset 2 \
                (restrictAway G K').cliqueFinset 2) := by
        intro e he
        rw [Finset.mem_sdiff] at he
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
        by_cases hc : e ∈ (restrictAway G (insert v K)).cliqueFinset 2
        · exact Or.inr ⟨hc, he.2⟩
        · exact Or.inl ⟨he.1, hc⟩
      have hc1 := deleted_insert_card_le G K v
      have hcard2 : (((restrictAway G K).cliqueFinset 2 \
          (restrictAway G K').cliqueFinset 2).card : ℝ)
          ≤ ((restrictAway G K).degree v : ℝ) +
            (((restrictAway G (insert v K)).cliqueFinset 2 \
              (restrictAway G K').cliqueFinset 2).card : ℝ) := by
        have h1 := Finset.card_le_card hsplit
        have h2 := Finset.card_union_le
          ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
          ((restrictAway G (insert v K)).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2)
        have h3 : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2).card
            ≤ (restrictAway G K).degree v +
              ((restrictAway G (insert v K)).cliqueFinset 2 \
                (restrictAway G K').cliqueFinset 2).card := by omega
        exact_mod_cast h3
      push_cast
      nlinarith only [hdel, hcard2, hvt]

/-- **The core, unpacked.**  Every graph has a spanning subgraph in which every vertex is isolated
or of degree at least `t`, obtained by deleting at most `t·|V|` edges. -/
theorem exists_core (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : Finset V,
      (∀ x, (restrictAway G K).degree x = 0 ∨ t ≤ ((restrictAway G K).degree x : ℝ)) ∧
      ((G.cliqueFinset 2 \ (restrictAway G K).cliqueFinset 2).card : ℝ)
        ≤ t * (Fintype.card V : ℝ) := by
  obtain ⟨K, -, hprop, hdel⟩ :=
    exists_core_aux G ht (Fintype.card V) ∅ (card_posDeg_le (restrictAway G ∅))
  refine ⟨K, hprop, ?_⟩
  rwa [cliqueFinset_two_restrictAway_empty G] at hdel

/-! ### The dense branch in the presence of isolated vertices -/

omit [DecidableEq V] in
theorem neighborFinset_subset_posDeg (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    G.neighborFinset u ⊆ posDeg G := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rw [mem_posDeg_iff, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
  exact ⟨u, by rw [SimpleGraph.mem_neighborFinset]; exact hy.symm⟩

theorem edgeV_pair (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    ∃ u v : V, u ≠ v ∧ E.val = ({u, v} : Finset V) := by
  have h2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  obtain ⟨u, v, huv, h⟩ := Finset.card_eq_two.mp h2
  exact ⟨u, v, huv, h⟩

/-- **Support ceiling.**  Every edge lies in at most `|support|` triangles. -/
theorem triangleSub_degree_le_support (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ ((posDeg G).card : ℝ) := by
  obtain ⟨u, v, -, hE⟩ := edgeV_pair G E
  rw [triangleSub_degree_eq_inter G E u v hE]
  have h : (G.neighborFinset u ∩ G.neighborFinset v).card ≤ (posDeg G).card :=
    Finset.card_le_card
      (Finset.Subset.trans Finset.inter_subset_left (neighborFinset_subset_posDeg G u))
  exact_mod_cast h

/-- **Support floor.**  If every non-isolated vertex has degree at least `D`, then every edge lies
in at least `2D − |support|` triangles: the two neighbourhoods live inside the support. -/
theorem triangleSub_degree_ge_support (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G)
    {D : ℕ} (hD : ∀ x : V, 0 < G.degree x → D ≤ G.degree x) :
    2 * (D : ℝ) - ((posDeg G).card : ℝ)
      ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
  obtain ⟨u, v, huv, hE⟩ := edgeV_pair G E
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp E.2
  rw [hE] at hclique
  have hadj : G.Adj u v := hclique.1 (by simp) (by simp) huv
  have hdu : 0 < G.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact hadj⟩
  have hdv : 0 < G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨u, by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm⟩
  rw [triangleSub_degree_eq_inter G E u v hE]
  have hunion : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ (posDeg G).card :=
    Finset.card_le_card (Finset.union_subset (neighborFinset_subset_posDeg G u)
      (neighborFinset_subset_posDeg G v))
  have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have h1 := hD u hdu
  have h2 := hD v hdv
  have hnat : 2 * D ≤ (posDeg G).card + (G.neighborFinset u ∩ G.neighborFinset v).card := by omega
  have hR : (2 * D : ℝ) ≤ ((posDeg G).card : ℝ)
      + ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) := by exact_mod_cast hnat
  linarith

theorem cliqueFinset_two_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (posDeg G).card = 0) : G.cliqueFinset 2 = ∅ := by
  rw [Finset.card_eq_zero] at h
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he.card_eq
  have hadj : G.Adj u v := he.1 (by simp) (by simp) huv
  have hu : u ∈ posDeg G := by
    rw [mem_posDeg_iff, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact hadj⟩
  rw [h] at hu
  exact absurd hu (Finset.notMem_empty u)

/-- A graph with no edges has zero packing gap. -/
theorem gap_le_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} (hc : 0 ≤ c)
    (h : (posDeg G).card = 0) : nu3star G - (nu3 G : ℝ) ≤ c := by
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  rw [cliqueFinset_two_eq_empty G h] at h1
  simp only [Finset.card_empty, Nat.cast_zero, zero_div] at h1
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The dense branch, tolerating isolated vertices.**  For every `ε > 0` there is a density
threshold `θ < 1` and a size threshold `n₀` such that every graph on at least `n₀` vertices all of
whose vertices are isolated or of degree at least `θ|V|` satisfies `ν₃* − ν₃ ≤ ε|V|²`.

The triangle hypergraph lives on the edges, so the isolated vertices are invisible to it: run the
nibble at the scale `d = |support|`, at which the hypergraph is near-`d`-regular with an *empty*
exceptional set. -/
theorem nibbleGap_denseCore (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ x : V, G.degree x = 0 ∨ θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  have hmpos : 0 < min μ 1 := lt_min hμ one_pos
  have hm1 : min μ 1 ≤ 1 := min_le_right _ _
  have hmμ : min μ 1 ≤ μ := min_le_left _ _
  have hθ0 : (0 : ℝ) < 1 - min μ 1 / 2 := by linarith
  have hθ1 : (1 : ℝ) - min μ 1 / 2 < 1 := by linarith
  refine ⟨1 - min μ 1 / 2, hθ0, hθ1,
    ⌈max d₀ (max (1 / μ) 1) / (1 - min μ 1 / 2)⌉₊, ?_⟩
  intro V _ _ G _ hV hdeg
  set θ : ℝ := 1 - min μ 1 / 2 with hθdef
  set R : ℝ := max d₀ (max (1 / μ) 1) with hRdef
  have hnR : R / θ ≤ (Fintype.card V : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hRθn : R ≤ θ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hθ0] at hnR; linarith
  rcases Nat.eq_zero_or_pos (posDeg G).card with hs0 | hspos
  · exact gap_le_of_no_edges G (by positivity) hs0
  obtain ⟨x, hx⟩ : ∃ x, x ∈ posDeg G := Finset.card_pos.mp hspos
  rw [mem_posDeg_iff] at hx
  have hdegx : θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ) := by
    rcases hdeg x with h | h
    · omega
    · exact h
  -- the support is large
  have hxs : (G.degree x : ℝ) ≤ ((posDeg G).card : ℝ) := by
    have h : G.degree x ≤ (posDeg G).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (neighborFinset_subset_posDeg G x)
    exact_mod_cast h
  have hsupp : θ * (Fintype.card V : ℝ) ≤ ((posDeg G).card : ℝ) := le_trans hdegx hxs
  have hsR : R ≤ ((posDeg G).card : ℝ) := le_trans hRθn hsupp
  have hd0 : d₀ ≤ ((posDeg G).card : ℝ) := le_trans (le_max_left _ _) hsR
  have hinv : 1 / μ ≤ ((posDeg G).card : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsR
  have hspos' : (0 : ℝ) < ((posDeg G).card : ℝ) := by exact_mod_cast hspos
  have hcodeg : (1 : ℝ) ≤ μ * ((posDeg G).card : ℝ) := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  have hsn : ((posDeg G).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast card_posDeg_le G
  -- the integer degree floor
  set D : ℕ := ⌈θ * (Fintype.card V : ℝ)⌉₊ with hDdef
  have hD : ∀ y : V, 0 < G.degree y → D ≤ G.degree y := by
    intro y hy
    refine Nat.ceil_le.mpr ?_
    rcases hdeg y with h | h
    · omega
    · exact h
  have hDR : θ * (Fintype.card V : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
  -- the near-regularity window at scale `d = |support|`
  have hwindow : ∀ E : EdgeV G,
      (1 - μ) * ((posDeg G).card : ℝ) ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ)
          ≤ (1 + μ) * ((posDeg G).card : ℝ) := by
    intro E
    have hlo := triangleSub_degree_ge_support G E hD
    have hhi := triangleSub_degree_le_support G E
    have hθs : θ * ((posDeg G).card : ℝ) ≤ θ * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hsn hθ0.le
    constructor
    · nlinarith
    · nlinarith
  have hreg : NearlyRegularMost (triangleHypergraphSub G) ((posDeg G).card : ℝ) μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G ∅
      (by
        rw [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hη.le (Nat.cast_nonneg _))
      (fun E _ => (hwindow E).1) (fun E _ => (hwindow E).2)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * ((posDeg G).card : ℝ)) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) ((posDeg G).card : ℝ) hspos' hd0
      (triangleHypergraphSub_uniform G) hreg hcod (fun E => (hwindow E).2)
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- **A new unconditional branch: graphs with a dense core.**  For every `ε > 0` there are `θ < 1`
and `n₀` such that every large graph which becomes (isolated-or-)`θ|V|`-dense after deleting at most
`(ε/4)|V|²` edges has packing gap at most `ε|V|²`.

This strictly extends `Nibble.AX1.nibbleGap_dense` (take `G' = G`, no deletion): the graph
itself may
have arbitrarily many vertices of arbitrarily small positive degree, as long as the edges at
them are
few. -/
theorem nibbleGap_of_dense_core (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ G' : SimpleGraph V, ∀ _ : DecidableRel G'.Adj, G' ≤ G →
          ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) ≤ (ε / 4) * (Fintype.card V : ℝ) ^ 2 →
          (∀ x : V, G'.degree x = 0 ∨ θ * (Fintype.card V : ℝ) ≤ (G'.degree x : ℝ)) →
          nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2) := by
  obtain ⟨θ, hθ0, hθ1, n₀, hdense⟩ := nibbleGap_denseCore (3 * ε / 4) (by linarith)
  refine ⟨θ, hθ0, hθ1, n₀, ?_⟩
  intro V _ _ G _ hV G' _ hle hdel hdeg
  have hgap' := hdense V G' hV hdeg
  have hstab := gap_le_core_gap G G' hle
  linarith

/-! ### The residual -/

/-- **The core packing-gap statement at parameters `(ε, δ)`.**  The gap `ν₃* − ν₃ ≤ ε|V|²` for large
graphs in which every vertex is isolated or has degree at least `δ|V|`, and whose fractional packing
number exceeds `ε|V|²` (otherwise the conclusion is immediate from `ν₃ ≥ 0`). -/
@[expose] def CoreGapAt (ε δ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    (∀ x : V, G.degree x = 0 ∨ δ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
    ε * (Fintype.card V : ℝ) ^ 2 < nu3star G →
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual.**  The core packing gap at every pair of parameters. -/
@[expose] def CoreGapResidual : Prop := ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → CoreGapAt ε δ

/-- Raising the degree threshold weakens the statement. -/
theorem CoreGapAt.mono_delta {ε δ δ' : ℝ} (h : CoreGapAt ε δ) (hδ : δ ≤ δ') : CoreGapAt ε δ' := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg hrich
  refine hmain V G hV (fun x => ?_) hrich
  rcases hdeg x with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) h)

/-- Raising the error term weakens the statement. -/
theorem CoreGapAt.mono_eps {ε ε' δ : ℝ} (h : CoreGapAt ε δ) (hε : ε ≤ ε') : CoreGapAt ε' δ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg _
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  rcases lt_or_ge (ε * (Fintype.card V : ℝ) ^ 2) (nu3star G) with hlt | hge
  · have := hmain V G hV hdeg hlt
    nlinarith
  · have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- **`CoreGapAt` is unconditionally true for `ε ≥ 1/3`**, since `ν₃* ≤ |E|/3 ≤ |V|²/3`. -/
theorem coreGapAt_of_third {ε δ : ℝ} (hε : 1 / 3 ≤ ε) : CoreGapAt ε δ := by
  refine ⟨0, ?_⟩
  intro V _ _ G _ _ _ _
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have h2 : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have h3 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith

/-- **`CoreGapAt` is unconditionally true near the top of the density range.**  For every `ε > 0`
there is `θ < 1` with `CoreGapAt ε θ` — hence, by `CoreGapAt.mono_delta`, `CoreGapAt ε δ` for every
`δ ≥ θ`.  This is the satisfiability witness for the residual: it is a nonempty, non-circular family
of true statements, proved from the nibble, not from the target. -/
theorem coreGapAt_dense (ε : ℝ) (hε : 0 < ε) : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ CoreGapAt ε θ := by
  obtain ⟨θ, hθ0, hθ1, n₀, hmain⟩ := nibbleGap_denseCore ε hε
  exact ⟨θ, hθ0, hθ1, n₀, fun V _ _ G _ hV hdeg _ => hmain V G hV hdeg⟩

/-! ### The reduction -/

/-- **The reduction.**  `NibbleGapResidual` follows from the core residual: delete the edges at all
vertices of positive degree below `(ε/4)|V|` — this costs at most `(ε/4)|V|²` edges, hence at most
that much of the packing gap — and apply the core residual to the resulting graph. -/
theorem nibbleGapResidual_of_coreGapResidual (h : CoreGapResidual) : NibbleGapResidual := by
  intro ε hε θ _ _
  obtain ⟨n₁, hres⟩ := h (ε / 2) (by linarith) (ε / 4) (by linarith)
  refine ⟨n₁, ?_⟩
  intro V _ _ G _ hV _ _
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  obtain ⟨K, hprop, hdel⟩ := exists_core G (t := (ε / 4) * (Fintype.card V : ℝ)) (by positivity)
  have hle : restrictAway G K ≤ G := restrictAway_le G K
  have hgap' : nu3star (restrictAway G K) - (nu3 (restrictAway G K) : ℝ)
      ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 := by
    rcases lt_or_ge ((ε / 2) * (Fintype.card V : ℝ) ^ 2) (nu3star (restrictAway G K))
      with hlt | hge
    · exact hres V (restrictAway G K) hV hprop hlt
    · have h2 : (0 : ℝ) ≤ (nu3 (restrictAway G K) : ℝ) := Nat.cast_nonneg _
      linarith
  have hstab := gap_le_core_gap G (restrictAway G K) hle
  nlinarith only [hdel, hstab, hgap']

/-- **`NibbleGapHyp` from the core residual.** -/
theorem nibbleGapHyp_of_coreGapResidual (h : CoreGapResidual) : NibbleGapHyp :=
  nibbleGapHyp_of_residual (nibbleGapResidual_of_coreGapResidual h)

/-- **AX1 from the core residual**, combining with the proved `strongDualityHyp_holds`. -/
theorem ax1_of_coreGapResidual (h : CoreGapResidual) : AX1Statement :=
  ax1_holds_of_residual (nibbleGapResidual_of_coreGapResidual h)

/-- **The Haxell–Rödl packing gap** for triangle hypergraphs: `ν₃*(G) − ν₃(G) = o(|V|²)` for every
graph.  This is the published theorem the whole AX1 chain is an instance of; it is recorded here
only to certify that the residual below it is genuinely true, never used as an input to anything
proved. -/
def HaxellRodlGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual is a special case of Haxell–Rödl**, hence true and not refutable. -/
theorem coreGapResidual_of_haxellRodl (h : HaxellRodlGap) : CoreGapResidual := by
  intro ε hε _ _
  obtain ⟨n₀, hmain⟩ := h ε hε
  exact ⟨n₀, fun V _ _ G _ hV _ _ => hmain V G hV⟩

/-- **The converse reduction.**  `NibbleGapResidual` implies the core residual as well (the dense
instances being supplied by `nibbleGap_denseCore`), so the reformulation is lossless: nothing has
been strengthened, and the two residuals are equivalent. -/
theorem coreGapResidual_of_nibbleGapResidual (h : NibbleGapResidual) : CoreGapResidual := by
  intro ε hε δ _
  obtain ⟨θ, hθ0, hθ1, n₁, hdense⟩ := nibbleGap_denseCore ε hε
  obtain ⟨n₂, hres⟩ := h ε hε θ hθ0 hθ1
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ _ G _ hV hdeg hrich
  by_cases hmin : ∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)
  · exact hdense V G (le_trans (le_max_left _ _) hV) (fun x => Or.inr (hmin x))
  push Not at hmin
  refine hres V G (le_trans (le_max_right _ _) hV) hmin ?_
  exact lt_of_lt_of_le hrich (nu3star_le_card_triangles G)

end Nibble.AX1
