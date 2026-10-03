/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the shape clauses of a design, for blocks spread over **several** cluster triples

`Nibble.AX1.subTripleShape_grid` (`Nibble.CoreGapTripleShape`) builds the local clauses of a design
out of the diagonal grid inside **one** cluster triple.  The assembly of the AX1 residual needs the
same clauses for a family whose members live in *different* cluster triples: the edge-disjointness
can then no longer come from the diagonal indices, and is instead required of the family as an
input — in the strong form of disjointness of the vertex-pair rectangles
(`Nibble.AX1.tripleRect`).

* `Nibble.AX1.IsGridSubTriple` — one sub-triple of blocks inside a good cluster triple: blocks of
  relative size at least `α`, of sizes `≈ τ·(opposite density)`;
* `Nibble.AX1.subTripleShape_of_gridSubTriples` — **the shape**: such a family, with pairwise
  disjoint rectangles, satisfies every local clause of `Nibble.AX1.IsSubTripleDesignLocal` for the
  regularity-reduced graph, with common triangle-degree scale `d i = τ·xᵢyᵢzᵢ`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapTripleShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRectPack
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularCover


/-! # CoreGapReducedPair -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **On a good cluster pair the reduced graph agrees with `G`.** -/
theorem regularityReduced_adj_iff_of_goodPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    {x y : V} (hx : x ∈ U) (hy : y ∈ W) :
    (G.regularityReduced P ep de).Adj x y ↔ G.Adj x y := by
  constructor
  · intro h; exact h.1
  · intro h
    exact ⟨h, U, hU, W, hW, hx, hy, hUW, hu, hd⟩

/-- The interedges of two sub-blocks of a good cluster pair are the same in `G` and in the reduced
graph. -/
theorem interedges_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) :
    (G.regularityReduced P ep de).interedges A B = G.interedges A B := by
  ext p
  obtain ⟨x, y⟩ := p
  simp only [SimpleGraph.mk_mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, hadj⟩
    exact ⟨hx, hy, hadj.1⟩
  · rintro ⟨hx, hy, hadj⟩
    exact ⟨hx, hy,
      (regularityReduced_adj_iff_of_goodPair G P hU hW hUW hu hd (hA hx) (hB hy)).mpr hadj⟩

/-- The densities of two sub-blocks of a good cluster pair are the same in `G` and in the reduced
graph. -/
theorem edgeDensity_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) :
    (G.regularityReduced P ep de).edgeDensity A B = G.edgeDensity A B := by
  rw [SimpleGraph.edgeDensity_def, SimpleGraph.edgeDensity_def,
    interedges_regularityReduced G P hU hW hUW hu hd hA hB]

/-- **Uniformity of a pair of sub-blocks transfers to the reduced graph.** -/
theorem isUniform_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de ε : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) (h : G.IsUniform ε A B) :
    (G.regularityReduced P ep de).IsUniform ε A B := by
  intro A' hA' B' hB' hcA hcB
  have h1 : (G.regularityReduced P ep de).edgeDensity A' B' = G.edgeDensity A' B' :=
    edgeDensity_regularityReduced G P hU hW hUW hu hd (hA'.trans hA) (hB'.trans hB)
  have h2 : (G.regularityReduced P ep de).edgeDensity A B = G.edgeDensity A B :=
    edgeDensity_regularityReduced G P hU hW hUW hu hd hA hB
  rw [h1, h2]
  exact h hA' hB' hcA hcB

end Nibble.AX1

end


/-! # CoreGapBlockShape -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **One sub-triple of the grid construction**: blocks `A ⊆ U`, `B ⊆ W`, `C ⊆ X` of a good cluster
triple, each of relative size at least `α` in its cluster, with sizes proportional to the density of
the *opposite* pair at the common scale `τ`. -/
@[expose]
def IsGridSubTriple (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de α τ : ℝ) (U W X A B C : Finset V) : Prop :=
  GoodTriple G P ep de U W X ∧ A ⊆ U ∧ B ⊆ W ∧ C ⊆ X ∧
  α * (#U : ℝ) ≤ (#A : ℝ) ∧ α * (#W : ℝ) ≤ (#B : ℝ) ∧ α * (#X : ℝ) ≤ (#C : ℝ) ∧
  |(#A : ℝ) - τ * (G.edgeDensity W X : ℝ)| ≤ 1 ∧
  |(#B : ℝ) - τ * (G.edgeDensity U X : ℝ)| ≤ 1 ∧
  |(#C : ℝ) - τ * (G.edgeDensity U W : ℝ)| ≤ 1

/-- **The three pairs of one block sub-triple**: they are disjoint, uniform at scale `ε₁/(8α)` in
the reduced graph, and their densities are within `ε₁/8` of the densities of the cluster pairs. -/
theorem gridSubTriple_data (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {δ α τ ε₁ : ℝ} {U W X A B C : Finset V}
    (hε₁ : 0 < ε₁) (hαε : ε₁ / 8 ≤ α) (hα2 : 2 * α ≤ 1) (hde : ε₁ / 4 ≤ δ)
    (h : IsGridSubTriple G P (ε₁ / 8) δ α τ U W X A B C) :
    (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) ∧
    ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).IsUniform (ε₁ / 8 / α) A B ∧
      (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).IsUniform (ε₁ / 8 / α) A C ∧
      (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).IsUniform (ε₁ / 8 / α) B C) ∧
    (|((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity A B : ℝ)
        - (G.edgeDensity U W : ℝ)| ≤ ε₁ / 8 ∧
      |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity A C : ℝ)
        - (G.edgeDensity U X : ℝ)| ≤ ε₁ / 8 ∧
      |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity B C : ℝ)
        - (G.edgeDensity W X : ℝ)| ≤ ε₁ / 8) := by
  classical
  have hε : (0:ℝ) < ε₁ / 8 := by linarith only [hε₁]
  obtain ⟨hgood, hAU, hBW, hCX, hrelA, hrelB, hrelC, hsA, hsB, hsC⟩ := h
  obtain ⟨hU, hW, hX, hUW, hUX, hWX, huUW, hdUW, huUX, hdUX, huWX, hdWX⟩ := hgood
  have hdisjUW : Disjoint U W := P.disjoint hU hW hUW
  have hdisjUX : Disjoint U X := P.disjoint hU hX hUX
  have hdisjWX : Disjoint W X := P.disjoint hW hX hWX
  have hdUW' : ε₁ / 4 ≤ (G.edgeDensity U W : ℝ) := le_trans hde hdUW
  have hdUX' : ε₁ / 4 ≤ (G.edgeDensity U X : ℝ) := le_trans hde hdUX
  have hdWX' : ε₁ / 4 ≤ (G.edgeDensity W X : ℝ) := le_trans hde hdWX
  refine ⟨⟨Finset.disjoint_of_subset_left hAU (Finset.disjoint_of_subset_right hBW hdisjUW),
    Finset.disjoint_of_subset_left hAU (Finset.disjoint_of_subset_right hCX hdisjUX),
    Finset.disjoint_of_subset_left hBW (Finset.disjoint_of_subset_right hCX hdisjWX)⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact isUniform_regularityReduced G P hU hW hUW huUW hdUW' hAU hBW
      (isUniform_subblock G huUW hε hAU hBW hαε hα2 hrelA hrelB)
  · exact isUniform_regularityReduced G P hU hX hUX huUX hdUX' hAU hCX
      (isUniform_subblock G huUX hε hAU hCX hαε hα2 hrelA hrelC)
  · exact isUniform_regularityReduced G P hW hX hWX huWX hdWX' hBW hCX
      (isUniform_subblock G huWX hε hBW hCX hαε hα2 hrelB hrelC)
  · rw [edgeDensity_regularityReduced G P hU hW hUW huUW hdUW' hAU hBW]
    exact le_of_lt (edgeDensity_sub_lt_of_isUniform G huUW hAU hBW hαε hrelA hrelB)
  · rw [edgeDensity_regularityReduced G P hU hX hUX huUX hdUX' hAU hCX]
    exact le_of_lt (edgeDensity_sub_lt_of_isUniform G huUX hAU hCX hαε hrelA hrelC)
  · rw [edgeDensity_regularityReduced G P hW hX hWX huWX hdWX' hBW hCX]
    exact le_of_lt (edgeDensity_sub_lt_of_isUniform G huWX hBW hCX hαε hrelB hrelC)

/-- The cluster densities of a good triple lie in `[δ, 1]`. -/
theorem gridSubTriple_density_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {δ α τ ep : ℝ} {U W X A B C : Finset V}
    (h : IsGridSubTriple G P ep δ α τ U W X A B C) :
    (δ ≤ (G.edgeDensity U W : ℝ) ∧ (G.edgeDensity U W : ℝ) ≤ 1) ∧
    (δ ≤ (G.edgeDensity U X : ℝ) ∧ (G.edgeDensity U X : ℝ) ≤ 1) ∧
    (δ ≤ (G.edgeDensity W X : ℝ) ∧ (G.edgeDensity W X : ℝ) ≤ 1) := by
  obtain ⟨⟨-, -, -, -, -, -, -, hdUW, -, hdUX, -, hdWX⟩, -⟩ := h
  refine ⟨⟨hdUW, ?_⟩, ⟨hdUX, ?_⟩, ⟨hdWX, ?_⟩⟩
  · exact_mod_cast G.edgeDensity_le_one U W
  · exact_mod_cast G.edgeDensity_le_one U X
  · exact_mod_cast G.edgeDensity_le_one W X

/-- **The local clauses of a design, for a family of block sub-triples.** -/
theorem subTripleShape_of_gridSubTriples (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {δ α τ μ₂ ε₁ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset V)
    (hε₁ : 0 < ε₁) (hαε : ε₁ / 8 ≤ α) (hα2 : 2 * α ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hμ0 : 0 < μ₂) (hμ1 : μ₂ ≤ 1)
    (hde : ε₁ / 4 ≤ δ)
    (hErr : ε₁ / 8 + 2 * (ε₁ / 8 / α) ≤ μ₂ * δ ^ 3 / 12)
    (hdense : 2 * (ε₁ / 8 / α) + ε₁ / 8 ≤ δ)
    (hτ : 2 / (μ₂ * δ ^ 3) ≤ τ)
    (hgrid : ∀ i < k, IsGridSubTriple G P (ε₁ / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    IsSubTripleShape (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) (ε₁ / 8 / α) μ₂ k A B C
      (fun i => τ * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
        * (G.edgeDensity (W i) (X i) : ℝ))) := by
  classical
  set H : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hH
  have hε : (0:ℝ) < ε₁ / 8 := by linarith only [hε₁]
  have hα0 : 0 < α := lt_of_lt_of_le hε hαε
  have hε₂ : (0:ℝ) < ε₁ / 8 / α := div_pos hε hα0
  -- the data of the `i`-th sub-triple
  have hdata : ∀ i < k,
      (Disjoint (A i) (B i) ∧ Disjoint (A i) (C i) ∧ Disjoint (B i) (C i)) ∧
      (H.IsUniform (ε₁ / 8 / α) (A i) (B i) ∧ H.IsUniform (ε₁ / 8 / α) (A i) (C i) ∧
        H.IsUniform (ε₁ / 8 / α) (B i) (C i)) ∧
      (|(H.edgeDensity (A i) (B i) : ℝ) - (G.edgeDensity (U i) (W i) : ℝ)| ≤ ε₁ / 8 ∧
        |(H.edgeDensity (A i) (C i) : ℝ) - (G.edgeDensity (U i) (X i) : ℝ)| ≤ ε₁ / 8 ∧
        |(H.edgeDensity (B i) (C i) : ℝ) - (G.edgeDensity (W i) (X i) : ℝ)| ≤ ε₁ / 8) :=
    fun i hi => gridSubTriple_data G P hε₁ hαε hα2 hde (hgrid i hi)
  have hclus : ∀ i < k,
      (δ ≤ (G.edgeDensity (U i) (W i) : ℝ) ∧ (G.edgeDensity (U i) (W i) : ℝ) ≤ 1) ∧
      (δ ≤ (G.edgeDensity (U i) (X i) : ℝ) ∧ (G.edgeDensity (U i) (X i) : ℝ) ≤ 1) ∧
      (δ ≤ (G.edgeDensity (W i) (X i) : ℝ) ∧ (G.edgeDensity (W i) (X i) : ℝ) ≤ 1) :=
    fun i hi => gridSubTriple_density_mem G P (hgrid i hi)
  have hlow : ∀ (u v : ℝ), δ ≤ v → |u - v| ≤ ε₁ / 8 → 2 * (ε₁ / 8 / α) ≤ u := by
    intro u v hv habs
    have := (abs_le.mp habs).1
    linarith only [hdense, hv, this]
  refine ⟨fun i hi => (hdata i hi).1.1, fun i hi => (hdata i hi).1.2.1,
    fun i hi => (hdata i hi).1.2.2, fun i hi => (hdata i hi).2.1.1,
    fun i hi => (hdata i hi).2.1.2.1, fun i hi => (hdata i hi).2.1.2.2, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i hi => hlow _ _ (hclus i hi).1.1 (hdata i hi).2.2.1
  · exact fun i hi => hlow _ _ (hclus i hi).2.1.1 (hdata i hi).2.2.2.1
  · exact fun i hi => hlow _ _ (hclus i hi).2.2.1 (hdata i hi).2.2.2.2
  -- the three scale windows
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (X i) : ℝ))
      (y := (G.edgeDensity (W i) (X i) : ℝ)) (z := (G.edgeDensity (U i) (W i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdata i hi).2.2.2.1 (hdata i hi).2.2.2.2 hsC
      (by linarith) hε₂ hμ0 hμ1 hErr hτ (by ring)).1
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (X i) : ℝ))
      (y := (G.edgeDensity (W i) (X i) : ℝ)) (z := (G.edgeDensity (U i) (W i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdata i hi).2.2.2.1 (hdata i hi).2.2.2.2 hsC
      (by linarith) hε₂ hμ0 hμ1 hErr hτ (by ring)).2
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (W i) : ℝ))
      (y := (G.edgeDensity (W i) (X i) : ℝ)) (z := (G.edgeDensity (U i) (X i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdata i hi).2.2.1 (hdata i hi).2.2.2.2 hsB
      (by linarith) hε₂ hμ0 hμ1 hErr hτ (by ring)).1
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (W i) : ℝ))
      (y := (G.edgeDensity (W i) (X i) : ℝ)) (z := (G.edgeDensity (U i) (X i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdata i hi).2.2.1 (hdata i hi).2.2.2.2 hsB
      (by linarith) hε₂ hμ0 hμ1 hErr hτ (by ring)).2
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (W i) : ℝ))
      (y := (G.edgeDensity (U i) (X i) : ℝ)) (z := (G.edgeDensity (W i) (X i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdata i hi).2.2.1 (hdata i hi).2.2.2.1 hsA
      (by linarith) hε₂ hμ0 hμ1 hErr hτ rfl).1
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := hclus i hi
    exact (scale_window (x := (G.edgeDensity (U i) (W i) : ℝ))
      (y := (G.edgeDensity (U i) (X i) : ℝ)) (z := (G.edgeDensity (W i) (X i) : ℝ))
      (δ := δ) (μ := μ₂) (ε := ε₁ / 8 / α) (e := ε₁ / 8)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdata i hi).2.2.1 (hdata i hi).2.2.2.1 hsA
      (by linarith) hε₂ hμ0 hμ1 hErr hτ rfl).2
  · intro i hi j hj hij x y hxy
    exact tripleGraph_edgeDisjoint_of_rect_disjoint H (hdisj i hi j hj hij) x y hxy

end Nibble.AX1
