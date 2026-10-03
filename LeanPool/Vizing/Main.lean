/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Vizing's theorem, upper bound

Iterating the extension step colours all edges, giving a proper edge colouring with
`Δ + 1` colours; equivalently, the line graph is `(Δ + 1)`-colourable.
-/

public section

open SimpleGraph Finset

namespace LeanPool.Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

/-- The colouring that colours nothing. -/
def empty (G : SimpleGraph V) (C : Type*) : PEC G C where
  col := fun _ _ => none
  col_symm := fun _ _ => rfl
  col_adj := by intro u v γ h; exact absurd h (by simp)
  col_proper := by intro u v w γ h; exact absurd h (by simp)

/-- The set of (ordered) uncoloured edges. -/
noncomputable def uncoloured [DecidableRel G.Adj] (c : PEC G C) : Finset (V × V) :=
  {p ∈ (Finset.univ : Finset (V × V)) | G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none}

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma mem_uncoloured [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by
  classical
  simp [uncoloured]

omit [DecidableEq V] [DecidableEq C] in
/-- Every graph has a proper edge colouring with more than `Δ` colours. -/
theorem exists_total [DecidableRel G.Adj] (hcard : G.maxDegree < Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  suffices H : ∀ (k : ℕ) (c : PEC G C), c.uncoloured.card ≤ k →
      ∃ c' : PEC G C, ∀ u v, G.Adj u v → c'.col u v ≠ none by
    exact H (empty G C).uncoloured.card (empty G C) le_rfl
  intro k
  induction k with
  | zero =>
    intro c hk
    refine ⟨c, fun u v huv hcol => ?_⟩
    have hmem : (u, v) ∈ c.uncoloured := (c.mem_uncoloured (u, v)).2 ⟨huv, hcol⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  | succ k ih =>
    intro c hk
    by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
    · exact ⟨c, hall⟩
    · push Not at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ := vizing_step c hcard hadj (by simpa using hnone)
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, by simpa using hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega

/-! ### From total colourings to colourings of the line graph -/

/-- The optional colour on an unordered pair. -/
@[expose]
def edgeOption (c : PEC G C) (e : Sym2 V) : Option C :=
  Sym2.lift ⟨c.col, c.col_symm⟩ e

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
@[simp] lemma edgeOption_mk (c : PEC G C) (u v : V) :
    c.edgeOption s(u, v) = c.col u v := rfl

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
/-- Totality supplies a colour on every actual edge, even for an empty palette. -/
lemma edgeOption_ne_none (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 ≠ none := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact htot u v he

/-- The colour of an actual edge, extracted from totality without a default colour. -/
noncomputable def edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) : C :=
  Classical.choose (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma edgeOption_eq_some_edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 = some (c.edgeColor htot e) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))

/-- A total proper partial colouring gives a colouring of the line graph. -/
noncomputable def lineGraphColoring (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) : (G.lineGraph).Coloring C :=
  Coloring.mk (c.edgeColor htot) (by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hv₁, hv₂⟩ := hadj
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
    intro hcol
    have hγ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, u), he₁⟩
    have hδ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, w), he₂⟩
    simp only [edgeOption_mk] at hγ hδ
    rw [← hcol] at hδ
    have huw : u = w := c.col_proper hγ hδ
    subst huw
    exact hne (Subtype.ext rfl))

end PEC

/-- **Vizing's theorem (upper bound)**: the line graph of a finite simple graph `G` is
`(Δ(G) + 1)`-colourable, i.e. `G` has a proper edge colouring with `Δ(G) + 1` colours. -/
theorem lineGraph_colorable {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.lineGraph).Colorable (G.maxDegree + 1) := by
  classical
  obtain ⟨c, hc⟩ := PEC.exists_total (G := G) (C := Fin (G.maxDegree + 1))
    (by simp)
  exact ⟨c.lineGraphColoring hc⟩

end LeanPool.Vizing

namespace SimpleGraph

/-- **Vizing's theorem** (upper bound), edge-chromatic-number form:
`χ'(G) ≤ Δ(G) + 1`, phrased via the line graph. -/
theorem lineGraph_chromaticNumber_le_maxDegree_succ {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lineGraph).chromaticNumber ≤ (G.maxDegree : ℕ∞) + 1 := by
  have h : (G.lineGraph).Colorable (G.maxDegree + 1) := LeanPool.Vizing.lineGraph_colorable G
  have := h.chromaticNumber_le
  simpa only [Nat.cast_add, Nat.cast_one] using this

end SimpleGraph
