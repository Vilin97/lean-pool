/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.GluingSimplicial

/-!
# Chordality of a graph glued along a retained clique

Eliminate a simplicial vertex outside the shared clique in the left piece,
unless the current vertex set lies entirely in the right piece. The no-cross
condition ensures that left-exclusive vertices acquire no extra neighbours.
The existing simplicial-elimination ranking then yields a PEO and chordality.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Chordality of an induced piece passes to an induced subset of that piece. -/
theorem IsChordal.induce_finset_subset {A S : Finset V}
    (hA : (G.induce (↑A : Set V)).IsChordal) (hSA : S ⊆ A) :
    (G.induce (↑S : Set V)).IsChordal := by
  let f : (↑S : Set V) ↪ (↑A : Set V) :=
    ⟨fun x => ⟨x.1, hSA x.2⟩, fun x y h =>
      Subtype.ext (congrArg (fun z : (↑A : Set V) => z.1) h)⟩
  exact hA.comap f

/-- A nonempty chordal induced vertex set contains a relative simplicial vertex. -/
theorem IsChordal.exists_relative_simplicial {S : Finset V}
    (hS : (G.induce (↑S : Set V)).IsChordal) (hSne : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  let : Nonempty (↑S : Set V) := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  obtain ⟨z, hz⟩ := hS.exists_isSimplicial
  refine ⟨z.1, z.2, ?_⟩
  intro a ha b hb hza hzb hab
  have ha' : (⟨a, ha⟩ : (↑S : Set V)) ∈ (G.induce (↑S : Set V)).neighborSet z := hza
  have hb' : (⟨b, hb⟩ : (↑S : Set V)) ∈ (G.induce (↑S : Set V)).neighborSet z := hzb
  exact hz ha' hb' (fun h => hab (congrArg Subtype.val h))

namespace CliqueGluing

variable [Fintype V] [DecidableEq V] {A B : Finset V} (h : G.CliqueGluing A B)

include h

/-- Every remaining nonempty vertex set admits simplicial elimination when
both induced pieces are chordal. The shared clique is retained until needed. -/
theorem exists_relative_simplicial
    (hA : (G.induce (↑A : Set V)).IsChordal)
    (hB : (G.induce (↑B : Set V)).IsChordal) (S : Finset V) (hSne : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  classical
  by_cases hSB : S ⊆ B
  · exact (hB.induce_finset_subset hSB).exists_relative_simplicial hSne
  · obtain ⟨u, huS, huB⟩ := Finset.not_subset.mp hSB
    have huA := (h.mem_left_or_right u).resolve_right huB
    have hSA := hA.induce_finset_subset (Finset.inter_subset_right (s₁ := S) (s₂ := A))
    have hclique : (G.induce (↑(S ∩ A) : Set V)).IsClique {v | v.1 ∈ B} := by
      intro x hx y hy hxy
      exact h.overlap_isClique
        (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.2).2, hx⟩)
        (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp y.2).2, hy⟩)
        (fun heq => hxy (Subtype.ext heq))
    obtain ⟨z, hzB, hz⟩ := hSA.exists_isSimplicial_not_mem_clique hclique
      ⟨⟨u, Finset.mem_inter.mpr ⟨huS, huA⟩⟩, huB⟩
    have hzS := (Finset.mem_inter.mp z.2).1
    have hzA := (Finset.mem_inter.mp z.2).2
    refine ⟨z.1, hzS, ?_⟩
    intro a ha b hb hza hzb hab
    have haSA := Finset.mem_inter.mpr ⟨ha, h.neighbor_mem_left hzA hzB hza⟩
    have hbSA := Finset.mem_inter.mpr ⟨hb, h.neighbor_mem_left hzA hzB hzb⟩
    have ha' : (⟨a, haSA⟩ : (↑(S ∩ A) : Set V)) ∈
        (G.induce (↑(S ∩ A) : Set V)).neighborSet z := hza
    have hb' : (⟨b, hbSA⟩ : (↑(S ∩ A) : Set V)) ∈
        (G.induce (↑(S ∩ A) : Set V)).neighborSet z := hzb
    exact hz ha' hb' (fun heq => hab (congrArg Subtype.val heq))

/-- Gluing chordal induced pieces along a retained clique preserves chordality. -/
theorem isChordal
    (hA : (G.induce (↑A : Set V)).IsChordal)
    (hB : (G.induce (↑B : Set V)).IsChordal) : G.IsChordal := by
  obtain ⟨f, hinj, hclique⟩ := exists_rank_of_simplicial_elimination
    (h.exists_relative_simplicial hA hB) Finset.univ.card Finset.univ rfl
  have hPEO : G.IsPEO f := by
    constructor
    · intro a b hab
      exact hinj (Finset.mem_univ a) (Finset.mem_univ b) hab
    · intro v a ha b hb hab
      exact hclique v (Finset.mem_univ v)
        ⟨Finset.mem_univ a, ha⟩ ⟨Finset.mem_univ b, hb⟩ hab
  exact hPEO.isChordal

/-- A graph glued along a retained clique is chordal exactly when both pieces are. -/
theorem isChordal_iff :
    G.IsChordal ↔ (G.induce (↑A : Set V)).IsChordal ∧
      (G.induce (↑B : Set V)).IsChordal :=
  ⟨fun hG => ⟨hG.induce _, hG.induce _⟩, fun hp => h.isChordal hp.1 hp.2⟩

/-- The glued graph admits a clique forest on its original vertex type.
This constructs a fresh forest from an elimination order, not a graft of supplied trees. -/
theorem nonempty_cliqueTree
    (hA : (G.induce (↑A : Set V)).IsChordal)
    (hB : (G.induce (↑B : Set V)).IsChordal) : Nonempty (G.CliqueTree V) :=
  (h.isChordal hA hB).nonempty_cliqueTree

end CliqueGluing

end SimpleGraph
