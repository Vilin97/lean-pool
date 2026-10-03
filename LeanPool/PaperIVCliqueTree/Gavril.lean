/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini
-/
module

public import LeanPool.PaperIVCliqueTree.SubtreeRepresentation
public import LeanPool.PaperIVCliqueTree.SubtreeHelly

/-!
# Gavril's characterization of finite chordal graphs

For the converse, prune leaves of the host tree until some represented subtree
is a singleton. Its vertex is simplicial. Repeating this argument on any finite
subfamily gives a perfect elimination order through the existing PEO engine.

The theorem formalized here is F. Gavril, "The intersection graphs of subtrees
in trees are exactly the chordal graphs", JCT B 16 (1974), 47–56,
doi:10.1016/0095-8956(74)90094-X. No recognition algorithm or runtime bound is claimed.
-/

public section

namespace SimpleGraph

private theorem subtree_family_simplicial_of_subsingleton
    {N : Type} [Subsingleton N] (T : SimpleGraph N)
    {V : Type*} (G : SimpleGraph V) (F : Finset V) (hF : F.Nonempty)
    (S : V → Set N) (hc : ∀ i ∈ F, (T.induce (S i)).Connected)
    (ha : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (G.Adj i j ↔ (S i ∩ S j).Nonempty)) :
    ∃ z ∈ F, ∀ a ∈ F, ∀ b ∈ F, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  obtain ⟨z, hz⟩ := hF
  refine ⟨z, hz, fun a hfa b hfb _ _ hab => ?_⟩
  obtain ⟨x⟩ := (hc a hfa).nonempty
  obtain ⟨y⟩ := (hc b hfb).nonempty
  exact (ha a hfa b hfb hab).mpr
    ⟨x.val, x.property, Subsingleton.elim y.val x.val ▸ y.property⟩

private theorem subtree_family_simplicial_of_singleton
    {N : Type} {V : Type*} (G : SimpleGraph V) (F : Finset V) (S : V → Set N)
    {leaf : N} (hsingle : ∃ z ∈ F, ¬ ∃ x ∈ S z, x ≠ leaf)
    (ha : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (G.Adj i j ↔ (S i ∩ S j).Nonempty)) :
    ∃ z ∈ F, ∀ a ∈ F, ∀ b ∈ F, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  obtain ⟨z, hz, hs⟩ := hsingle
  refine ⟨z, hz, fun a hfa b hfb hza hzb hab => ?_⟩
  obtain ⟨x, hxz, hxa⟩ := (ha z hz a hfa hza.ne).mp hza
  obtain ⟨y, hyz, hyb⟩ := (ha z hz b hfb hzb.ne).mp hzb
  exact (ha a hfa b hfb hab).mpr
    ⟨leaf, eq_leaf_of_no_other hs hxz ▸ hxa, eq_leaf_of_no_other hs hyz ▸ hyb⟩

private theorem subtree_family_simplicial_aux : ∀ n : ℕ,
    ∀ {N : Type} [Fintype N] (T : SimpleGraph N), Fintype.card N = n → T.IsTree →
    ∀ {V : Type*} (G : SimpleGraph V) (F : Finset V), F.Nonempty →
    ∀ (S : V → Set N), (∀ i ∈ F, (T.induce (S i)).Connected) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → (G.Adj i j ↔ (S i ∩ S j).Nonempty)) →
      ∃ z ∈ F, ∀ a ∈ F, ∀ b ∈ F, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N _ T hcard hT V G F hF S hc ha
    classical
    rcases subsingleton_or_nontrivial N with hsmall | hlarge
    · let _ := hsmall
      exact subtree_family_simplicial_of_subsingleton T G F hF S hc ha
    · let _ := hlarge
      obtain ⟨leaf, hdegree⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨neighbour, hadj, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hdegree
      by_cases hsingle : ∃ z ∈ F, ¬ ∃ x ∈ S z, x ≠ leaf
      · exact subtree_family_simplicial_of_singleton G F S hsingle ha
      · have hother : ∀ i ∈ F, ∃ x ∈ S i, x ≠ leaf := by
          intro i hi
          by_contra h
          exact hsingle ⟨i, hi, h⟩
        obtain ⟨hlt, ht, hc', hp⟩ := hT.prune_subtree_family hadj hunique F S hc hother
        refine ih _ (hlt.trans_eq hcard) (T.induce ({leaf}ᶜ : Set N)) rfl ht G F hF
          (fun i => prunedSet (S i) leaf) hc' ?_
        intro i hi j hj hij
        exact (ha i hi j hj hij).trans
          (hp i hi j hj).symm

variable {V : Type*} {G : SimpleGraph V}

/-- Any finite graph represented exactly by subtrees of a finite tree is chordal. -/
theorem SubtreeRepresentation.isChordal [Finite V] (R : SubtreeRepresentation G) :
    G.IsChordal := by
  obtain ⟨ord, hord⟩ := exists_isPEO_of_simplicial_in_finset (G := G) (by
    intro F hF
    exact subtree_family_simplicial_aux (Fintype.card R.Node) R.tree rfl R.isTree
      G F hF R.subtree (fun i _ => R.connected i) (fun i _ j _ hij => R.adjacency i j hij))
  exact hord.isChordal

variable {V : Type} {G : SimpleGraph V}

/-- Gavril's characterization: finite chordal graphs are exactly finite-tree subtree graphs. -/
theorem isChordal_iff_nonempty_subtreeRepresentation [Finite V] :
    G.IsChordal ↔ Nonempty (SubtreeRepresentation G) :=
  ⟨IsChordal.nonempty_subtreeRepresentation, fun ⟨R⟩ => R.isChordal⟩

end SimpleGraph
