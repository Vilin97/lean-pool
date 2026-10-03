/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Helly

/-!
# Chordality is equivalent to having a clique tree

`CliqueTree/PEO.lean` builds a clique tree out of a perfect elimination order of a chordal graph.
This file proves the converse implications, turning both constructions into characterisations of
chordality:

* a graph carrying a clique tree is chordal (`SimpleGraph.IsChordal.of_nonempty_cliqueTree`);
* a graph carrying a perfect elimination order is chordal (`SimpleGraph.IsPEO.isChordal`).

The proof of the first statement is direct, with no induction on the graph.  Given a cycle of
length at least `4`, pick the vertex `z` of the cycle whose top node is deepest, i.e. of largest
rank.  The two neighbours of `z` along the cycle share a bag with `z`, so by maximality of the rank
they both lie in the bag of `top z`; that bag is a clique, so they are adjacent, and being at
distance two along a cycle of length at least `4` their edge is not an edge of the cycle.

## Main results

* `SimpleGraph.IsChordal.of_nonempty_cliqueTree`
* `SimpleGraph.isChordal_iff_nonempty_cliqueTree`
* `SimpleGraph.IsPEO.isChordal`
* `SimpleGraph.isChordal_iff_exists_isPEO`
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every edge of a walk joins two consecutive vertices of the walk. -/
private theorem exists_getVert_eq_of_mem_edges : ∀ {u v : V} (w : G.Walk u v) {e : Sym2 V},
    e ∈ w.edges → ∃ i, i < w.length ∧ e = s(w.getVert i, w.getVert (i + 1)) := by
  intro u v w
  induction w with
  | nil => simp
  | cons h p ih =>
      intro e he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨i, hi, hei⟩ := ih he
        exact ⟨i + 1, by simpa using hi, by simpa using hei⟩

/-- In a cycle of length at least `4` the two neighbours of the base point are distinct. -/
private theorem chord_ne {z : V} {c : G.Walk z z} (hc : c.IsCycle) (hn : 4 ≤ c.length) :
    c.getVert 1 ≠ c.getVert (c.length - 1) := by
  intro h
  have := hc.getVert_injOn (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
    (show c.length - 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h
  omega

/-- In a cycle of length at least `4`, the pair formed by the two neighbours of the base point is
not an edge of the cycle. -/
private theorem chord_notMem_edges {z : V} {c : G.Walk z z} (hc : c.IsCycle) (hn : 4 ≤ c.length) :
    s(c.getVert 1, c.getVert (c.length - 1)) ∉ c.edges := by
  intro hmem
  obtain ⟨i, hi, hei⟩ := exists_getVert_eq_of_mem_edges c hmem
  have hinj := hc.getVert_injOn
  have hzn : c.getVert c.length = z := c.getVert_length
  have hz0 : c.getVert 0 = z := c.getVert_zero
  rcases Sym2.eq_iff.1 hei with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have : (1 : ℕ) = c.length :=
        hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (by rw [h₁, hz0, hzn])
      omega
    · have e₁ : (1 : ℕ) = i :=
        hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show i ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₁
      have e₂ : c.length - 1 = i + 1 :=
        hinj (show c.length - 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show i + 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₂
      omega
  · have e₁ : (1 : ℕ) = i + 1 :=
      hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (show i + 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₁
    have hi0 : i = 0 := by omega
    subst hi0
    have : c.length - 1 = c.length :=
      hinj (show c.length - 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (by rw [h₂, hz0, hzn])
    omega

/-- **A graph carrying a clique tree is chordal.** -/
theorem IsChordal.of_nonempty_cliqueTree {ι : Type*} (T : CliqueTree G ι) : G.IsChordal := by
  classical
  intro v c hc hlen
  obtain ⟨z, hz, hzmax⟩ :=
    Finset.exists_max_image c.support.toFinset (fun u => T.rank (T.top u)) ⟨v, by simp⟩
  have hzs : z ∈ c.support := by simpa using hz
  have hcycle := hc.rotate hzs
  have hrot : (c.rotate z hzs).edges ~r c.edges := c.rotate_edges z hzs
  set c' := c.rotate z hzs with hc'def
  have hlen' : c'.length = c.length := by
    have h := hrot.perm.length_eq
    rwa [Walk.length_edges, Walk.length_edges] at h
  have hn : 4 ≤ c'.length := by omega
  -- the two neighbours of `z` along the cycle
  have hadjzx : G.Adj z (c'.getVert 1) := by
    have := c'.adj_getVert_succ (i := 0) (by omega)
    rwa [Walk.getVert_zero] at this
  have hadjyz : G.Adj (c'.getVert (c'.length - 1)) z := by
    have := c'.adj_getVert_succ (i := c'.length - 1) (by omega)
    rwa [show c'.length - 1 + 1 = c'.length by omega, Walk.getVert_length] at this
  have hsupp : ∀ w ∈ c'.support, w ∈ c.support := by
    intro w hw
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hzs
    · exact List.mem_of_mem_tail ((c.support_rotate z hzs).mem_iff.1 hw)
  have hxs : c'.getVert 1 ∈ c.support := hsupp _ (c'.getVert_mem_support 1)
  have hys : c'.getVert (c'.length - 1) ∈ c.support :=
    hsupp _ (c'.getVert_mem_support (c'.length - 1))
  -- the chord
  obtain ⟨k, hzk, hxk⟩ := T.exists_bag_of_adj hadjzx
  have hxbag : c'.getVert 1 ∈ T.bag (T.top z) :=
    CliqueTree.mem_bag_top_of_rank_le hzk hxk (hzmax _ (by simpa using hxs))
  obtain ⟨k₂, hyk, hzk₂⟩ := T.exists_bag_of_adj hadjyz
  have hybag : c'.getVert (c'.length - 1) ∈ T.bag (T.top z) :=
    CliqueTree.mem_bag_top_of_rank_le hzk₂ hyk (hzmax _ (by simpa using hys))
  refine ⟨c'.getVert 1, c'.getVert (c'.length - 1), hxs, hys,
    T.bag_isClique (T.top z) (by simpa using hxbag) (by simpa using hybag)
      (chord_ne hcycle hn), fun hmemE => chord_notMem_edges hcycle hn (hrot.mem_iff.2 hmemE)⟩

/-- **Chordality is exactly the existence of a clique tree.** -/
theorem isChordal_iff_nonempty_cliqueTree [Finite V] :
    G.IsChordal ↔ Nonempty (CliqueTree G V) :=
  ⟨fun hG => hG.nonempty_cliqueTree, fun ⟨T⟩ => IsChordal.of_nonempty_cliqueTree T⟩

/-- **A graph carrying a perfect elimination order is chordal.** -/
theorem IsPEO.isChordal [Finite V] {ord : V → ℕ} (h : G.IsPEO ord) :
    G.IsChordal := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel _
  exact IsChordal.of_nonempty_cliqueTree h.cliqueTree

/-- **Chordality is exactly the existence of a perfect elimination order.** -/
theorem isChordal_iff_exists_isPEO [Finite V] :
    G.IsChordal ↔ ∃ ord : V → ℕ, G.IsPEO ord :=
  ⟨fun hG => hG.exists_isPEO, fun ⟨_, h⟩ => h.isChordal⟩

end SimpleGraph
