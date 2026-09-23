/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Cuts.WeightedCut

/-!
# A disconnected graph has algebraic connectivity at most `2`

If the vertex set splits as `A ⊔ Aᶜ` (both nonempty) with no edges between the parts,
then the cut is empty, so the weighted-cut certificate gives `algConn G ≤ 2` (indeed
`algConn G = 0`).  This handles disconnected graphs uniformly for every `n`.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- If `G` has a nonempty proper vertex set `A` with no edges to its complement, then
`algConn G ≤ 2`. -/
theorem algConn_le_two_of_separated {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b, b ∉ A → ¬ G.Adj a b) :
    algConn G ≤ 2 := by
  classical
  refine algConn_le_two_of_weighted_cut G A hA hAc ?_
  have hzero : ∀ a ∈ A, G.neighborFinset a \ A = ∅ := by
    intro a ha
    ext b
    simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.notMem_empty,
      iff_false, not_and]
    intro hadj hbA
    exact hsep a ha b hbA hadj
  have hsum : ∑ a ∈ A, (G.neighborFinset a \ A).card = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a ha
    rw [hzero a ha, Finset.card_empty]
  rw [hsum, Nat.mul_zero]
  exact Nat.zero_le _

open Classical in
/-- A disconnected graph (on a nonempty vertex type) has `algConn G ≤ 2` — uniformly, for every
`n`.  The connected component of any vertex is a nonempty proper set with no edges leaving it, so
`algConn_le_two_of_separated` applies. -/
theorem algConn_le_two_of_not_connected {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : ¬ G.Connected) :
    algConn G ≤ 2 := by
  classical
  -- `G` is not connected: either not preconnected, or `V` is empty (excluded by `Nonempty`).
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  -- The reachability class of `v`.
  set A : Finset V := Finset.univ.filter (fun u => G.Reachable v u) with hA
  have hvA : v ∈ A := by rw [hA]; simp
  have hAne : A.Nonempty := ⟨v, hvA⟩
  -- No edges leave `A`: a neighbour of a reachable vertex is reachable.
  have hsep : ∀ a ∈ A, ∀ b, b ∉ A → ¬ G.Adj a b := by
    intro a ha b hb hadj
    rw [hA, Finset.mem_filter] at ha
    exact hb (by rw [hA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha.2.trans hadj.reachable⟩)
  -- `A` is proper: otherwise every vertex is reachable from `v`, making `G` connected.
  have hAc : Aᶜ.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hcon
    refine hG ?_
    refine ⟨?_⟩
    · intro x y
      have hx : G.Reachable v x := by
        have : x ∈ A := by rw [hcon]; exact Finset.mem_univ _
        rw [hA, Finset.mem_filter] at this; exact this.2
      have hy : G.Reachable v y := by
        have : y ∈ A := by rw [hcon]; exact Finset.mem_univ _
        rw [hA, Finset.mem_filter] at this; exact this.2
      exact hx.symm.trans hy
  exact algConn_le_two_of_separated G A hAne hAc hsep

end ACMax
