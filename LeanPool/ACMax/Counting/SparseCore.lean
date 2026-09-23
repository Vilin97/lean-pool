/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import LeanPool.ACMax.Counting.Quotient
public import LeanPool.ACMax.Cuts.WeightedCut

/-!
# Sparse-boundary cores from internal edge excess

If a vertex set carries more ordered internal adjacent pairs than twice its total
degree excess above three, iterative deletion cannot remove every vertex while
always deleting a vertex with at least three external neighbors.  The surviving
set has external degree at most two at every vertex.
-/

@[expose] public section

namespace ACMax

open Finset

noncomputable section

/-- Use the same finite-set decisions as the classical graph certificates. -/
local instance sparseCoreFinDecidableEq {n : ℕ} : DecidableEq (Fin n) := Classical.decEq _

open Classical in
/-- A displayed set of internal neighbors subtracts from the number of edges
leaving a vertex set. -/
theorem neighbor_sdiff_card_add_le_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (S K : Finset (Fin n)) (v : Fin n)
    (hK : K ⊆ G.neighborFinset v ∩ S) :
    (G.neighborFinset v \ S).card + K.card ≤ G.degree v := by
  have hpart : (G.neighborFinset v ∩ S).card +
      (G.neighborFinset v \ S).card = G.degree v := by
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hKcard := Finset.card_le_card hK
  omega

open Classical in
/-- The number of ordered adjacent pairs contained in `S`. -/
def internalPairCount {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card

open Classical in
theorem internalPairCount_eq_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    internalPairCount G S = ∑ v ∈ S, (G.neighborFinset v ∩ S).card := by
  rw [internalPairCount, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hset : G.neighborFinset v ∩ S = S.filter (fun w => G.Adj v w) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  rw [hset, Finset.card_filter]

open Classical in
/-- The ordered internal-pair count is even: each induced edge contributes its
two orientations. -/
theorem internalPairCount_eq_two_mul {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ∃ k : ℕ, internalPairCount G S = 2 * k := by
  classical
  let H := G.induce (↑S : Set (Fin n))
  refine ⟨H.edgeFinset.card, ?_⟩
  rw [internalPairCount]
  have hbij : (Finset.univ : Finset H.Dart).card =
      ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card := by
    apply Finset.card_bij (fun d _ => ((d.fst : Fin n), (d.snd : Fin n)))
    · intro d _
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_coe.mp d.fst.2, Finset.mem_coe.mp d.snd.2⟩, d.adj⟩
    · intro d₁ _ d₂ _ heq
      rw [Prod.mk.injEq] at heq
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2))
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hq1, hq2⟩, hadj⟩ := hq
      exact ⟨⟨(⟨q.1, Finset.mem_coe.mpr hq1⟩, ⟨q.2, Finset.mem_coe.mpr hq2⟩), hadj⟩,
        Finset.mem_univ _, rfl⟩
  rw [← hbij, Finset.card_univ, SimpleGraph.dart_card_eq_twice_card_edges]

open Classical in
private theorem neighbor_inter_card_erase {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {v x : Fin n} (hv : v ∈ S) :
    (G.neighborFinset x ∩ S).card =
      (G.neighborFinset x ∩ S.erase v).card + if G.Adj x v then 1 else 0 := by
  by_cases hadj : G.Adj x v
  · have heq : G.neighborFinset x ∩ S =
        insert v (G.neighborFinset x ∩ S.erase v) := by
      ext y
      constructor
      · intro hy
        rw [Finset.mem_inter] at hy
        by_cases hyv : y = v
        · subst y
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_inter.mpr ⟨hy.1, Finset.mem_erase.mpr ⟨hyv, hy.2⟩⟩)
      · intro hy
        rw [Finset.mem_insert] at hy
        rcases hy with hyv | hy
        · exact Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset x y).mpr (by simpa [hyv] using hadj), by simpa [hyv] using hv⟩
        · have hy' := Finset.mem_inter.mp hy
          exact Finset.mem_inter.mpr ⟨hy'.1, (Finset.mem_erase.mp hy'.2).2⟩
    have hvnot : v ∉ G.neighborFinset x ∩ S.erase v := by simp
    rw [heq, Finset.card_insert_of_notMem hvnot, ite_eq_left hadj]
  · have heq : G.neighborFinset x ∩ S = G.neighborFinset x ∩ S.erase v := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        refine Finset.mem_inter.mpr ⟨hy'.1, Finset.mem_erase.mpr ⟨?_, hy'.2⟩⟩
        intro hyv
        exact hadj (by simpa [hyv] using (G.mem_neighborFinset x y).mp hy'.1)
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        exact Finset.mem_inter.mpr ⟨hy'.1, (Finset.mem_erase.mp hy'.2).2⟩
    rw [heq, ite_eq_right hadj, add_zero]

open Classical in
private theorem adjacency_indicator_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {v : Fin n} :
    ∑ x ∈ S.erase v, (if G.Adj x v then 1 else 0) =
      (G.neighborFinset v ∩ S).card := by
  rw [← Finset.card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hxv, hxS⟩, hadj⟩
    exact ⟨G.adj_symm hadj, hxS⟩
  · rintro ⟨hadj, hxS⟩
    exact ⟨⟨(G.ne_of_adj hadj).symm, hxS⟩, G.adj_symm hadj⟩

open Classical in
/-- Removing a vertex deletes twice its internal degree from the ordered-pair count. -/
theorem internalPairCount_erase {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {v : Fin n} (hv : v ∈ S) :
    internalPairCount G S = internalPairCount G (S.erase v) +
      2 * (G.neighborFinset v ∩ S).card := by
  rw [internalPairCount_eq_sum, internalPairCount_eq_sum]
  have hadd := Finset.add_sum_erase S (fun x => (G.neighborFinset x ∩ S).card) hv
  rw [← hadd]
  have hrewrite : ∑ x ∈ S.erase v, (G.neighborFinset x ∩ S).card =
      ∑ x ∈ S.erase v,
        ((G.neighborFinset x ∩ S.erase v).card + if G.Adj x v then 1 else 0) := by
    exact Finset.sum_congr rfl fun x _ => neighbor_inter_card_erase G S hv
  rw [hrewrite, Finset.sum_add_distrib, adjacency_indicator_sum G S]
  omega

open Classical in
/-- The internal degree of one vertex accounts for twice as many ordered
internal incidences: once at each endpoint of every incident edge. -/
theorem twice_internal_degree_le_internalPairCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) {v : Fin n} (hv : v ∈ S) :
    2 * (G.neighborFinset v ∩ S).card ≤ internalPairCount G S := by
  have herase := internalPairCount_erase G S hv
  omega

open Classical in
/-- If an induced subgraph has exactly one edge, any two of its non-isolated
vertices are the endpoints of that edge. -/
theorem adj_of_internalPairCount_eq_two {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) {u v : Fin n}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (huPos : 0 < (G.neighborFinset u ∩ S).card)
    (hvPos : 0 < (G.neighborFinset v ∩ S).card)
    (hpairs : internalPairCount G S = 2) : G.Adj u v := by
  have huLe := twice_internal_degree_le_internalPairCount G S hu
  have huOne : (G.neighborFinset u ∩ S).card = 1 := by omega
  have herase : internalPairCount G (S.erase u) = 0 := by
    have hsplit := internalPairCount_erase G S hu
    omega
  rw [internalPairCount_eq_sum] at herase
  have hvErase : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hvZero : (G.neighborFinset v ∩ S.erase u).card = 0 := by
    have hterm : (G.neighborFinset v ∩ S.erase u).card ≤
        ∑ x ∈ S.erase u, (G.neighborFinset x ∩ S.erase u).card :=
      Finset.single_le_sum
        (f := fun x => (G.neighborFinset x ∩ S.erase u).card)
        (fun x _ => Nat.zero_le _) hvErase
    omega
  by_contra hnot
  have hvNonempty : (G.neighborFinset v ∩ S).Nonempty := Finset.card_pos.mp hvPos
  obtain ⟨w, hw⟩ := hvNonempty
  have hwN := (Finset.mem_inter.mp hw).1
  have hwS := (Finset.mem_inter.mp hw).2
  have hwu : w ≠ u := by
    intro hwu
    subst w
    exact hnot (G.adj_symm ((G.mem_neighborFinset v u).mp hwN))
  have hwErase : w ∈ S.erase u := Finset.mem_erase.mpr ⟨hwu, hwS⟩
  have hwMem : w ∈ G.neighborFinset v ∩ S.erase u :=
    Finset.mem_inter.mpr ⟨hwN, hwErase⟩
  have hwPos : 0 < (G.neighborFinset v ∩ S.erase u).card :=
    Finset.card_pos.mpr ⟨w, hwMem⟩
  omega

open Classical in
/-- If every induced edge is incident with `u`, then every other vertex has
internal degree at most one. The pair-count equality expresses precisely that
the edges incident with `u` exhaust the induced subgraph. -/
theorem internal_degree_le_one_of_pairCount_eq_twice_at {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) {u v : Fin n}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hpairs : internalPairCount G S =
      2 * (G.neighborFinset u ∩ S).card) :
    (G.neighborFinset v ∩ S).card ≤ 1 := by
  have hsplit := internalPairCount_erase G S hu
  have herase : internalPairCount G (S.erase u) = 0 := by omega
  rw [internalPairCount_eq_sum] at herase
  have hvErase : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hvZero : (G.neighborFinset v ∩ S.erase u).card = 0 := by
    have hterm : (G.neighborFinset v ∩ S.erase u).card ≤
        ∑ x ∈ S.erase u, (G.neighborFinset x ∩ S.erase u).card :=
      Finset.single_le_sum
        (f := fun x => (G.neighborFinset x ∩ S.erase u).card)
        (fun x _ => Nat.zero_le _) hvErase
    omega
  have hsub : G.neighborFinset v ∩ S ⊆ {u} := by
    intro w hw
    by_contra hwu
    have hwErase : w ∈ S.erase u :=
      Finset.mem_erase.mpr ⟨by simpa using hwu, (Finset.mem_inter.mp hw).2⟩
    have hwMem : w ∈ G.neighborFinset v ∩ S.erase u :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hwErase⟩
    have hwPos : 0 < (G.neighborFinset v ∩ S.erase u).card :=
      Finset.card_pos.mpr ⟨w, hwMem⟩
    omega
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton u)

open Classical in
private theorem internalPairCount_le_twice_excess_of_peelable {n : ℕ}
    (G : SimpleGraph (Fin n)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (S : Finset (Fin n))
    (hpeel : ∀ T ⊆ S, T.Nonempty →
      ∃ v ∈ T, 2 < (G.neighborFinset v \ T).card) :
    internalPairCount G S ≤ 2 * ∑ v ∈ S, (G.degree v - 3) := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hSne : S.Nonempty
  · obtain ⟨v, hv, hvout⟩ := hpeel S (by rfl) hSne
    have hproper : S.erase v ⊂ S := Finset.erase_ssubset hv
    have hpeel' : ∀ T ⊆ S.erase v, T.Nonempty →
        ∃ w ∈ T, 2 < (G.neighborFinset w \ T).card := by
      intro T hT hTne
      exact hpeel T (hT.trans hproper.subset) hTne
    have hind := ih (S.erase v) hproper hpeel'
    have hpart : (G.neighborFinset v ∩ S).card +
        (G.neighborFinset v \ S).card = G.degree v := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have hint : (G.neighborFinset v ∩ S).card ≤ G.degree v - 3 := by
      have := h3 v
      omega
    have hpairs := internalPairCount_erase G S hv
    have hexcess := Finset.add_sum_erase S (fun x => G.degree x - 3) hv
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hSne]
    simp [internalPairCount]

open Classical in
/-- If the internal ordered-pair count is larger than twice the total degree excess,
some nonempty subset has external degree at most two at every vertex. -/
theorem exists_sparse_core_of_twice_excess_lt_pairs {n : ℕ}
    (G : SimpleGraph (Fin n)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (S : Finset (Fin n))
    (hlarge : 2 * ∑ v ∈ S, (G.degree v - 3) < internalPairCount G S) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.Nonempty ∧
      ∀ v ∈ T, (G.neighborFinset v \ T).card ≤ 2 := by
  by_contra hnone
  have hpeel : ∀ T ⊆ S, T.Nonempty →
      ∃ v ∈ T, 2 < (G.neighborFinset v \ T).card := by
    intro T hT hTne
    by_contra hbad
    apply hnone
    refine ⟨T, hT, hTne, ?_⟩
    intro v hv
    have hnot : ¬2 < (G.neighborFinset v \ T).card := fun hlt =>
      (not_exists.mp hbad v) ⟨hv, hlt⟩
    omega
  exact (not_le_of_gt hlarge)
    (internalPairCount_le_twice_excess_of_peelable G h3 S hpeel)

open Classical in
/-- Two separated vertex sets certify `algConn G <= 2` when every vertex has at
most two neighbors outside its own set. -/
theorem algConn_le_two_of_sparse_core_clusters {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (S T : Finset (Fin n))
    (hSne : S.Nonempty) (hTne : T.Nonempty) (hdisj : Disjoint S T)
    (hnc : ∀ u ∈ S, ∀ v ∈ T, ¬G.Adj u v)
    (hS : ∀ u ∈ S, (G.neighborFinset u \ S).card ≤ 2)
    (hT : ∀ v ∈ T, (G.neighborFinset v \ T).card ≤ 2) :
    algConn G ≤ 2 := by
  classical
  have hcnt : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card =
        ∑ x ∈ X, (G.neighborFinset x ∩ Y).card := by
    intro X Y
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hset : G.neighborFinset x ∩ Y = Y.filter (fun y => G.Adj x y) := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  have hcutS : ((S ×ˢ (S ∪ T)ᶜ).filter (fun q => G.Adj q.1 q.2)).card ≤
      2 * S.card := by
    rw [hcnt]
    calc
      ∑ x ∈ S, (G.neighborFinset x ∩ (S ∪ T)ᶜ).card ≤
          ∑ _x ∈ S, 2 := by
        refine Finset.sum_le_sum fun x hx => le_trans (Finset.card_le_card ?_) (hS x hx)
        intro y hy
        rw [Finset.mem_inter, Finset.mem_compl, Finset.mem_union] at hy
        exact Finset.mem_sdiff.mpr ⟨hy.1, fun hyS => hy.2 (Or.inl hyS)⟩
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hcutT : ((T ×ˢ (S ∪ T)ᶜ).filter (fun q => G.Adj q.1 q.2)).card ≤
      2 * T.card := by
    rw [hcnt]
    calc
      ∑ x ∈ T, (G.neighborFinset x ∩ (S ∪ T)ᶜ).card ≤
          ∑ _x ∈ T, 2 := by
        refine Finset.sum_le_sum fun x hx => le_trans (Finset.card_le_card ?_) (hT x hx)
        intro y hy
        rw [Finset.mem_inter, Finset.mem_compl, Finset.mem_union] at hy
        exact Finset.mem_sdiff.mpr ⟨hy.1, fun hyT => hy.2 (Or.inr hyT)⟩
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  refine algConn_le_two_of_two_clusters G S T hSne hTne hdisj hnc ?_
  have hboundS := Nat.mul_le_mul hcutS (le_refl (T.card ^ 2))
  have hboundT := Nat.mul_le_mul hcutT (le_refl (S.card ^ 2))
  refine le_trans (add_le_add hboundS hboundT) (le_of_eq ?_)
  ring

open Classical in
/-- On fifteen vertices, a set of size five or six whose edge boundary is at
most one more than its order is a sparse cut. -/
theorem algConn_le_two_of_order15_cluster_sum (G : SimpleGraph (Fin 15))
    (S : Finset (Fin 15)) (hSne : S.Nonempty)
    (hcard : S.card = 5 ∨ S.card = 6)
    (hsum : ∑ v ∈ S, (G.neighborFinset v \ S).card ≤ S.card + 1) :
    algConn G ≤ 2 := by
  classical
  have hScard : Sᶜ.card = 15 - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hScne : Sᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [hScard]
    rcases hcard with h5 | h6 <;> omega
  refine algConn_le_two_of_weighted_cut G S hSne hScne ?_
  change 15 * (∑ a ∈ S, (G.neighborFinset a \ S).card) ≤
    2 * (S.card * Sᶜ.card)
  rcases hcard with h5 | h6
  · rw [h5, hScard, h5]
    omega
  · rw [h6, hScard, h6]
    omega

open Classical in
/-- Pointwise form of `algConn_le_two_of_order15_cluster_sum`: one distinguished
vertex may send two edges out and every other cluster vertex may send one. -/
theorem algConn_le_two_of_order15_cluster (G : SimpleGraph (Fin 15))
    (S : Finset (Fin 15)) (p : Fin 15) (hp : p ∈ S)
    (hcard : S.card = 5 ∨ S.card = 6)
    (hpout : (G.neighborFinset p \ S).card ≤ 2)
    (hother : ∀ v ∈ S, v ≠ p → (G.neighborFinset v \ S).card ≤ 1) :
    algConn G ≤ 2 := by
  have hsum : ∑ v ∈ S, (G.neighborFinset v \ S).card ≤ S.card + 1 := by
    calc
      ∑ v ∈ S, (G.neighborFinset v \ S).card ≤
          ∑ v ∈ S, (1 + if v = p then 1 else 0) := by
        refine Finset.sum_le_sum fun v hv => ?_
        by_cases hvp : v = p
        · subst v
          simpa using hpout
        · simpa [hvp] using hother v hv hvp
      _ = S.card + 1 := by
        rw [Finset.sum_add_distrib]
        simp [hp]
  exact algConn_le_two_of_order15_cluster_sum G S ⟨p, hp⟩ hcard hsum

end

end ACMax
