/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Push
public import LeanPool.ACMax.Counting.Moats
public import LeanPool.ACMax.Counting.SparseCore

/-!
# The sparse-core M-edge moat

For an adjacent pair of degree-three vertices, the ordinary moat has at most
four vertices.  If the remote bulk did not contain a sparse-boundary core, its
internal ordered-pair count would be at most twice its degree excess.  The moat
and bulk incidence ledgers would then force `2 * n + 2 ≤ 5 * |F|`, which is
impossible from order ten onward.
-/

@[expose] public section

namespace ACMax

open Finset

open Classical in
private theorem medge_sparse_core_fires_hslice : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u p : Fin n)
  (_ : G.Adj u p)
  (_ : G.degree u = 3) (_ : G.degree p = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = {u, p}), ∀ x ∈ S₁, #(G.neighborFinset x \ S₁) ≤ 2 := by
  classical
  intro n G u p hM hu hp this S₁ hS1def x hx
  rw [hS1def, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxu | hxp
  · subst x
    have hpMem : p ∈ G.neighborFinset u ∩ S₁ := by
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hM, by rw [hS1def]; simp⟩
    have hpart : (G.neighborFinset u ∩ S₁).card +
        (G.neighborFinset u \ S₁).card = G.degree u := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have hpos := Finset.card_pos.mpr ⟨p, hpMem⟩
    omega
  · subst x
    have huMem : u ∈ G.neighborFinset p ∩ S₁ := by
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hM.symm, by rw [hS1def]; simp⟩
    have hpart : (G.neighborFinset p ∩ S₁).card +
        (G.neighborFinset p \ S₁).card = G.degree p := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have hpos := Finset.card_pos.mpr ⟨u, huMem⟩
    omega

open Classical in
private theorem medge_sparse_core_fires_hFbound : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u p : Fin n),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = {u, p}),
    let F := (G.neighborFinset u ∪ G.neighborFinset p) \ S₁;
    let S₂ := (S₁ ∪ F)ᶜ;
    ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : F ⊆ G.neighborFinset u ∪ G.neighborFinset p),
      ∀ w ∈ F, #(G.neighborFinset w ∩ S₂) ≤ G.degree w - 1 := by
  classical
  intro n G u p this S₁ hS1def F S₂ hS2def hFsub w hw
  obtain ⟨a, ha1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
    have hw' := hFsub hw
    rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset] at hw'
    rcases hw' with huw | hpw
    · exact ⟨u, by rw [hS1def]; simp, huw⟩
    · exact ⟨p, by rw [hS1def]; simp, hpw⟩
  have haN : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
  have haNot : a ∉ S₂ := by
    rw [hS2def, Finset.mem_compl, not_not]
    exact Finset.mem_union_left F ha1
  have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_erase]
    refine ⟨?_, hx.1⟩
    rintro rfl
    exact haNot hx.2
  calc
    (G.neighborFinset w ∩ S₂).card ≤ ((G.neighborFinset w).erase a).card :=
      Finset.card_le_card hsub
    _ = G.degree w - 1 := by
      rw [Finset.card_erase_of_mem haN, G.card_neighborFinset_eq_degree]

open Classical in
private theorem medge_sparse_core_fires_hbulk : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v :
  Fin n), 3 ≤ G.degree v)
  (u p : Fin n),
  let _ := Classical.decEq (Fin n);
  let S₁ := {u, p};
  let F := (G.neighborFinset u ∪ G.neighborFinset p) \ S₁;
  ∀ (S₂ : Finset (Fin n)) (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : ∀ x ∈ S₁, ∀ y ∈ S₂, ¬G.Adj x y)
    (_ : ∀ (X Y : Finset (Fin n)), #({q ∈ X ×ˢ Y | G.Adj q.1 q.2}) = ∑ x ∈ X, #(G.neighborFinset x
      ∩ Y)),
    #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) + internalPairCount G S₂ = 3 * #S₂ + ∑ x ∈ S₂, (G.degree x -
      3) := by
  classical
  intro n G h3 u p this S₁ F S₂ hS2def hnc hcnt
  rw [hcnt S₂ F, internalPairCount_eq_sum, ← Finset.sum_add_distrib]
  have hpoint : ∀ x ∈ S₂,
      (G.neighborFinset x ∩ F).card + (G.neighborFinset x ∩ S₂).card =
        G.degree x := by
    intro x hx2
    have hsplit : G.neighborFinset x ∩ (F ∪ S₂) = G.neighborFinset x := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_union]
      refine ⟨fun hy => hy.1, fun hy => ⟨hy, ?_⟩⟩
      by_contra hnot
      push Not at hnot
      have hy1 : y ∈ S₁ := by
        have hy2 : y ∉ S₂ := hnot.2
        rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hy2
        rcases hy2 with hy1 | hyF
        · exact hy1
        · exact absurd hyF hnot.1
      exact hnc y hy1 x hx2 (G.adj_symm ((G.mem_neighborFinset x y).mp hy))
    have hdisjFS2' : Disjoint F S₂ := by
      rw [Finset.disjoint_left]
      intro y hyF hy2
      rw [hS2def, Finset.mem_compl] at hy2
      exact hy2 (Finset.mem_union_right S₁ hyF)
    have hdisjSlices : Disjoint (G.neighborFinset x ∩ F)
        (G.neighborFinset x ∩ S₂) :=
      hdisjFS2'.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← Finset.card_union_of_disjoint hdisjSlices,
      ← Finset.inter_union_distrib_left, hsplit, G.card_neighborFinset_eq_degree]
  rw [Finset.sum_congr rfl hpoint]
  have hrewrite : ∑ x ∈ S₂, G.degree x =
      ∑ x ∈ S₂, ((G.degree x - 3) + 3) :=
    Finset.sum_congr rfl (fun x _ => by have := h3 x; omega)
  rw [hrewrite, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

open Classical in
/-- An edge joining two degree-three vertices produces a sparse-core cut at
every order `n ≥ 10`. -/
theorem medge_sparse_core_fires {n : ℕ} [Nonempty (Fin n)] (hn : 10 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (u p : Fin n) (hM : G.Adj u p)
    (hu : G.degree u = 3) (hp : G.degree p = 3) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq _
  have hup : u ≠ p := hM.ne
  set S₁ : Finset (Fin n) := {u, p} with hS1def
  set F : Finset (Fin n) := (G.neighborFinset u ∪ G.neighborFinset p) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hS1card : S₁.card = 2 := by rw [hS1def]; exact Finset.card_pair hup
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u {p}
  have hFsub : F ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
    rw [hFdef]
    exact Finset.sdiff_subset
  have hFcard : F.card ≤ 4 := by
    have hsubpair : S₁ ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
      rw [hS1def]
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact Or.inr hM.symm
      · exact Or.inl hM
    have hunion : (G.neighborFinset u ∪ G.neighborFinset p).card ≤ 6 := by
      calc
        (G.neighborFinset u ∪ G.neighborFinset p).card ≤
            (G.neighborFinset u).card + (G.neighborFinset p).card :=
          Finset.card_union_le _ _
        _ = 6 := by
          rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree, hu, hp]
    rw [hFdef, Finset.card_sdiff_of_subset hsubpair, hS1card]
    omega
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro x hx1 hxF
    rw [hFdef, Finset.mem_sdiff] at hxF
    exact hxF.2 hx1
  have hS2card : S₂.card = n - (2 + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F, hS1card]
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]
    omega
  have hslice :=
      medge_sparse_core_fires_hslice (n := n) (G := G) (u := u) (p := p) (hM) (hu)
        (hp) (S₁ := S₁) (hS1def)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS2def, Finset.mem_compl] at hx2
    exact hx2 (Finset.mem_union_left F hx1)
  have hnc : ∀ x ∈ S₁, ∀ y ∈ S₂, ¬G.Adj x y := by
    intro x hx1 y hy2 hxy
    rw [hS2def, Finset.mem_compl] at hy2
    apply hy2
    by_cases hy1 : y ∈ S₁
    · exact Finset.mem_union_left F hy1
    · apply Finset.mem_union_right S₁
      rw [hFdef, Finset.mem_sdiff]
      refine ⟨?_, hy1⟩
      rw [hS1def, Finset.mem_insert, Finset.mem_singleton] at hx1
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases hx1 with rfl | rfl
      · exact Or.inl hxy
      · exact Or.inr hxy
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
  have htrans : ∀ (X Y : Finset (Fin n)),
      ((X ×ˢ Y).filter (fun q => G.Adj q.1 q.2)).card =
        ((Y ×ˢ X).filter (fun q => G.Adj q.1 q.2)).card := by
    intro X Y
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  have hEFEB : (∑ x ∈ F, (G.degree x - 3)) +
      (∑ x ∈ S₂, (G.degree x - 3)) = n - 8 := by
    have htot := total_excess_eq (by omega) G hm h3
    have hsplit : (∑ x ∈ S₁ ∪ F, (G.degree x - 3)) +
        (∑ x ∈ S₂, (G.degree x - 3)) =
          ∑ x : Fin n, (G.degree x - 3) := by
      rw [hS2def]
      exact Finset.sum_add_sum_compl _ _
    have hS1zero : ∑ x ∈ S₁, (G.degree x - 3) = 0 := by
      rw [hS1def, Finset.sum_pair hup, hu, hp]
    have hunion : ∑ x ∈ S₁ ∪ F, (G.degree x - 3) =
        (∑ x ∈ S₁, (G.degree x - 3)) + ∑ x ∈ F, (G.degree x - 3) :=
      Finset.sum_union hdisjS1F
    omega
  have hFbound : ∀ w ∈ F,
      (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 :=
      medge_sparse_core_fires_hFbound (n := n) (G := G) (u := u) (p := p) (S₁ := S₁) (hS1def)
        (hS2def) (hFsub)
  have hmoat : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤
      (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
    rw [htrans S₂ F, hcnt F S₂]
    calc
      ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤
          ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hFbound
      _ = ∑ w ∈ F, ((G.degree w - 3) + 2) :=
        Finset.sum_congr rfl (fun w _ => by have := h3 w; omega)
      _ = (∑ w ∈ F, (G.degree w - 3)) + 2 * F.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hbulk : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card +
        internalPairCount G S₂ =
      3 * S₂.card + ∑ x ∈ S₂, (G.degree x - 3) :=
      medge_sparse_core_fires_hbulk (n := n) (G := G) (h3) (u := u) (p := p) (S₂ := S₂)
        (hS2def) (hnc) (hcnt)
  have hlarge : 2 * ∑ x ∈ S₂, (G.degree x - 3) < internalPairCount G S₂ := by
    by_contra hnot
    have hpairle := not_lt.mp hnot
    omega
  obtain ⟨T, hTsub, hTne, hTslice⟩ :=
    exists_sparse_core_of_twice_excess_lt_pairs G h3 S₂ hlarge
  have hdisjT : Disjoint S₁ T := hdisj.mono_right hTsub
  have hncT : ∀ x ∈ S₁, ∀ y ∈ T, ¬G.Adj x y :=
    fun x hx y hy => hnc x hx y (hTsub hy)
  exact algConn_le_two_of_sparse_core_clusters G S₁ T hS1ne hTne hdisjT hncT
    hslice hTslice

end ACMax
