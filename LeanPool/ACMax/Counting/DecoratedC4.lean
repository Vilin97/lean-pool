/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.NormNum
public import LeanPool.ACMax.Counting.SparseCore

/-!
# Decorated four-cycle cuts at order fifteen

Two compact sparse-cut certificates used by the endpoint shared-star census.
The four-cycle itself misses the order-15 cut inequality by one edge; adjoining
one parent, or two adjacent parents, supplies exactly the missing slack.
-/

public section

namespace ACMax

open Finset

noncomputable section

/-- Use the same finite-set decisions as the classical graph certificates. -/
local instance decoratedCycleFinDecidableEq {n : ℕ} : DecidableEq (Fin n) := Classical.decEq _

open Classical in
private theorem outside_le_of_internal {n : ℕ} (G : SimpleGraph (Fin n))
    (S K : Finset (Fin n)) (v : Fin n) (hK : K ⊆ G.neighborFinset v ∩ S)
    (hKcard : K.card = 2) (hdeg : G.degree v ≤ 3) :
    (G.neighborFinset v \ S).card ≤ 1 := by
  have h := neighbor_sdiff_card_add_le_degree G S K v hK
  omega

open Classical in
private theorem outside_le_one_of_three_internal {n : ℕ} (G : SimpleGraph (Fin n))
    (S K : Finset (Fin n)) (v : Fin n) (hK : K ⊆ G.neighborFinset v ∩ S)
    (hKcard : K.card = 3) (hdeg : G.degree v ≤ 4) :
    (G.neighborFinset v \ S).card ≤ 1 := by
  have h := neighbor_sdiff_card_add_le_degree G S K v hK
  omega

open Classical in
private theorem outside_le_two_of_two_internal {n : ℕ} (G : SimpleGraph (Fin n))
    (S K : Finset (Fin n)) (v : Fin n) (hK : K ⊆ G.neighborFinset v ∩ S)
    (hKcard : K.card = 2) (hdeg : G.degree v ≤ 4) :
    (G.neighborFinset v \ S).card ≤ 2 := by
  have h := neighbor_sdiff_card_add_le_degree G S K v hK
  omega

open Classical in
/-- A `K_{2,2}` whose degree-at-most-four vertices share a degree-at-most-four
parent gives a five-vertex order-15 sparse cut. -/
theorem decorated_c4_same_parent_fires (G : SimpleGraph (Fin 15))
    (p x y b₁ b₂ : Fin 15)
    (hS : ({p, x, y, b₁, b₂} : Finset (Fin 15)).card = 5)
    (hxy : ({x, y} : Finset (Fin 15)).card = 2)
    (hpbb : ({p, b₁, b₂} : Finset (Fin 15)).card = 3)
    (hdp : G.degree p ≤ 4) (hdx : G.degree x ≤ 4) (hdy : G.degree y ≤ 4)
    (hdb1 : G.degree b₁ ≤ 3) (hdb2 : G.degree b₂ ≤ 3)
    (hpx : G.Adj p x) (hpy : G.Adj p y)
    (hxb1 : G.Adj x b₁) (hxb2 : G.Adj x b₂)
    (hyb1 : G.Adj y b₁) (hyb2 : G.Adj y b₂) :
    algConn G ≤ 2 := by
  classical
  set S : Finset (Fin 15) := {p, x, y, b₁, b₂} with hSdef
  have hpout : (G.neighborFinset p \ S).card ≤ 2 := by
    apply outside_le_two_of_two_internal G S {x, y} p _ hxy hdp
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hpx, Or.inr (Or.inl rfl)⟩
    · exact ⟨hpy, Or.inr (Or.inr (Or.inl rfl))⟩
  have hxout : (G.neighborFinset x \ S).card ≤ 1 := by
    apply outside_le_one_of_three_internal G S {p, b₁, b₂} x _ hpbb hdx
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl | rfl
    · exact ⟨hpx.symm, Or.inl rfl⟩
    · exact ⟨hxb1, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨hxb2, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  have hyout : (G.neighborFinset y \ S).card ≤ 1 := by
    apply outside_le_one_of_three_internal G S {p, b₁, b₂} y _ hpbb hdy
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl | rfl
    · exact ⟨hpy.symm, Or.inl rfl⟩
    · exact ⟨hyb1, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨hyb2, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  have hb1out : (G.neighborFinset b₁ \ S).card ≤ 1 := by
    apply outside_le_of_internal G S {x, y} b₁ _ hxy hdb1
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hxb1.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hyb1.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  have hb2out : (G.neighborFinset b₂ \ S).card ≤ 1 := by
    apply outside_le_of_internal G S {x, y} b₂ _ hxy hdb2
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hxb2.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hyb2.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  refine algConn_le_two_of_order15_cluster G S p (by simp [S]) (Or.inl ?_) hpout ?_
  · simpa [S] using hS
  · intro v hv hvp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact (hvp rfl).elim
    · exact hxout
    · exact hyout
    · exact hb1out
    · exact hb2out

open Classical in
/-- A `K_{2,2}` whose two degree-at-most-four vertices have adjacent parents
of degrees at most four and three gives a six-vertex order-15 sparse cut. -/
theorem decorated_c4_adjacent_parents_fires (G : SimpleGraph (Fin 15))
    (p q x y b₁ b₂ : Fin 15)
    (hS : ({p, q, x, y, b₁, b₂} : Finset (Fin 15)).card = 6)
    (hqx : ({q, x} : Finset (Fin 15)).card = 2)
    (hpy : ({p, y} : Finset (Fin 15)).card = 2)
    (hpbb : ({p, b₁, b₂} : Finset (Fin 15)).card = 3)
    (hqbb : ({q, b₁, b₂} : Finset (Fin 15)).card = 3)
    (hxy : ({x, y} : Finset (Fin 15)).card = 2)
    (hdp : G.degree p ≤ 4) (hdq : G.degree q ≤ 3)
    (hdx : G.degree x ≤ 4) (hdy : G.degree y ≤ 4)
    (hdb1 : G.degree b₁ ≤ 3) (hdb2 : G.degree b₂ ≤ 3)
    (hpq : G.Adj p q) (hpx : G.Adj p x) (hqy : G.Adj q y)
    (hxb1 : G.Adj x b₁) (hxb2 : G.Adj x b₂)
    (hyb1 : G.Adj y b₁) (hyb2 : G.Adj y b₂) :
    algConn G ≤ 2 := by
  classical
  set S : Finset (Fin 15) := {p, q, x, y, b₁, b₂} with hSdef
  have hpout : (G.neighborFinset p \ S).card ≤ 2 := by
    apply outside_le_two_of_two_internal G S {q, x} p _ hqx hdp
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hpq, Or.inr (Or.inl rfl)⟩
    · exact ⟨hpx, Or.inr (Or.inr (Or.inl rfl))⟩
  have hqout : (G.neighborFinset q \ S).card ≤ 1 := by
    apply outside_le_of_internal G S {p, y} q _ hpy hdq
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hpq.symm, Or.inl rfl⟩
    · exact ⟨hqy, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  have hxout : (G.neighborFinset x \ S).card ≤ 1 := by
    apply outside_le_one_of_three_internal G S {p, b₁, b₂} x _ hpbb hdx
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl | rfl
    · exact ⟨hpx.symm, Or.inl rfl⟩
    · exact ⟨hxb1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact ⟨hxb2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  have hyout : (G.neighborFinset y \ S).card ≤ 1 := by
    apply outside_le_one_of_three_internal G S {q, b₁, b₂} y _ hqbb hdy
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl | rfl
    · exact ⟨hqy.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hyb1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · exact ⟨hyb2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  have hb1out : (G.neighborFinset b₁ \ S).card ≤ 1 := by
    apply outside_le_of_internal G S {x, y} b₁ _ hxy hdb1
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hxb1.symm, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨hyb1.symm,
        Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  have hb2out : (G.neighborFinset b₂ \ S).card ≤ 1 := by
    apply outside_le_of_internal G S {x, y} b₂ _ hxy hdb2
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, S,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl
    · exact ⟨hxb2.symm, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨hyb2.symm,
        Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  refine algConn_le_two_of_order15_cluster G S p (by simp [S]) (Or.inr ?_) hpout ?_
  · simpa [S] using hS
  · intro v hv hvp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hvp rfl).elim
    · exact hqout
    · exact hxout
    · exact hyout
    · exact hb1out
    · exact hb2out

open Classical in
/-- At order fourteen, a triangle whose degree sum is at most ten is a
weighted-cut certificate. -/
theorem order14_sparse_triangle_fires (G : SimpleGraph (Fin 14))
    (x y z : Fin 14) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (hdeg : G.degree x + G.degree y + G.degree z ≤ 10) :
    algConn G ≤ 2 := by
  classical
  set S : Finset (Fin 14) := {x, y, z} with hSdef
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hyzne : y ≠ z := G.ne_of_adj hyz
  have hxzne : x ≠ z := G.ne_of_adj hxz
  have hScard : S.card = 3 := by simp [hSdef, hxyne, hyzne, hxzne]
  have hxout : (G.neighborFinset x \ S).card + 2 ≤ G.degree x := by
    have hsub : ({y, z} : Finset (Fin 14)) ⊆ G.neighborFinset x ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwy | hwz
      · subst w
        exact ⟨(G.mem_neighborFinset x y).mpr hxy, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset x z).mpr hxz, by rw [hSdef]; simp⟩
    have hout := neighbor_sdiff_card_add_le_degree G S {y, z} x hsub
    rw [Finset.card_pair hyzne] at hout
    exact hout
  have hyout : (G.neighborFinset y \ S).card + 2 ≤ G.degree y := by
    have hsub : ({x, z} : Finset (Fin 14)) ⊆ G.neighborFinset y ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwx | hwz
      · subst w
        exact ⟨(G.mem_neighborFinset y x).mpr hxy.symm, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset y z).mpr hyz, by rw [hSdef]; simp⟩
    have hout := neighbor_sdiff_card_add_le_degree G S {x, z} y hsub
    rw [Finset.card_pair hxzne] at hout
    exact hout
  have hzout : (G.neighborFinset z \ S).card + 2 ≤ G.degree z := by
    have hsub : ({x, y} : Finset (Fin 14)) ⊆ G.neighborFinset z ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwx | hwy
      · subst w
        exact ⟨(G.mem_neighborFinset z x).mpr hxz.symm, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset z y).mpr hyz.symm, by rw [hSdef]; simp⟩
    have hout := neighbor_sdiff_card_add_le_degree G S {x, y} z hsub
    rw [Finset.card_pair hxyne] at hout
    exact hout
  have hsum : ∑ v ∈ S, (G.neighborFinset v \ S).card ≤ 4 := by
    rw [hSdef] at hxout hyout hzout ⊢
    rw [Finset.sum_insert (by simp [hxyne, hxzne]),
      Finset.sum_insert (by simp [hyzne]), Finset.sum_singleton]
    omega
  have hSc : Sᶜ.card = 11 := by
    rw [Finset.card_compl, hScard, Fintype.card_fin]
  have hScne : Sᶜ.Nonempty := Finset.card_pos.mp (by rw [hSc]; norm_num)
  refine algConn_le_two_of_weighted_cut G S ⟨x, by rw [hSdef]; simp⟩ hScne ?_
  rw [hScard, hSc, Fintype.card_fin]
  omega

end

end ACMax
