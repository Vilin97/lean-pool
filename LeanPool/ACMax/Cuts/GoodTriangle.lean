/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Cuts.WeightedCut

/-!
# The good-triangle certificate

A triangle sends `deg x + deg y + deg z - 6` edges to its complement.  The
usual weighted cut vector therefore certifies algebraic connectivity at most
two whenever that boundary satisfies the corresponding cut inequality.
-/

public section

namespace ACMax

open Classical in
/-- A triangle satisfying the exact weighted-cut arithmetic forces
`algConn G ≤ 2`. -/
theorem algConn_le_two_of_good_triangle {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) (x y z : Fin n)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (hcut : n * (G.degree x + G.degree y + G.degree z - 6) ≤
      2 * (3 * (n - 3))) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  set S : Finset (Fin n) := {x, y, z} with hSdef
  have hxyne : x ≠ y := G.ne_of_adj hxy
  have hyzne : y ≠ z := G.ne_of_adj hyz
  have hxzne : x ≠ z := G.ne_of_adj hxz
  have hScard : S.card = 3 := by simp [hSdef, hxyne, hyzne, hxzne]
  have hScompl : Sᶜ.card = n - 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hScard]
  have hSne : S.Nonempty := ⟨x, by rw [hSdef]; simp⟩
  have hScne : Sᶜ.Nonempty := by
    rw [← Finset.card_pos, hScompl]
    omega
  have hxout : (G.neighborFinset x \ S).card + 2 ≤ G.degree x := by
    have hsub : ({y, z} : Finset (Fin n)) ⊆ G.neighborFinset x ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwy | hwz
      · subst w
        exact ⟨(G.mem_neighborFinset x y).mpr hxy, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset x z).mpr hxz, by rw [hSdef]; simp⟩
    have hpart : (G.neighborFinset x ∩ S).card +
        (G.neighborFinset x \ S).card = G.degree x := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have htwo : 2 ≤ (G.neighborFinset x ∩ S).card := by
      rw [← Finset.card_pair hyzne]
      exact Finset.card_le_card hsub
    omega
  have hyout : (G.neighborFinset y \ S).card + 2 ≤ G.degree y := by
    have hsub : ({x, z} : Finset (Fin n)) ⊆ G.neighborFinset y ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwx | hwz
      · subst w
        exact ⟨(G.mem_neighborFinset y x).mpr hxy.symm, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset y z).mpr hyz, by rw [hSdef]; simp⟩
    have hpart : (G.neighborFinset y ∩ S).card +
        (G.neighborFinset y \ S).card = G.degree y := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have htwo : 2 ≤ (G.neighborFinset y ∩ S).card := by
      rw [← Finset.card_pair hxzne]
      exact Finset.card_le_card hsub
    omega
  have hzout : (G.neighborFinset z \ S).card + 2 ≤ G.degree z := by
    have hsub : ({x, y} : Finset (Fin n)) ⊆ G.neighborFinset z ∩ S := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter]
      rcases hw with hwx | hwy
      · subst w
        exact ⟨(G.mem_neighborFinset z x).mpr hxz.symm, by rw [hSdef]; simp⟩
      · subst w
        exact ⟨(G.mem_neighborFinset z y).mpr hyz.symm, by rw [hSdef]; simp⟩
    have hpart : (G.neighborFinset z ∩ S).card +
        (G.neighborFinset z \ S).card = G.degree z := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have htwo : 2 ≤ (G.neighborFinset z ∩ S).card := by
      rw [← Finset.card_pair hxyne]
      exact Finset.card_le_card hsub
    omega
  have hsum : ∑ v ∈ S, (G.neighborFinset v \ S).card ≤
      G.degree x + G.degree y + G.degree z - 6 := by
    rw [hSdef] at hxout hyout hzout
    rw [hSdef, Finset.sum_insert (by simp [hxyne, hxzne]),
      Finset.sum_insert (by simp [hyzne]), Finset.sum_singleton]
    omega
  refine algConn_le_two_of_weighted_cut G S hSne hScne ?_
  rw [Fintype.card_fin, hScard, hScompl]
  exact (Nat.mul_le_mul_left n hsum).trans hcut

end ACMax
