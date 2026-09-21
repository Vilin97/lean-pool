/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Cuts.GoodTriangle
import LeanPool.ACMax.Reduction.Reduction

/-!
# The degree-three core at orders eight and nine

At these two orders the global excess ledger leaves at least eight degree-three
vertices and at most one other vertex.  Hence every degree-three vertex has at
least two neighbors inside the degree-three core.  A triangle in the core is a
good-triangle certificate; if the core is triangle-free, the standard
small-degree lemma supplies an induced `2K₂`.
-/

namespace ACMax

open Classical in
/-- Every minimum-degree-three graph in the ACMAX family on eight or nine
vertices has algebraic connectivity at most two. -/
theorem small_degree_three_core_fires {n : ℕ} [Nonempty (Fin n)]
    (hn8 : 8 ≤ n) (hn9 : n ≤ 9)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  set D : Finset (Fin n) := Finset.univ.filter (fun v => G.degree v = 3) with hDdef
  have hDcard : 8 ≤ D.card := by
    rw [hDdef]
    exact card_deg3_ge_eight n hn8 G hm h3
  have hDcompl : Dᶜ.card ≤ 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hdegD : ∀ v ∈ D, G.degree v = 3 := by
    intro v hv
    simpa [hDdef] using hv
  have hmin : ∀ v ∈ D, 1 ≤ (G.neighborFinset v ∩ D).card := by
    intro v hv
    have hout : (G.neighborFinset v \ D).card ≤ 1 := by
      calc
        (G.neighborFinset v \ D).card ≤ Dᶜ.card := Finset.card_le_card (by
          intro w hw
          rw [Finset.mem_sdiff] at hw
          rw [Finset.mem_compl]
          exact hw.2)
        _ ≤ 1 := hDcompl
    have hpart : (G.neighborFinset v ∩ D).card +
        (G.neighborFinset v \ D).card = G.degree v := by
      rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
    have hd := hdegD v hv
    omega
  have hmax : ∀ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 3 := by
    intro v hv
    calc
      (G.neighborFinset v ∩ D).card ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := by rw [G.card_neighborFinset_eq_degree, hdegD v hv]
  by_cases htri : ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D,
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z
  · obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz⟩ := htri
    apply algConn_le_two_of_good_triangle (by omega) G x y z hxy hyz hxz
    rw [hdegD x hx, hdegD y hy, hdegD z hz]
    omega
  · have htriFree : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
        ¬(G.Adj x y ∧ G.Adj y z ∧ G.Adj x z) := by
      intro x hx y hy z hz hxyz
      exact htri ⟨x, hx, y, hy, z, hz, hxyz⟩
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hdist, hab, hcd,
        hac, had, hbc, hbd⟩ :=
      exists_induced_2K2_of_triangleFree_smalldeg G D htriFree hmin hmax hDcard
    exact algConn_le_two_of_ind_2K2 G a b c d hdist hab hcd hac had hbc hbd
      (by rw [hdegD a ha, hdegD b hb, hdegD c hc, hdegD d hd])

end ACMax
