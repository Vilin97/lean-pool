/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.ResidualInterface
public import LeanPool.ACMax.Counting.Moats
public import LeanPool.ACMax.Counting.XBoundAssembly

/-!
# Forcing a shared degree-three star

The incidence census below is independent of the finite-order case files.  In a graph
with minimum degree at least three and no edge joining two degree-three vertices, it
forces a degree-four vertex with at least two degree-three neighbors whenever the order
is at most `31`.
-/

public section

namespace ACMax

open Classical in
/-- On `8 <= n <= 31`, a graph in the starved census contains a degree-`4` vertex
with at least two degree-`3` neighbors. -/
theorem z1_forced_of_le_31 {n : ℕ} (hn8 : 8 ≤ n) (hn31 : n ≤ 31)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    ∃ h : Fin n, G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ deg3Set G).card := by
  classical
  by_contra hnZ1
  have cap4 : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ deg3Set G).card ≤ 1 := by
    intro h hd
    by_contra hlt
    exact hnZ1 ⟨h, hd, by omega⟩
  have hEq : deg3Set G = isoTwins G := deg3_eq_isoTwins_of_s0 G hs0
  have hsum : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card =
      3 * (deg3Set G).card := by
    have key := twin_incidence_total G h3
    rw [← hEq] at key
    refine Eq.trans ?_ key
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    ext x
    simp [Finset.mem_inter]
  set c : ℕ := (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card with hc
  have hfilt_eq : (hubSet G).filter (fun h => 5 ≤ G.degree h) =
      Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) := by
    ext v
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hptbound : ∀ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card ≤
      (G.degree h - 3) + 3 * (if 5 ≤ G.degree h then 1 else 0) := by
    intro h hh
    have hge4 : 4 ≤ G.degree h := mem_hubSet.mp hh
    have htle : (G.neighborFinset h ∩ deg3Set G).card ≤ G.degree h := by
      calc
        (G.neighborFinset h ∩ deg3Set G).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    by_cases hd4 : G.degree h = 4
    · rw [ite_eq_right (by omega)]
      have := cap4 h hd4
      omega
    · have hge5 : 5 ≤ G.degree h := by omega
      rw [ite_eq_left hge5]
      omega
  have hsum_le : ∑ h ∈ hubSet G, (G.neighborFinset h ∩ deg3Set G).card ≤
      ∑ h ∈ hubSet G, ((G.degree h - 3) + 3 * (if 5 ≤ G.degree h then 1 else 0)) :=
    Finset.sum_le_sum hptbound
  have hc_sum : ∑ h ∈ hubSet G, 3 * (if 5 ≤ G.degree h then 1 else 0) = 3 * c := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.card_filter, hfilt_eq]
  rw [Finset.sum_add_distrib, hc_sum] at hsum_le
  have hexcess_hub : ∑ h ∈ hubSet G, (G.degree h - 3) ≤ n - 8 := by
    have hfull : ∑ v : Fin n, (G.degree v - 3) = n - 8 :=
      total_excess_eq (by omega) G hm h3
    calc
      ∑ h ∈ hubSet G, (G.degree h - 3) ≤ ∑ v : Fin n, (G.degree v - 3) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n - 8 := hfull
  have hn3 : (deg3Set G).card = 8 + excessX n G :=
    deg3_card_eq_eight_add_excess n G (by omega) hm h3
  have hcX : c ≤ excessX n G := by
    rw [hc, excessX]
    calc
      (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card =
          ∑ _v ∈ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v),
          (G.degree v - 4) := by
        apply Finset.sum_le_sum
        intro v hv
        have := (Finset.mem_filter.mp hv).2
        omega
  omega

end ACMax
