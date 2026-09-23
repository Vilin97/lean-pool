/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.StarvedCensus

/-!
# Heavy-degree census lemmas

Two elementary set-counting facts used by the exact Moore argument on
`48 ≤ n ≤ 122`. They were first proved inside the former island-band
development; this neutral module keeps the active proof independent of that
historical assembly.
-/

@[expose] public section

namespace ACMax

open SimpleGraph Finset

open Classical in
/-- The total degree excess dominates the heavy vertices, with additional
weights for non-giant degree-`6` hubs and giant hubs. -/
theorem heavy_class_ledger {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 48 ≤ n) :
    (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card
      + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + 3 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ excessX n G := by
  classical
  have hE6 : ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)))
      = (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).filter
          (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    omega
  have hEg : ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h))
      = (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).filter
          (fun h => n + 15 < 9 * G.degree h) := by
    ext x
    simp only [Finset.mem_filter, mem_hubSet, Finset.mem_univ, true_and]
    omega
  rw [hE6, hEg, excessX, Finset.card_eq_sum_ones, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  split_ifs <;> omega

open Classical in
/-- The non-giant degree-`6` hubs and giant hubs are disjoint subsets of the
heavy vertices. -/
theorem heavy_class_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 48 ≤ n) :
    ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
  classical
  have hdisj : Disjoint
      ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h)))
      ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter] at hx hy
    exact hx.2.2 hy.2
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hx
  rcases hx with hx | hx
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, by omega⟩
  · rw [Finset.mem_filter]
    have hxhub := (mem_hubSet.mp hx.1)
    exact ⟨Finset.mem_univ x, by omega⟩

end ACMax
