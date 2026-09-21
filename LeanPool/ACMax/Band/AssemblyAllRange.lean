/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Band.CertAllRange
import LeanPool.ACMax.Band.KillSharp
import LeanPool.ACMax.Band.Rows
import LeanPool.ACMax.Counting.MEdgeSparse
import LeanPool.ACMax.Cuts.LowDegreeVertex
import LeanPool.ACMax.Spectral.AlgConnK2

/-!
# Exact Moore closure for every order at least 48

This assembly replaces the split between the finite exact-Moore range and the
polynomial large-order range by one exact non-backtracking certificate.
-/

namespace ACMax

open Finset

open Classical in
/-- A degree-`3`-separated obstruction cannot have order at least `48`. -/
theorem starved_dead_ge_48_exact {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hn48 : 48 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) : False := by
  have hh : (v9Set G)ᶜ.card ≤ excessX n G := heavy_card_le_excess G
  have hM : 10 * excessX n G + 7 * (v9Set G)ᶜ.card + 186 ≤ 4 * n := by
    have hmd := master_dprime G hn48 hm h3 hnf hs0
    omega
  have hpos : excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n :=
    t9_window G hn48 hm h3 hnf hs0
  have hv : (v9Set G).card = n - (v9Set G)ᶜ.card := by
    have := v9_card_add_compl G
    omega
  have hcert := band_cert_uniform_ge_48 n (excessX n G) ((v9Set G)ᶜ.card)
    hM hh hn48
  rw [← hv] at hcert
  exact starved_v9_kill_ahl_sum_sharp G hn48 hm h3 hnf hpos
    ((2 * n - excessX n G) / 12) (by omega) (by omega) hcert

open Classical in
/-- Every graph of order at least `48` with exactly `2(n-2)` edges has
algebraic connectivity at most `2`. -/
theorem upperBound_ge_48_exact {n : ℕ} [Nonempty (Fin n)]
    (hn48 : 48 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) : algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · obtain ⟨u, hdeg⟩ := hlow
    exact algConn_le_two_of_degree_le_two (by omega) G u hdeg
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by
      have := hlow v
      omega
    by_cases hMedge : ∃ v w : Fin n,
        G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_sparse_core_fires (by omega) G hm h3 u p hadj hu hp
    · have hs0 : ∀ v w : Fin n,
          G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      by_contra hnf
      exact starved_dead_ge_48_exact G hn48 hm h3 hnf hs0

open Classical in
/-- The ACMAX extremal statement for every order at least `48`. -/
theorem acmax_conjecture_ge_48_exact {n : ℕ} [Nonempty (Fin n)] (hn48 : 48 ≤ n) :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n),
        G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two n (by omega),
    fun G hm => upperBound_ge_48_exact hn48 G hm⟩

end ACMax
