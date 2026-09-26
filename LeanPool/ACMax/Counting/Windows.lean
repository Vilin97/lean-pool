/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Spectral.AlgConnK2
public import LeanPool.ACMax.Cuts.LowDegreeVertex
public import LeanPool.ACMax.Counting.ResidualInterface
public import LeanPool.ACMax.Counting.XBoundAssembly
public import LeanPool.ACMax.Counting.StarvedCensus
public import LeanPool.ACMax.Counting.MEdgeSparse
public import LeanPool.ACMax.Counting.SmallDegreeThreeCore
public import LeanPool.ACMax.Counting.StarMoatSharp
public import LeanPool.ACMax.Counting.StarForcing

/-!
# Orders below fifty

One continuous structural argument handles orders through `31`, and the
owner-slot census handles `32 ≤ n ≤ 49`.

## Main results

* `z1_fires_sharp`, `z1_forced_of_le_31` — the `Z1` star-moat (a degree-4 hub
  with two degree-3 neighbors) and its forcing count on `8 ≤ n ≤ 31`.
* `upperBound_moat` — the upper bound on the complete window `4 ≤ n ≤ 31`,
  including the low-order degree-three core and the sparse-core endpoints.
* `starved_band_kill_32_49`, `acmax_conjecture_range_49` — the widened starved
  band and the continuous verdict on `4 ≤ n ≤ 49`.
-/

/-! ## The window-34 discharge

For a graph of minimum degree three, split on the presence of an `M`-edge:
present ⟹ the sparse-core moat fires; absent ⟹ the shared-hub stars are forced. On
`10 ≤ n ≤ 31` the E1 count `z1_forced_of_le_31` forces `Z1` with no heavy
hypothesis (negating `Z1` starves the degree-4 hubs and the incidence total forces
`n ≥ 32`). The same star moat fires throughout this range by `z1_fires_sharp`. -/

public section

namespace ACMax

open Classical in
/-- **`Z1` fires via a sparse bulk core.**  A degree-`4` hub owning at least two
degree-`3` neighbors closes the graph at every `n ≥ 10`. -/
theorem z1_fires_sharp {n : ℕ} [Nonempty (Fin n)] (hn : 10 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hZ1 : ∃ h : Fin n, G.degree h = 4 ∧ 2 ≤ (G.neighborFinset h ∩ deg3Set G).card) :
    algConn G ≤ 2 := by
  obtain ⟨h, hdh, htw⟩ := hZ1
  obtain ⟨t₁, t₂, ht1mem, ht2mem, ht12⟩ :=
    Finset.one_lt_card_iff.mp (by omega : 1 < (G.neighborFinset h ∩ deg3Set G).card)
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_deg3Set] at ht1mem ht2mem
  exact z1_star_moat_fires_core hn G hm h3 hs0 h t₁ t₂ hdh
    ht1mem.1 ht2mem.1 ht1mem.2 ht2mem.2 ht12

/-! ## The finite window `4 ≤ n ≤ 31`

Closes the complete finite window `4 ≤ n ≤ 31`. The low-degree test vector handles
all orders below eight. At orders eight and nine, the degree-three core supplies a
triangle or an induced `2K₂`. From order ten onward, an `M`-edge fires via
`medge_sparse_core_fires`; with no `M`-edge, the `Z1`-only forcing count
`z1_forced_of_le_31` is killed by `z1_fires_sharp`. The
`λ₂(K_{2,n-2}) = 2` half reuses `algConn_completeBipartite_two`. -/

open Classical in
/-- **The finite-window upper bound on `4 ≤ n ≤ 31`.** Every `G` on `Fin n` with
`2(n−2)` edges has `algConn G ≤ 2`. -/
theorem upperBound_moat {n : ℕ} [Nonempty (Fin n)] (hn4 : 4 ≤ n) (hn31 : n ≤ 31)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 := by
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · obtain ⟨u, hdeg⟩ := hlow
    exact algConn_le_two_of_degree_le_two hn4 G u hdeg
  · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
      rw [G.sum_degrees_eq_twice_card_edges, hm]
    have hbase : 3 * n ≤ ∑ v : Fin n, G.degree v := by
      calc
        3 * n = ∑ _v : Fin n, (3 : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            Nat.mul_comm]
        _ ≤ ∑ v : Fin n, G.degree v := Finset.sum_le_sum (fun v _ => h3 v)
    have hn8 : 8 ≤ n := by omega
    by_cases hn9 : n ≤ 9
    · exact small_degree_three_core_fires hn8 hn9 G hm h3
    have hn10 : 10 ≤ n := by omega
    by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
    · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
      exact medge_sparse_core_fires hn10 G hm h3 u p hadj hu hp
    · have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
        s0_of_no_medge G hMedge
      exact z1_fires_sharp (by omega) G hm h3 hs0
        (z1_forced_of_le_31 hn8 hn31 G hm h3 hs0)

end ACMax

/-! ## The continuous range `4 ≤ n ≤ 49`

Assembles the moat window `upperBound_moat` with the starved band
`32 ≤ n ≤ 49` into a single verdict. The starved band kill is widened from
`35 ≤ n ≤ 49` to `32 ≤ n ≤ 49` — every owner-choke ingredient is `n`-generic well
below 35, and the closing `interval_cases` count still closes at `n ∈ {32,33,34}`
(where the hoarding and giant-census rows force `n_g = X = 0` and the choke caps
`7·t₄ < 7·24`), giving `starved_band_kill_32_49`. The verdict
`acmax_conjecture_range_49` dispatches on `δ ≤ 2` / `M`-edge / starved band. -/

namespace ACMax

open Finset

open Classical in
/-- **The starved owner-choke, widened to `32 ≤ n ≤ 49`.**  Identical to
`starved_owner_choke_35_49` but with the closing `interval_cases n <;> omega` run over the wider
window; the extra rows `n ∈ {32, 33, 34}` close because hoarding forces `X ≤ n_g`, the giant
census forces `(n − 20)·n_g ≤ 9X`, together pinning `n_g = X = 0`, which collides the slots row
(`t₄ ≥ 24`) with the choke (`7·t₄ ≤ 4n − 32`). -/
theorem starved_owner_choke_32_49 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn32 : 32 ≤ n) (hn49 : n ≤ 49)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w)
    (hchoke : 7 * (∑ h ∈ (hubSet G).filter (fun h => G.degree h = 4),
                (G.neighborFinset h ∩ isoTwins G).card)
              + 3 * excessX n G + 32 ≤ 4 * n) :
    algConn G ≤ 2 := by
  by_contra hnf
  have hsl := slots_law G (by omega) hm h3 hnf hs0
  have hho := hoarding_law G (by omega) hm h3 hnf hs0
  have hgi := giant_excess_bound G (by omega)
  have hhX := heavy_le_excess G
  interval_cases n <;> omega

open Classical in
/-- **The starved band kill, widened to `32 ≤ n ≤ 49`.**  Identical to `starved_band_kill_35_49`
but routed through `starved_owner_choke_32_49`; a never-firing starved census on `32 ≤ n ≤ 49`
cannot exist, so the graph fires: `algConn G ≤ 2`. -/
theorem starved_band_kill_32_49 {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hn32 : 32 ≤ n) (hn49 : n ≤ 49)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    algConn G ≤ 2 := by
  by_contra hnf
  have hcap : ∀ h : Fin n, G.degree h = 4 → (G.neighborFinset h ∩ isoTwins G).card ≤ 1 := by
    intro h hh
    have hc := starved_cap G hm h3 hnf h (by rw [hh]; omega)
    rw [hh] at hc
    omega
  have hindep : ∀ o₁ o₂ : Fin n, G.degree o₁ = 4 → G.degree o₂ = 4 →
      (G.neighborFinset o₁ ∩ isoTwins G).Nonempty →
      (G.neighborFinset o₂ ∩ isoTwins G).Nonempty → o₁ ≠ o₂ → ¬ G.Adj o₁ o₂ := by
    intro o₁ o₂ ho1 ho2 hn1 hn2 _hne
    obtain ⟨t₁, ht1⟩ := hn1
    obtain ⟨t₂, ht2⟩ := hn2
    rw [Finset.mem_inter, G.mem_neighborFinset] at ht1 ht2
    exact owner_independence (by omega) G hm h3 hnf o₁ o₂ t₁ t₂ ho1 ho2 ht1.1
      (mem_isoTwins.mp ht1.2).1 ht2.1 (mem_isoTwins.mp ht2.2).1
  exact absurd (starved_owner_choke_32_49 G hn32 hn49 hm h3 hs0
    (choke_count (by omega) G hm h3 hs0 hcap hindep)) hnf

open Classical in
/-- **The moat/choke upper bound on the continuous range `4 ≤ n ≤ 49`.**  Every `G` on `Fin n`
with `2(n−2)` edges has `algConn G ≤ 2`: below `32` this is `upperBound_moat`; on `32 ≤ n ≤ 49`
the graph is dispatched by minimum degree — low-degree test vector, sparse-core
certificate, or the widened starved band kill. -/
theorem upperBound_range_49 {n : ℕ} [Nonempty (Fin n)] (hn4 : 4 ≤ n) (hn49 : n ≤ 49)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 := by
  by_cases hle31 : n ≤ 31
  · exact upperBound_moat hn4 hle31 G hm
  · have hn32 : 32 ≤ n := by omega
    rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
    · obtain ⟨u, hdeg⟩ := hlow
      exact algConn_le_two_of_degree_le_two hn4 G u hdeg
    · let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
      simp only [not_exists, not_le] at hlow
      have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
      by_cases hMedge : ∃ v w : Fin n, G.degree v = 3 ∧ G.degree w = 3 ∧ G.Adj v w
      · obtain ⟨u, p, hu, hp, hadj⟩ := hMedge
        exact medge_sparse_core_fires (by omega) G hm h3 u p hadj hu hp
      · have hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w :=
          s0_of_no_medge G hMedge
        exact starved_band_kill_32_49 G hn32 hn49 hm h3 hs0

open Classical in
/-- **The ACMAX conjecture on the continuous range `4 ≤ n ≤ 49`.**  `K_{2,n-2}` is the maximizer
(`λ₂ = 2`) and every `G` with `2(n−2)` edges has `algConn G ≤ 2`. -/
theorem acmax_conjecture_range_49 {n : ℕ} [Nonempty (Fin n)]
    (hn4 : 4 ≤ n) (hn49 : n ≤ 49) :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two n hn4, fun G hm => upperBound_range_49 hn4 hn49 G hm⟩

end ACMax
