/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.CompactLedgers
public import LeanPool.ACMax.Counting.SigmaCloud
public import LeanPool.ACMax.Counting.CompactCell
public import LeanPool.ACMax.Counting.DoubleStar

/-!
# The master X-bound assembly

Combines the D1 suppressed-mass bound `suppressed_card_le` with the degree
handshake to bound the total excess `X = excessX n G` on the `SeaFatBoundary`
linearly in the number of *usable* (unsuppressed, `sigS ≤ 2`) degree-3 vertices.

1. `deg3_card_eq_eight_add_excess` — handshake: `|D₃| = 8 + X`.
2. `deg3_usable_suppressed_split` — `|D₃| = m + s` (usable + suppressed).
3. `sfb_excess_bound_beta` — the sharpened excess bound on the boundary (`n ≥ 512`),
   dispatched through the slope-`11/2` light-anchor cover
   (`compact_covering_eleven_halves`).
-/

@[expose] public section

namespace ACMax

open Finset

open Classical in
/-- **Handshake**: with `2(n−2)` edges and minimum degree 3, the degree-3 set has
exactly `8 + X` members, where `X = excessX n G` is the total degree excess. -/
theorem deg3_card_eq_eight_add_excess (n : ℕ) (G : SimpleGraph (Fin n))
    (hn : 2 ≤ n) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v, 3 ≤ G.degree v) :
    (deg3Set G).card = 8 + excessX n G := by
  classical
  -- handshake: `∑ deg + 8 = 4n`
  have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hsum8 : ∑ v : Fin n, G.degree v + 8 = 4 * n := by omega
  set D3 := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD3
  set D4 := Finset.univ.filter (fun v : Fin n => G.degree v = 4) with hD4
  set D5 := Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) with hD5
  -- the three degree classes partition the vertex set
  have hcard : D3.card + D4.card + D5.card = n := by
    have hpt : ∀ v : Fin n,
        (if G.degree v = 3 then 1 else 0) + (if G.degree v = 4 then 1 else 0)
          + (if 5 ≤ G.degree v then 1 else 0) = 1 := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc D3.card + D4.card + D5.card
        = ∑ v : Fin n, ((if G.degree v = 3 then 1 else 0)
            + (if G.degree v = 4 then 1 else 0)
            + (if 5 ≤ G.degree v then 1 else 0)) := by
          simp only [hD3, hD4, hD5, Finset.card_filter, ← Finset.sum_add_distrib]
      _ = ∑ _v : Fin n, 1 := Finset.sum_congr rfl (fun v _ => hpt v)
      _ = n := by simp
  -- the degree sum splits along the partition
  have hdegsum : ∑ v : Fin n, G.degree v
      = 3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
    have hpt : ∀ v : Fin n, G.degree v
        = 3 * (if G.degree v = 3 then 1 else 0) + 4 * (if G.degree v = 4 then 1 else 0)
          + (if 5 ≤ G.degree v then G.degree v else 0) := by
      intro v
      have := h3 v
      split_ifs <;> omega
    calc ∑ v : Fin n, G.degree v
        = ∑ v : Fin n, (3 * (if G.degree v = 3 then 1 else 0)
            + 4 * (if G.degree v = 4 then 1 else 0)
            + (if 5 ≤ G.degree v then G.degree v else 0)) :=
          Finset.sum_congr rfl (fun v _ => hpt v)
      _ = 3 * D3.card + 4 * D4.card + ∑ v ∈ D5, G.degree v := by
          simp only [hD3, hD4, hD5, Finset.card_filter, Finset.sum_filter,
            Finset.mul_sum, mul_ite, mul_one, mul_zero, ← Finset.sum_add_distrib]
  -- the heavy degree sum is the excess plus `4·|D₅|`
  have hex : excessX n G + 4 * D5.card = ∑ v ∈ D5, G.degree v := by
    have h4 : ∀ v ∈ D5, G.degree v - 4 + 4 = G.degree v := by
      intro v hv
      have : 5 ≤ G.degree v := (Finset.mem_filter.mp hv).2
      omega
    calc excessX n G + 4 * D5.card
        = ∑ v ∈ D5, (G.degree v - 4) + ∑ _v ∈ D5, 4 := by
          rw [excessX, ← hD5, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ v ∈ D5, (G.degree v - 4 + 4) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ D5, G.degree v := Finset.sum_congr rfl h4
  have hd3 : (deg3Set G).card = D3.card := by rw [deg3Set, ← hD3]
  omega

open Classical in
/-- **Partition of the degree-3 set** into usable (`sigS ≤ 2`) and suppressed
(`2 < sigS`) vertices. -/
theorem deg3_usable_suppressed_split (n : ℕ) (G : SimpleGraph (Fin n)) :
    (deg3Set G).card
      = (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card
        + (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v)).card := by
  classical
  have h : (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card
      + (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ ¬sigS G v ≤ 2)).card
      = (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not (fun v => sigS G v ≤ 2)
  simp only [not_le] at h
  rw [deg3Set]
  exact h.symm

open Classical in
/-- **The all-usable-heavy corner count**: if no light usable vertex exists,
every degree-3 vertex is suppressed (needing `≥ 2` heavy neighbours) and every
degree-4 vertex is suppressed (needing `≥ 1`), so heavy-slot counting alone
gives `2n₃ + n₄ ≤ X + 4|H|` and hence

  `n + 8 ≤ 5·X`

— no ball or covering required. -/
theorem all_heavy_corner_count (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G)
    (hnolight : ∀ u : Fin n, sigS G u ≤ 2 → 5 ≤ G.degree u) :
    n + 8 ≤ 5 * excessX n G := by
  classical
  have h3 := h.min_degree
  set D₃ := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD₃
  set D₄ := Finset.univ.filter (fun v : Fin n => G.degree v = 4) with hD₄
  set H := Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) with hH
  -- the three classes partition the vertex set
  have hpart : D₃.card + D₄.card + H.card = n := by
    have h1 : (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card
        + (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).card
        = (Finset.univ : Finset (Fin n)).card :=
      Finset.card_filter_add_card_filter_not _
    have h2 : ((Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).filter
          (fun v => G.degree v = 4)).card
        + ((Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).filter
          (fun v => ¬G.degree v = 4)).card
        = (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).card :=
      Finset.card_filter_add_card_filter_not _
    have h4eq : (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).filter
        (fun v => G.degree v = 4) = D₄ := by
      rw [hD₄, Finset.filter_filter]
      apply Finset.filter_congr
      intro v _
      constructor
      · rintro ⟨-, h4⟩
        exact h4
      · intro h4
        exact ⟨by omega, h4⟩
    have h5eq : (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).filter
        (fun v => ¬G.degree v = 4) = H := by
      rw [hH, Finset.filter_filter]
      apply Finset.filter_congr
      intro v _
      have := h3 v
      constructor
      · rintro ⟨hn3, hn4⟩
        omega
      · intro h5
        omega
    rw [h4eq, h5eq] at h2
    rw [Finset.card_univ, Fintype.card_fin, ← hD₃] at h1
    omega
  -- degree-3 count from the handshake
  have hd3 : D₃.card = 8 + excessX n G := by
    rw [hD₃]
    exact deg3_card_eq_eight_add_excess n G (by omega) h.edge_card h3
  -- heavy slots
  have hslots : ∑ w ∈ H, G.degree w = excessX n G + 4 * H.card := by
    rw [hH, excessX]
    have hpt : ∀ v ∈ Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v),
        G.degree v = (G.degree v - 4) + 4 := by
      intro v hv
      have := (Finset.mem_filter.mp hv).2
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm]
  -- suppressed degree-3s consume two heavy slots each
  have hinc3 : 2 * D₃.card ≤ ∑ t ∈ D₃, (G.neighborFinset t ∩ H).card := by
    calc 2 * D₃.card = ∑ _t ∈ D₃, 2 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ t ∈ D₃, (G.neighborFinset t ∩ H).card := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht3 : G.degree t = 3 := by
            rw [hD₃] at ht
            exact (Finset.mem_filter.mp ht).2
          have hsup : 2 < sigS G t := by
            by_contra hcon
            have := hnolight t (le_of_not_gt hcon)
            omega
          obtain ⟨-, -, htwo⟩ := nonusable_deg3_structure G t ht3 h3 hsup
          calc 2 ≤ ((G.neighborFinset t).filter
                (fun w => 5 ≤ G.degree w)).card := htwo
            _ = (G.neighborFinset t ∩ H).card := by
                have heq : (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w)
                    = G.neighborFinset t ∩ H := by
                  rw [hH]
                  ext w
                  simp only [Finset.mem_filter, Finset.mem_inter,
                    Finset.mem_univ, true_and]
                rw [heq]
  -- suppressed degree-4s consume one heavy slot each
  have hinc4 : D₄.card ≤ ∑ v ∈ D₄, (G.neighborFinset v ∩ H).card := by
    calc D₄.card = ∑ _v ∈ D₄, 1 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
      _ ≤ ∑ v ∈ D₄, (G.neighborFinset v ∩ H).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hv4 : G.degree v = 4 := by
            rw [hD₄] at hv
            exact (Finset.mem_filter.mp hv).2
          have hsup : 2 < sigS G v := by
            by_contra hcon
            have := hnolight v (le_of_not_gt hcon)
            omega
          by_contra hzero
          have hempty : G.neighborFinset v ∩ H = ∅ := by
            rw [← Finset.card_eq_zero]
            omega
          -- all neighbours light ⟹ `sigS ≤ 2`, contradiction
          have hle : sigS G v ≤ 2 := by
            rw [sigS]
            calc ∑ w ∈ G.neighborFinset v, sigma (G.degree w)
                ≤ ∑ _w ∈ G.neighborFinset v, (1 / 2 : ℝ) := by
                  refine Finset.sum_le_sum fun w hw => ?_
                  have hw4 : G.degree w ≤ 4 := by
                    by_contra hcon
                    have : w ∈ G.neighborFinset v ∩ H := by
                      rw [Finset.mem_inter, hH, Finset.mem_filter]
                      exact ⟨hw, Finset.mem_univ w, by omega⟩
                    rw [hempty] at this
                    exact absurd this (Finset.notMem_empty w)
                  have := sigma_mono (h3 w) hw4
                  rw [sigma_four] at this
                  linarith
              _ = ((G.neighborFinset v).card : ℝ) * (1 / 2) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ 2 := by
                  rw [G.card_neighborFinset_eq_degree, hv4]
                  norm_num
          linarith
  -- the double count: light-to-heavy incidences fit in the heavy slots
  have hdouble : ∑ t ∈ D₃, (G.neighborFinset t ∩ H).card
      + ∑ v ∈ D₄, (G.neighborFinset v ∩ H).card
      ≤ ∑ w ∈ H, G.degree w := by
    rw [sum_nbr_inter_comm G D₃ H, sum_nbr_inter_comm G D₄ H]
    have hdisj : Disjoint D₃ D₄ := by
      rw [Finset.disjoint_left]
      intro v hv3 hv4
      rw [hD₃, Finset.mem_filter] at hv3
      rw [hD₄, Finset.mem_filter] at hv4
      omega
    calc ∑ w ∈ H, (G.neighborFinset w ∩ D₃).card
        + ∑ w ∈ H, (G.neighborFinset w ∩ D₄).card
        = ∑ w ∈ H, ((G.neighborFinset w ∩ D₃).card
            + (G.neighborFinset w ∩ D₄).card) :=
          (Finset.sum_add_distrib).symm
      _ ≤ ∑ w ∈ H, G.degree w := by
          refine Finset.sum_le_sum fun w _ => ?_
          have hcup : (G.neighborFinset w ∩ D₃).card
              + (G.neighborFinset w ∩ D₄).card
              = ((G.neighborFinset w ∩ D₃) ∪ (G.neighborFinset w ∩ D₄)).card := by
            rw [Finset.card_union_of_disjoint]
            exact Finset.disjoint_of_subset_left Finset.inter_subset_right
              (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj)
          rw [hcup]
          calc ((G.neighborFinset w ∩ D₃) ∪ (G.neighborFinset w ∩ D₄)).card
              ≤ (G.neighborFinset w).card := by
                refine Finset.card_le_card fun z hz => ?_
                rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at hz
                rcases hz with h | h
                · exact h.1
                · exact h.1
            _ = G.degree w := G.card_neighborFinset_eq_degree w
  have hheavy := card_heavy_le G
  rw [← hH] at hheavy
  omega

open Classical in
/-- **The slope-`11/2` light-cell covering** — a sharpening of
`compact_covering_nine` (slope `6 → 11/2`).  Two extra levers over the crude
covering: (1) the degree-3 handshake `|D₃| = 8 + X`, and (2) the *far-heavy
multiplicity* of a suppressed **degree-3** halo vertex — it has two heavy
neighbours (`nonusable_deg3_structure`), and *every* heavy neighbour of a vertex
outside the ball lies outside the 2-ball (`hfarnbr`), so it draws **two** far
heavy slots, not one.  A suppressed degree-4 halo vertex still draws only one
(`v` with three degree-4 and one degree-5 neighbour has `sigS = 2/3 + 3·(1/2) >
2` yet a single heavy neighbour), so the naive `≥ 2`-far bound is *false*; but
the handshake forces `|Bh₃|` large whenever the far excess outgrows the ball,
and balancing `|Bh₃| ≥ 0` against `|closeSet| + |Bh₃| ≥ 8 + X` yields, on a
non-double-counting four-piece cover,

  `2·n ≤ 151 + 11·X`

i.e. `n ≤ 75.5 + 5.5·X`.  The slope `11/2` is tight (achieved at
`X_far = 3·X_near`). -/
theorem compact_covering_eleven_halves (n : ℕ) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v, 3 ≤ G.degree v) (hcpt : ¬HasUsableFarPair G)
    (hlight : ∃ u : Fin n, sigS G u ≤ 2 ∧ G.degree u ≤ 4) :
    2 * n ≤ 151 + 11 * excessX n G := by
  classical
  obtain ⟨u₀, hu₀, hu₀4⟩ := hlight
  have hn2 : 2 ≤ n := by
    have hlt : G.degree u₀ < n := by
      have := G.degree_lt_card_verts u₀
      simpa using this
    have := h3 u₀
    omega
  set TB : Finset (Fin n) := insert u₀ (G.neighborFinset u₀
    ∪ (G.neighborFinset u₀).biUnion (fun w => G.neighborFinset w)) with hTB
  set Hfar : Finset (Fin n) :=
    (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)) \ TB with hHfar
  set Bh3 : Finset (Fin n) :=
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3)) \ closeSet G u₀ with hBh3
  set Bh4 : Finset (Fin n) :=
    (Finset.univ.filter (fun v : Fin n => G.degree v = 4)) \ closeSet G u₀ with hBh4
  set Hout : Finset (Fin n) :=
    (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)) \ closeSet G u₀ with hHout
  -- the 2-ball sits inside the 3-ball
  have hTBclose : TB ⊆ closeSet G u₀ := by
    rw [hTB]
    intro x hx
    rcases Finset.mem_insert.mp hx with heq | hx
    · rw [heq]; exact mem_closeSet_self G u₀
    · rcases Finset.mem_union.mp hx with hx1 | hx2
      · exact mem_closeSet_of_adj G ((G.mem_neighborFinset u₀ x).mp hx1)
      · obtain ⟨w, hwA, hxw⟩ := Finset.mem_biUnion.mp hx2
        exact mem_closeSet_of_adj_adj G ((G.mem_neighborFinset u₀ w).mp hwA)
          ((G.mem_neighborFinset w x).mp hxw)
  -- every heavy neighbour of a vertex outside the ball lands in `Hfar`
  have hfarnbr : ∀ v : Fin n, v ∉ closeSet G u₀ →
      ∀ w, w ∈ G.neighborFinset v → 5 ≤ G.degree w → w ∈ Hfar := by
    intro v hvc w hwN hw5
    rw [hHfar, Finset.mem_sdiff]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw5⟩, ?_⟩
    intro hwTB
    rw [hTB, Finset.mem_insert] at hwTB
    have hadj : G.Adj w v := (G.mem_neighborFinset v w).mp hwN |>.symm
    rcases hwTB with rfl | hwTB
    · exact hvc (mem_closeSet_of_adj G hadj)
    · rw [Finset.mem_union] at hwTB
      rcases hwTB with hwA | hwB
      · exact hvc (mem_closeSet_of_adj_adj G ((G.mem_neighborFinset u₀ w).mp hwA) hadj)
      · obtain ⟨a, haA, hwa⟩ := Finset.mem_biUnion.mp hwB
        exact hvc (mem_closeSet_of_adj_adj_adj G
          ((G.mem_neighborFinset u₀ a).mp haA) ((G.mem_neighborFinset a w).mp hwa) hadj)
  -- the four-piece cover (degree-partitioned outside the ball; no double count)
  have hcover : n ≤ (closeSet G u₀).card + Bh3.card + Bh4.card + Hout.card := by
    have hsub : (Finset.univ : Finset (Fin n)) ⊆
        closeSet G u₀ ∪ Bh3 ∪ Bh4 ∪ Hout := by
      intro v _
      by_cases hc : v ∈ closeSet G u₀
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
      · have hdeg := h3 v
        by_cases hd3 : G.degree v = 3
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, hd3⟩, hc⟩)))
        · by_cases hd4 : G.degree v = 4
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_sdiff.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, hd4⟩, hc⟩))
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩, hc⟩)
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (closeSet G u₀ ∪ Bh3 ∪ Bh4 ∪ Hout).card := Finset.card_le_card hsub
      _ ≤ (closeSet G u₀ ∪ Bh3 ∪ Bh4).card + Hout.card := Finset.card_union_le _ _
      _ ≤ (closeSet G u₀ ∪ Bh3).card + Bh4.card + Hout.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (closeSet G u₀).card + Bh3.card + Bh4.card + Hout.card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  -- ball bound with near excess
  have hball := card_closeSet_le_light_twoball G u₀ h3 hu₀4
  rw [← hTB] at hball
  set Xnear : ℕ := ∑ w ∈ TB.filter (fun w => 5 ≤ G.degree w), (G.degree w - 4)
    with hXnear
  set Xfar : ℕ := ∑ w ∈ Hfar, (G.degree w - 4) with hXfar
  -- far heavy slots: `∑ deg = Xfar + 4·|Hfar|`, and `|Hfar| ≤ Xfar`
  have hslotdeg : ∑ w ∈ Hfar, G.degree w = Xfar + 4 * Hfar.card := by
    rw [hXfar]
    have hpt : ∀ w ∈ Hfar, G.degree w = (G.degree w - 4) + 4 := by
      intro w hw
      rw [hHfar, Finset.mem_sdiff, Finset.mem_filter] at hw
      have := hw.1.2
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm]
  have hHfarle : Hfar.card ≤ Xfar := by
    rw [hXfar]
    calc Hfar.card = ∑ _w ∈ Hfar, 1 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
      _ ≤ ∑ w ∈ Hfar, (G.degree w - 4) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [hHfar, Finset.mem_sdiff, Finset.mem_filter] at hw
          have := hw.1.2
          omega
  -- `Hout ⊆ Hfar`, so `|Hout| ≤ Xfar`
  have hHoutle : Hout.card ≤ Xfar := by
    have hsub : Hout ⊆ Hfar := by
      rw [hHout, hHfar]
      exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hTBclose
    exact le_trans (Finset.card_le_card hsub) hHfarle
  -- the far-support incidence: deg-3 halo draws 2, deg-4 halo draws 1
  have hdisj34 : Disjoint Bh3 Bh4 := by
    rw [Finset.disjoint_left]
    intro v hv3 hv4
    rw [hBh3, Finset.mem_sdiff, Finset.mem_filter] at hv3
    rw [hBh4, Finset.mem_sdiff, Finset.mem_filter] at hv4
    have := hv3.1.2
    have := hv4.1.2
    omega
  have hinc3 : ∀ v ∈ Bh3, 2 ≤ (G.neighborFinset v ∩ Hfar).card := by
    intro v hv
    rw [hBh3, Finset.mem_sdiff, Finset.mem_filter] at hv
    obtain ⟨⟨-, hd3⟩, hvc⟩ := hv
    have hsup := nonusable_of_far G hcpt u₀ hu₀ v hvc
    obtain ⟨-, -, htwo⟩ := nonusable_deg3_structure G v hd3 h3 hsup
    have hsub : (G.neighborFinset v).filter (fun w => 5 ≤ G.degree w)
        ⊆ G.neighborFinset v ∩ Hfar := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_inter]
      exact ⟨hw.1, hfarnbr v hvc w hw.1 hw.2⟩
    calc 2 ≤ ((G.neighborFinset v).filter (fun w => 5 ≤ G.degree w)).card := htwo
      _ ≤ (G.neighborFinset v ∩ Hfar).card := Finset.card_le_card hsub
  have hinc4 : ∀ v ∈ Bh4, 1 ≤ (G.neighborFinset v ∩ Hfar).card := by
    intro v hv
    rw [hBh4, Finset.mem_sdiff, Finset.mem_filter] at hv
    obtain ⟨⟨-, hd4⟩, hvc⟩ := hv
    have hsup := nonusable_of_far G hcpt u₀ hu₀ v hvc
    obtain ⟨w, hwN, hw5⟩ := nonusable_light_has_heavy_nbr G h3 v (by omega) hsup
    refine Finset.card_pos.mpr ⟨w, ?_⟩
    rw [Finset.mem_inter]
    exact ⟨hwN, hfarnbr v hvc w hwN hw5⟩
  have hincidence : 2 * Bh3.card + Bh4.card ≤ ∑ w ∈ Hfar, G.degree w := by
    have h3sum : 2 * Bh3.card ≤ ∑ v ∈ Bh3, (G.neighborFinset v ∩ Hfar).card := by
      calc 2 * Bh3.card = ∑ _v ∈ Bh3, 2 := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ v ∈ Bh3, (G.neighborFinset v ∩ Hfar).card := Finset.sum_le_sum hinc3
    have h4sum : Bh4.card ≤ ∑ v ∈ Bh4, (G.neighborFinset v ∩ Hfar).card := by
      calc Bh4.card = ∑ _v ∈ Bh4, 1 := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
        _ ≤ ∑ v ∈ Bh4, (G.neighborFinset v ∩ Hfar).card := Finset.sum_le_sum hinc4
    calc 2 * Bh3.card + Bh4.card
        ≤ ∑ v ∈ Bh3, (G.neighborFinset v ∩ Hfar).card
          + ∑ v ∈ Bh4, (G.neighborFinset v ∩ Hfar).card := Nat.add_le_add h3sum h4sum
      _ = ∑ w ∈ Hfar, (G.neighborFinset w ∩ Bh3).card
          + ∑ w ∈ Hfar, (G.neighborFinset w ∩ Bh4).card := by
          rw [sum_nbr_inter_comm G Bh3 Hfar, sum_nbr_inter_comm G Bh4 Hfar]
      _ = ∑ w ∈ Hfar, ((G.neighborFinset w ∩ Bh3).card
          + (G.neighborFinset w ∩ Bh4).card) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ w ∈ Hfar, G.degree w := by
          refine Finset.sum_le_sum fun w _ => ?_
          have hcup : (G.neighborFinset w ∩ Bh3).card + (G.neighborFinset w ∩ Bh4).card
              = ((G.neighborFinset w ∩ Bh3) ∪ (G.neighborFinset w ∩ Bh4)).card := by
            rw [Finset.card_union_of_disjoint]
            exact Finset.disjoint_of_subset_left Finset.inter_subset_right
              (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj34)
          rw [hcup]
          calc ((G.neighborFinset w ∩ Bh3) ∪ (G.neighborFinset w ∩ Bh4)).card
              ≤ (G.neighborFinset w).card := by
                refine Finset.card_le_card fun z hz => ?_
                rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at hz
                rcases hz with h | h
                · exact h.1
                · exact h.1
            _ = G.degree w := G.card_neighborFinset_eq_degree w
  -- the handshake `|D₃| = 8 + X`, so `|closeSet| + |Bh₃| ≥ 8 + X`
  have hd3card : (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card
      = 8 + excessX n G := by
    have hkey := deg3_card_eq_eight_add_excess n G hn2 hm h3
    rwa [deg3Set] at hkey
  have hsplit3 : ((Finset.univ.filter (fun v : Fin n => G.degree v = 3))
        ∩ closeSet G u₀).card + Bh3.card
      = (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card := by
    rw [hBh3]
    exact Finset.card_inter_add_card_sdiff _ _
  have hnB3le : ((Finset.univ.filter (fun v : Fin n => G.degree v = 3))
      ∩ closeSet G u₀).card ≤ (closeSet G u₀).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hhand : 8 + excessX n G ≤ (closeSet G u₀).card + Bh3.card := by
    omega
  -- the excess splits between near and far heavies
  have hsplitX : Xnear + Xfar ≤ excessX n G := by
    rw [hXnear, hXfar, excessX]
    have hdisj : Disjoint (TB.filter (fun w => 5 ≤ G.degree w)) Hfar := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [hHfar, Finset.mem_sdiff] at hw2
      exact hw2.2 (Finset.mem_of_mem_filter w hw1)
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
    intro w hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · rw [Finset.mem_filter] at hw ⊢
      exact ⟨Finset.mem_univ w, hw.2⟩
    · rw [hHfar, Finset.mem_sdiff] at hw
      exact hw.1
  -- the slope-`11/2` LP: average of the crude bound and the handshake bound
  omega

open Classical in
/-- **The β excess bound** (`β = 105/128`): on the boundary of the compact
cell, either a σ-law fires or `23·X ≤ 128·C_m + 34508` — the sharpened
`X ≤ (128/23)·m + const` from `suppressed_ledger_beta`
(`(32/21)s ≤ (5/4)X + 685` with `8 + X = m + s`). -/
theorem sfb_excess_bound_beta (n : ℕ) [Nonempty (Fin n)] (hn : 512 ≤ n)
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G) (hb : SeaFatBoundary G)
    (hcpt : ¬HasUsableFarPair G) (C_m : ℕ)
    (hmb : (Finset.univ.filter
        (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card ≤ C_m) :
    algConn G ≤ 2 ∨ 23 * excessX n G ≤ 128 * C_m + 34508 := by
  classical
  rcases suppressed_ledger_beta n hn G h hb hcpt with hfire | hled
  · exact Or.inl hfire
  refine Or.inr ?_
  have key := deg3_card_eq_eight_add_excess n G (by omega) h.edge_card h.min_degree
  have hsplit := deg3_usable_suppressed_split n G
  have hpart : 8 + excessX n G
      = (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card
        + (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v)).card :=
    key.symm.trans hsplit
  have hpartR : (8 : ℝ) + (excessX n G : ℝ)
      = ((Finset.univ.filter
            (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card : ℝ)
        + ((Finset.univ.filter
            (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v)).card : ℝ) := by
    exact_mod_cast hpart
  have hmR : ((Finset.univ.filter
      (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card : ℝ) ≤ (C_m : ℝ) := by
    exact_mod_cast hmb
  have hXR : (23 : ℝ) * (excessX n G : ℝ)
      ≤ ((128 * C_m + 34508 : ℕ) : ℝ) := by
    push_cast
    linarith [hled, hpartR, hmR]
  exact_mod_cast hXR

end ACMax
