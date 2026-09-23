/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.FarPair
public import LeanPool.ACMax.Counting.CompactCell
public import LeanPool.ACMax.Counting.CompactLedgers
public import LeanPool.ACMax.Counting.HubCross
public import LeanPool.ACMax.Counting.Quotient

/-!
# The σ-weighted firing laws, the σ-transfer, and the `W₅ᵇ` cloud bound

The σ-weighted supply machinery for the mid-range boundedness program: two σ-shaped
firing laws, the unified σ-transfer inequality behind `β = 105/128`, and the bound
on the one cloud class (`W₅ᵇ`) that obstructs it. All certificates use the σ-weights
`p_w = c/(deg w − 2)` and the per-slot cost identity
`(c − c/(d−2))² + (d−3)·(c/(d−2))² = c²·σ(d)`.

## Main results

* `algConn_le_two_of_sigma_apex_pair` (**LAW A**) — an apex pair (`u, v` share
  one neighbour `g` of weight 0, no cross edges, each side's non-apex σ-sum
  `≤ 1`) closes with slack `cB²(Σ_A σ − 1) + cA²(Σ_B σ − 1) ≤ 0`.
* `algConn_le_two_of_sigma_cross_pair` (**LAW B**) — a far pair with one heavy
  cross `(h, h′)` and `sigS + 1/(deg h − 2) ≤ 2` on each side closes (the
  master's leak set discounts the cross at `h`).
* The **unified σ-transfer** `σ(d)·(a₃ + j) ≤ (5/4)(d − 4) + S_w`: summed over
  heavy vertices the transfer terms cancel identically, giving
  `Σ σ(d)·a₃ ≤ (5/4)·X + exceptions`, the two exceptions being the `W₅`
  overflow `sigma_transfer_w5` (`1/12`) and the SFB-capped classes.
* The `W₅ᵇ` cloud bound: `w5big_structure`, `w5big_pair_mechanism`,
  `w5big_cloud_le` (each big hub carries `≤ 269` members) and `w5big_card_le`
  (`|W₅ᵇ| ≤ 5441`) — unless a σ-law fires, via `W5LawConfig` / `w5LawConfig_closes`.
* `suppressed_ledger_beta` — the assembled supply bound `β = 105/128 < 7/8` for
  `n ≥ 512`.
-/

@[expose] public section

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- The σ-slot cost identity: with weight `c/(d−2)`,
`(c − c/(d−2))² + (d−3)(c/(d−2))² = c²·σ(d)`. -/
theorem sigma_slot_identity (c : ℝ) {d : ℕ} (hd : 3 ≤ d) :
    (c - c / ((d : ℝ) - 2)) ^ 2 + ((d : ℝ) - 3) * (c / ((d : ℝ) - 2)) ^ 2
      = c ^ 2 * sigma d := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hD0 : ((d : ℝ) - 2) ≠ 0 := by linarith
  rw [sigma]
  field_simp
  ring

open Classical in
/-- **LAW A — the σ-apex law.**  Two non-adjacent vertices sharing exactly one
common neighbour `g`, with no cross edges between the punctured
neighbourhoods and per-side punctured σ-sum at most `1`, certify
`algConn ≤ 2`.  (Weights `p_w = cB/(deg w − 2)` on `N(u) \ {g}`,
`q_w = cA/(deg w − 2)` on `N(v) \ {g}`, apex at `0`; the cross-scaled
magnitudes `au = cB`, `av = cA` balance the sides exactly.) -/
theorem algConn_le_two_of_sigma_apex_pair [Nonempty V]
    (G : SimpleGraph V) (u v g : V)
    (h3 : ∀ w, 3 ≤ G.degree w) (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hgu : G.Adj u g) (hgv : G.Adj v g)
    (hcap : ∀ w : V, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w))
    (hnc : ∀ w ∈ (G.neighborFinset u).erase g,
      ∀ w' ∈ (G.neighborFinset v).erase g, ¬G.Adj w w')
    (hsu : ∑ w ∈ (G.neighborFinset u).erase g, sigma (G.degree w) ≤ 1)
    (hsv : ∑ w ∈ (G.neighborFinset v).erase g, sigma (G.degree w) ≤ 1) :
    algConn G ≤ 2 := by
  classical
  set cA : ℝ := 1 + ∑ w ∈ (G.neighborFinset u).erase g,
    1 / ((G.degree w : ℝ) - 2) with hcA
  set cB : ℝ := 1 + ∑ w ∈ (G.neighborFinset v).erase g,
    1 / ((G.degree w : ℝ) - 2) with hcB
  have hDpos : ∀ w : V, (0 : ℝ) < (G.degree w : ℝ) - 2 := by
    intro w
    have : (3 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast h3 w
    linarith
  have hterm_nonneg : ∀ w : V, (0 : ℝ) ≤ 1 / ((G.degree w : ℝ) - 2) :=
    fun w => le_of_lt (div_pos one_pos (hDpos w))
  have hcA1 : (1 : ℝ) ≤ cA := by
    rw [hcA]
    have : (0 : ℝ) ≤ ∑ w ∈ (G.neighborFinset u).erase g, 1 / ((G.degree w : ℝ) - 2) :=
      Finset.sum_nonneg fun w _ => hterm_nonneg w
    linarith
  have hcB1 : (1 : ℝ) ≤ cB := by
    rw [hcB]
    have : (0 : ℝ) ≤ ∑ w ∈ (G.neighborFinset v).erase g, 1 / ((G.degree w : ℝ) - 2) :=
      Finset.sum_nonneg fun w _ => hterm_nonneg w
    linarith
  have hcA0 : (0 : ℝ) < cA := by linarith
  have hcB0 : (0 : ℝ) < cB := by linarith
  refine algConn_le_two_of_apex_double_star G u v g cB cA
    (fun w => cB / ((G.degree w : ℝ) - 2))
    (fun w => cA / ((G.degree w : ℝ) - 2))
    hne huv hgu hgv hcap hcB0
    (fun w _ => le_of_lt (div_pos hcB0 (hDpos w)))
    (fun w _ => le_of_lt (div_pos hcA0 (hDpos w)))
    ?_ ?_
  · -- balance: `cB·cA = cA·cB`
    have h1 : ∑ w ∈ (G.neighborFinset u).erase g, cB / ((G.degree w : ℝ) - 2)
        = cB * ∑ w ∈ (G.neighborFinset u).erase g, 1 / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ (G.neighborFinset v).erase g, cA / ((G.degree w : ℝ) - 2)
        = cA * ∑ w ∈ (G.neighborFinset v).erase g, 1 / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [h1, h2, hcA, hcB]
    ring
  · -- the quadratic-form certificate
    -- crosses vanish
    have hcross : ∑ w ∈ (G.neighborFinset u).erase g, ∑ w' ∈ (G.neighborFinset v).erase g,
        (if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2)
          + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun w' hw' => ?_
      rw [ite_eq_right (hnc w hw w' hw')]
    -- generic per-slot bound: leak ≤ deg − 1 plus the slot identity
    have hslot : ∀ (c : ℝ) (z : V) (Z : Finset V) (w : V),
        G.Adj z w →
        (c - c / ((G.degree w : ℝ) - 2)) ^ 2
          + ((G.neighborFinset w \ insert z Z).card : ℝ)
            * (c / ((G.degree w : ℝ) - 2)) ^ 2
        ≤ c ^ 2 * sigma (G.degree w)
          + 2 * (c / ((G.degree w : ℝ) - 2)) ^ 2 := by
      intro c z Z w hzw
      have hzwN : z ∈ G.neighborFinset w := by
        rw [SimpleGraph.mem_neighborFinset]
        exact G.adj_symm hzw
      have hsub : G.neighborFinset w \ insert z Z
          ⊆ (G.neighborFinset w).erase z := by
        intro y hy
        rw [Finset.mem_sdiff] at hy
        exact Finset.mem_erase.mpr
          ⟨fun h => hy.2 (h ▸ Finset.mem_insert_self z Z), hy.1⟩
      have hcard : (G.neighborFinset w \ insert z Z).card + 1 ≤ G.degree w := by
        have h1 : (G.neighborFinset w \ insert z Z).card
            ≤ ((G.neighborFinset w).erase z).card := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hzwN,
          G.card_neighborFinset_eq_degree] at h1
        have := h3 w
        omega
      have hleakR : ((G.neighborFinset w \ insert z Z).card : ℝ)
          ≤ (G.degree w : ℝ) - 1 := by
        have : ((G.neighborFinset w \ insert z Z).card : ℝ) + 1
            ≤ (G.degree w : ℝ) := by exact_mod_cast hcard
        linarith
      have hid := sigma_slot_identity c (h3 w)
      have hp2 : (0 : ℝ) ≤ (c / ((G.degree w : ℝ) - 2)) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hleakR hp2]
    -- sum the per-slot bounds on each side
    have hsumA : ∑ w ∈ (G.neighborFinset u).erase g, ((cB - cB / ((G.degree w : ℝ) - 2)) ^ 2)
        + ∑ w ∈ (G.neighborFinset u).erase g, ((G.neighborFinset w \ insert u ((G.neighborFinset
          v).erase g)).card : ℝ)
          * (cB / ((G.degree w : ℝ) - 2)) ^ 2
        ≤ cB ^ 2 + 2 * ∑ w ∈ (G.neighborFinset u).erase g, (cB / ((G.degree w : ℝ) - 2)) ^ 2 := by
      have h1 : ∑ w ∈ (G.neighborFinset u).erase g, ((cB - cB / ((G.degree w : ℝ) - 2)) ^ 2
            + ((G.neighborFinset w \ insert u ((G.neighborFinset v).erase g)).card : ℝ)
              * (cB / ((G.degree w : ℝ) - 2)) ^ 2)
          ≤ ∑ w ∈ (G.neighborFinset u).erase g, (cB ^ 2 * sigma (G.degree w)
            + 2 * (cB / ((G.degree w : ℝ) - 2)) ^ 2) := by
        refine Finset.sum_le_sum fun w hw => ?_
        exact hslot cB u ((G.neighborFinset v).erase g) w ((G.mem_neighborFinset u w).mp
          (Finset.mem_of_mem_erase hw))
      rw [Finset.sum_add_distrib] at h1
      have h2 : ∑ w ∈ (G.neighborFinset u).erase g, (cB ^ 2 * sigma (G.degree w)
            + 2 * (cB / ((G.degree w : ℝ) - 2)) ^ 2)
          = cB ^ 2 * (∑ w ∈ (G.neighborFinset u).erase g, sigma (G.degree w))
            + 2 * ∑ w ∈ (G.neighborFinset u).erase g, (cB / ((G.degree w : ℝ) - 2)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [h2] at h1
      have h3' : cB ^ 2 * (∑ w ∈ (G.neighborFinset u).erase g, sigma (G.degree w)) ≤ cB ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsu (sq_nonneg cB)
      linarith
    have hsumB : ∑ w ∈ (G.neighborFinset v).erase g, ((cA - cA / ((G.degree w : ℝ) - 2)) ^ 2)
        + ∑ w ∈ (G.neighborFinset v).erase g, ((G.neighborFinset w \ insert v ((G.neighborFinset
          u).erase g)).card : ℝ)
          * (cA / ((G.degree w : ℝ) - 2)) ^ 2
        ≤ cA ^ 2 + 2 * ∑ w ∈ (G.neighborFinset v).erase g, (cA / ((G.degree w : ℝ) - 2)) ^ 2 := by
      have h1 : ∑ w ∈ (G.neighborFinset v).erase g, ((cA - cA / ((G.degree w : ℝ) - 2)) ^ 2
            + ((G.neighborFinset w \ insert v ((G.neighborFinset u).erase g)).card : ℝ)
              * (cA / ((G.degree w : ℝ) - 2)) ^ 2)
          ≤ ∑ w ∈ (G.neighborFinset v).erase g, (cA ^ 2 * sigma (G.degree w)
            + 2 * (cA / ((G.degree w : ℝ) - 2)) ^ 2) := by
        refine Finset.sum_le_sum fun w hw => ?_
        exact hslot cA v ((G.neighborFinset u).erase g) w ((G.mem_neighborFinset v w).mp
          (Finset.mem_of_mem_erase hw))
      rw [Finset.sum_add_distrib] at h1
      have h2 : ∑ w ∈ (G.neighborFinset v).erase g, (cA ^ 2 * sigma (G.degree w)
            + 2 * (cA / ((G.degree w : ℝ) - 2)) ^ 2)
          = cA ^ 2 * (∑ w ∈ (G.neighborFinset v).erase g, sigma (G.degree w))
            + 2 * ∑ w ∈ (G.neighborFinset v).erase g, (cA / ((G.degree w : ℝ) - 2)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [h2] at h1
      have h3' : cA ^ 2 * (∑ w ∈ (G.neighborFinset v).erase g, sigma (G.degree w)) ≤ cA ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsv (sq_nonneg cA)
      linarith
    rw [hcross]
    linarith [hsumA, hsumB]

open Classical in
/-- Generic σ-slot bound: for any adjacent anchor `z` and slot `w`, with
weight `p = c/(deg w − 2)` and master leak set `N(w) ∖ insert z Z`,

  `(c − p)² + L·p² ≤ c²·σ(deg w) + 2p²`. -/
theorem sigma_slot_le (G : SimpleGraph V) (h3 : ∀ w, 3 ≤ G.degree w)
    (c : ℝ) (z : V) (Z : Finset V) (w : V) (hzw : G.Adj z w) :
    (c - c / ((G.degree w : ℝ) - 2)) ^ 2
      + ((G.neighborFinset w \ insert z Z).card : ℝ)
        * (c / ((G.degree w : ℝ) - 2)) ^ 2
    ≤ c ^ 2 * sigma (G.degree w) + 2 * (c / ((G.degree w : ℝ) - 2)) ^ 2 := by
  classical
  have hzwN : z ∈ G.neighborFinset w := by
    rw [SimpleGraph.mem_neighborFinset]
    exact G.adj_symm hzw
  have hsub : G.neighborFinset w \ insert z Z ⊆ (G.neighborFinset w).erase z := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    exact Finset.mem_erase.mpr
      ⟨fun h => hy.2 (h ▸ Finset.mem_insert_self z Z), hy.1⟩
  have hcard : (G.neighborFinset w \ insert z Z).card + 1 ≤ G.degree w := by
    have h1 : (G.neighborFinset w \ insert z Z).card
        ≤ ((G.neighborFinset w).erase z).card := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hzwN, G.card_neighborFinset_eq_degree] at h1
    have := h3 w
    omega
  have hleakR : ((G.neighborFinset w \ insert z Z).card : ℝ)
      ≤ (G.degree w : ℝ) - 1 := by
    have : ((G.neighborFinset w \ insert z Z).card : ℝ) + 1
        ≤ (G.degree w : ℝ) := by exact_mod_cast hcard
    linarith
  have hid := sigma_slot_identity c (h3 w)
  have hp2 : (0 : ℝ) ≤ (c / ((G.degree w : ℝ) - 2)) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hleakR hp2]

open Classical in
/-- Sharp σ-slot bound at a crossing slot: if additionally `w` has a
neighbour `y ∈ Z` distinct from `z`, the leak drops by one more:

  `(c − p)² + L·p² ≤ c²·σ(deg w) + p²`. -/
theorem sigma_slot_le_sharp (G : SimpleGraph V) (h3 : ∀ w, 3 ≤ G.degree w)
    (c : ℝ) (z : V) (Z : Finset V) (w y : V) (hzw : G.Adj z w)
    (hwy : G.Adj w y) (hyZ : y ∈ Z) (hyz : y ≠ z) :
    (c - c / ((G.degree w : ℝ) - 2)) ^ 2
      + ((G.neighborFinset w \ insert z Z).card : ℝ)
        * (c / ((G.degree w : ℝ) - 2)) ^ 2
    ≤ c ^ 2 * sigma (G.degree w) + (c / ((G.degree w : ℝ) - 2)) ^ 2 := by
  classical
  have hzwN : z ∈ G.neighborFinset w := by
    rw [SimpleGraph.mem_neighborFinset]
    exact G.adj_symm hzw
  have hywN : y ∈ G.neighborFinset w := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hwy
  have hsub : G.neighborFinset w \ insert z Z
      ⊆ ((G.neighborFinset w).erase z).erase y := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    refine Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ Finset.mem_insert_of_mem hyZ),
      Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ Finset.mem_insert_self z Z), hx.1⟩⟩
  have hcard : (G.neighborFinset w \ insert z Z).card + 2 ≤ G.degree w := by
    have h1 : (G.neighborFinset w \ insert z Z).card
        ≤ (((G.neighborFinset w).erase z).erase y).card := Finset.card_le_card hsub
    have hy' : y ∈ (G.neighborFinset w).erase z := Finset.mem_erase.mpr ⟨hyz, hywN⟩
    rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hzwN,
      G.card_neighborFinset_eq_degree] at h1
    have := h3 w
    omega
  have hleakR : ((G.neighborFinset w \ insert z Z).card : ℝ)
      ≤ (G.degree w : ℝ) - 2 := by
    have : ((G.neighborFinset w \ insert z Z).card : ℝ) + 2
        ≤ (G.degree w : ℝ) := by exact_mod_cast hcard
    linarith
  have hid := sigma_slot_identity c (h3 w)
  have hp2 : (0 : ℝ) ≤ (c / ((G.degree w : ℝ) - 2)) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hleakR hp2]

open Classical in
private theorem algConn_le_two_of_sigma_cross_pair_hcrossle : ∀ {V : Type u_1} [Fintype V]
  (G : SimpleGraph V)
  (u v h h' : V) (_ : G.Adj u h) (_ : G.Adj v h')
  (_ : ∀ w ∈ G.neighborFinset u, ∀ w' ∈ G.neighborFinset v, G.Adj w w' → w = h ∧ w' = h')
  (_ : sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2) (_ : sigS G v + 1 / ((G.degree h' : ℝ) - 2)
    ≤ 2),
  let cA : ℝ := 1 + ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2);
  let cB : ℝ := 1 + ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2);
  ∀ (_ : h ∈ G.neighborFinset u) (_ : h' ∈ G.neighborFinset v)
    (_ : cB / ((G.degree h : ℝ) - 2) = cB * (1 / ((G.degree h : ℝ) - 2))),
    (∑ w ∈ G.neighborFinset u,
        ∑ w' ∈ G.neighborFinset v,
          if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2) + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else
            0) ≤
      (cB / ((G.degree h : ℝ) - 2) + cA / ((G.degree h' : ℝ) - 2)) ^ 2 := by
  classical
  intro V inst G u v h h' hh hh' hcross1 hsu hsv cA cB hhN hh'N hph
  have hrow : ∀ w ∈ G.neighborFinset u,
      ∑ w' ∈ G.neighborFinset v,
        (if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2)
          + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else 0)
      ≤ (if w = h then (cB / ((G.degree h : ℝ) - 2)
          + cA / ((G.degree h' : ℝ) - 2)) ^ 2 else 0) := by
    intro w hw
    by_cases hwh : w = h
    · subst hwh
      rw [ite_eq_left rfl]
      calc ∑ w' ∈ G.neighborFinset v,
          (if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2)
            + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else 0)
          ≤ ∑ w' ∈ G.neighborFinset v,
            (if w' = h' then (cB / ((G.degree w : ℝ) - 2)
              + cA / ((G.degree h' : ℝ) - 2)) ^ 2 else 0) := by
            refine Finset.sum_le_sum fun w' hw' => ?_
            by_cases hadj : G.Adj w w'
            · obtain ⟨-, rfl⟩ := hcross1 w hw w' hw' hadj
              rw [ite_eq_left hadj, ite_eq_left rfl]
            · rw [ite_eq_right hadj]
              split <;> positivity
        _ = (cB / ((G.degree w : ℝ) - 2)
            + cA / ((G.degree h' : ℝ) - 2)) ^ 2 := by
            rw [Finset.sum_ite_eq' (G.neighborFinset v) h']
            exact ite_eq_left hh'N
    · rw [ite_eq_right hwh]
      refine le_of_eq (Finset.sum_eq_zero fun w' hw' => ?_)
      refine ite_eq_right fun hadj => hwh (hcross1 w hw w' hw' hadj).1
  calc ∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
      (if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2)
        + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else 0)
      ≤ ∑ w ∈ G.neighborFinset u,
        (if w = h then (cB / ((G.degree h : ℝ) - 2)
          + cA / ((G.degree h' : ℝ) - 2)) ^ 2 else 0) :=
        Finset.sum_le_sum hrow
    _ = (cB / ((G.degree h : ℝ) - 2) + cA / ((G.degree h' : ℝ) - 2)) ^ 2 := by
        rw [Finset.sum_ite_eq' (G.neighborFinset u) h]
        exact ite_eq_left hhN

open Classical in
private theorem algConn_le_two_of_sigma_cross_pair_hsideU : ∀ {V : Type u_1} [Fintype V] (G
  : SimpleGraph V)
  (u v h h' : V) (_ : ∀ (w : V), 3 ≤ G.degree w) (_ : ¬G.Adj u v) (_ : G.Adj u h) (_ : G.Adj
    v h')
  (_ : ∀ w ∈ G.neighborFinset u, ∀ w' ∈ G.neighborFinset v, G.Adj w w' → w = h ∧ w' = h')
  (_ : sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2),
  let cA : ℝ := 1 + ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2);
  let cB : ℝ := 1 + ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2);
  ∀ (_ : h ∈ G.neighborFinset u) (_ : h' ∈ G.neighborFinset v)
    (_ : cB / ((G.degree h : ℝ) - 2) = cB * (1 / ((G.degree h : ℝ) - 2)))
    (_ :
      (∑ w ∈ G.neighborFinset u,
          ∑ w' ∈ G.neighborFinset v,
            if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2) + cA / ((G.degree w' : ℝ) - 2)) ^ 2
              else 0) ≤
        (cB / ((G.degree h : ℝ) - 2) + cA / ((G.degree h' : ℝ) - 2)) ^ 2)
    (_ : G.Adj h h'),
    ∑ w ∈ G.neighborFinset u, (cB - cB / ((G.degree w : ℝ) - 2)) ^ 2 +
        ∑ w ∈ G.neighborFinset u,
          ↑(#(G.neighborFinset w \ insert u (G.neighborFinset v))) * (cB / ((G.degree w : ℝ) - 2))
            ^ 2 ≤
      cB ^ 2 * sigS G u + 2 * ∑ w ∈ G.neighborFinset u, (cB / ((G.degree w : ℝ) - 2)) ^ 2 -
        (cB / ((G.degree h : ℝ) - 2)) ^ 2 := by
  classical
  intro V inst G u v h h' h3 huv hh hh' hcross1 hsu cA cB hhN hh'N hph hcrossle hhh'
  have hpt : ∀ w ∈ G.neighborFinset u,
      (cB - cB / ((G.degree w : ℝ) - 2)) ^ 2
        + ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
          * (cB / ((G.degree w : ℝ) - 2)) ^ 2
      ≤ cB ^ 2 * sigma (G.degree w)
        + 2 * (cB / ((G.degree w : ℝ) - 2)) ^ 2
        - (if w = h then (cB / ((G.degree w : ℝ) - 2)) ^ 2 else 0) := by
    intro w hw
    have hadj_uw : G.Adj u w := (G.mem_neighborFinset u w).mp hw
    by_cases hwh : w = h
    · subst hwh
      rw [ite_eq_left rfl]
      have hsharp := sigma_slot_le_sharp G h3 cB u (G.neighborFinset v)
        w h' hadj_uw hhh' hh'N (fun hc => huv (hc ▸ (G.adj_symm hh')))
      linarith
    · rw [ite_eq_right hwh]
      have hgen := sigma_slot_le G h3 cB u (G.neighborFinset v) w hadj_uw
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hrhs : ∑ w ∈ G.neighborFinset u,
      (cB ^ 2 * sigma (G.degree w)
        + 2 * (cB / ((G.degree w : ℝ) - 2)) ^ 2
        - (if w = h then (cB / ((G.degree w : ℝ) - 2)) ^ 2 else 0))
      = cB ^ 2 * sigS G u
        + 2 * ∑ w ∈ G.neighborFinset u, (cB / ((G.degree w : ℝ) - 2)) ^ 2
        - (cB / ((G.degree h : ℝ) - 2)) ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sigS]
    congr 1
    rw [Finset.sum_ite_eq' (G.neighborFinset u) h]
    exact ite_eq_left hhN
  rw [hrhs] at hsum
  linarith

open Classical in
private theorem algConn_le_two_of_sigma_cross_pair_hsideV : ∀ {V : Type u_1} [Fintype V] (G
  : SimpleGraph V)
  (u v h h' : V) (_ : ∀ (w : V), 3 ≤ G.degree w) (_ : ¬G.Adj u v) (_ : G.Adj u h) (_ : G.Adj
    v h')
  (_ : ∀ w ∈ G.neighborFinset u, ∀ w' ∈ G.neighborFinset v, G.Adj w w' → w = h ∧ w' = h')
  (_ : sigS G v + 1 / ((G.degree h' : ℝ) - 2) ≤ 2),
  let cA : ℝ := 1 + ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2);
  let cB : ℝ := 1 + ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2);
  ∀ (_ : h ∈ G.neighborFinset u) (_ : h' ∈ G.neighborFinset v)
    (_ :
      (∑ w ∈ G.neighborFinset u,
          ∑ w' ∈ G.neighborFinset v,
            if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2) + cA / ((G.degree w' : ℝ) - 2)) ^ 2
              else 0) ≤
        (cB / ((G.degree h : ℝ) - 2) + cA / ((G.degree h' : ℝ) - 2)) ^ 2)
    (_ : G.Adj h h'),
    ∑ w ∈ G.neighborFinset v, (cA - cA / ((G.degree w : ℝ) - 2)) ^ 2 +
        ∑ w ∈ G.neighborFinset v,
          ↑(#(G.neighborFinset w \ insert v (G.neighborFinset u))) * (cA / ((G.degree w : ℝ) - 2))
            ^ 2 ≤
      cA ^ 2 * sigS G v + 2 * ∑ w ∈ G.neighborFinset v, (cA / ((G.degree w : ℝ) - 2)) ^ 2 -
        (cA / ((G.degree h' : ℝ) - 2)) ^ 2 := by
  classical
  intro V inst G u v h h' h3 huv hh hh' hcross1 hsv cA cB hhN hh'N hcrossle hhh'
  have hpt : ∀ w ∈ G.neighborFinset v,
      (cA - cA / ((G.degree w : ℝ) - 2)) ^ 2
        + ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
          * (cA / ((G.degree w : ℝ) - 2)) ^ 2
      ≤ cA ^ 2 * sigma (G.degree w)
        + 2 * (cA / ((G.degree w : ℝ) - 2)) ^ 2
        - (if w = h' then (cA / ((G.degree w : ℝ) - 2)) ^ 2 else 0) := by
    intro w hw
    have hadj_vw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    by_cases hwh : w = h'
    · subst hwh
      rw [ite_eq_left rfl]
      have hsharp := sigma_slot_le_sharp G h3 cA v (G.neighborFinset u)
        w h hadj_vw (G.adj_symm hhh') hhN
        (fun hc => huv (hc ▸ (G.adj_symm hh)).symm)
      linarith
    · rw [ite_eq_right hwh]
      have hgen := sigma_slot_le G h3 cA v (G.neighborFinset u) w hadj_vw
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hrhs : ∑ w ∈ G.neighborFinset v,
      (cA ^ 2 * sigma (G.degree w)
        + 2 * (cA / ((G.degree w : ℝ) - 2)) ^ 2
        - (if w = h' then (cA / ((G.degree w : ℝ) - 2)) ^ 2 else 0))
      = cA ^ 2 * sigS G v
        + 2 * ∑ w ∈ G.neighborFinset v, (cA / ((G.degree w : ℝ) - 2)) ^ 2
        - (cA / ((G.degree h' : ℝ) - 2)) ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sigS]
    congr 1
    rw [Finset.sum_ite_eq' (G.neighborFinset v) h']
    exact ite_eq_left hh'N
  rw [hrhs] at hsum
  linarith

open Classical in
private theorem algConn_le_two_of_sigma_cross_pair_hkey : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v h h' : V) (_ : sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2) (_ : sigS G v + 1 /
    ((G.degree h' : ℝ) - 2) ≤ 2),
  let cA : ℝ := 1 + ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2);
  let cB : ℝ := 1 + ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2);
  ∀ (_ : 0 < 1 / ((G.degree h : ℝ) - 2)) (_ : 0 < 1 / ((G.degree h' : ℝ) - 2)) (_ : 1 /
    ((G.degree h : ℝ) - 2) ≤ 1)
    (_ : 1 / ((G.degree h' : ℝ) - 2) ≤ 1),
    (cB / ((G.degree h : ℝ) - 2) + cA / ((G.degree h' : ℝ) - 2)) ^ 2 - (cB / ((G.degree h : ℝ) -
      2)) ^ 2 -
            (cA / ((G.degree h' : ℝ) - 2)) ^ 2 +
          cB ^ 2 * sigS G u +
        cA ^ 2 * sigS G v ≤
      2 * cB ^ 2 + 2 * cA ^ 2 := by
  classical
  intro V inst G u v h h' hsu hsv cA cB hsh hsh' hsh1 hsh'1
  have e1 : cB / ((G.degree h : ℝ) - 2)
      = cB * (1 / ((G.degree h : ℝ) - 2)) := by ring
  have e2 : cA / ((G.degree h' : ℝ) - 2)
      = cA * (1 / ((G.degree h' : ℝ) - 2)) := by ring
  rw [e1, e2]
  set s := 1 / ((G.degree h : ℝ) - 2)
  set s' := 1 / ((G.degree h' : ℝ) - 2)
  have hs1 : cB ^ 2 * sigS G u ≤ cB ^ 2 * (2 - s) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg cB)
  have hs2 : cA ^ 2 * sigS G v ≤ cA ^ 2 * (2 - s') :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg cA)
  have hs2le : s ^ 2 ≤ s := by nlinarith only [hsh, hsh1]
  have hs'2le : s' ^ 2 ≤ s' := by nlinarith only [hsh', hsh'1]
  have hcross2 : 2 * (cB * s) * (cA * s') ≤ cB ^ 2 * s + cA ^ 2 * s' := by
    nlinarith only [sq_nonneg (cB * s - cA * s'),
      mul_le_mul_of_nonneg_left hs2le (sq_nonneg cB),
      mul_le_mul_of_nonneg_left hs'2le (sq_nonneg cA)]
  nlinarith only [hs1, hs2, hcross2]

open Classical in
/-- **LAW B — the σ-cross law.**  Two non-adjacent vertices with no common
neighbour whose only cross edge can be `(h, h′)` (`h ∈ N(u)`, `h′ ∈ N(v)`),
with the σ-slack conditions `sigS u + 1/(deg h − 2) ≤ 2` and
`sigS v + 1/(deg h′ − 2) ≤ 2`, certify `algConn ≤ 2`.  The master's leak set
discounts the cross edge at `h` and `h′`, leaving exactly the cross cost
`2·p_h·q_{h′} ≤ cB²s_h + cA²s_{h′}`, which the slack absorbs. -/
theorem algConn_le_two_of_sigma_cross_pair [Nonempty V]
    (G : SimpleGraph V) (u v h h' : V)
    (h3 : ∀ w, 3 ≤ G.degree w) (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hh : G.Adj u h) (hh' : G.Adj v h')
    (hcross1 : ∀ w ∈ G.neighborFinset u, ∀ w' ∈ G.neighborFinset v,
      G.Adj w w' → w = h ∧ w' = h')
    (hsu : sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2)
    (hsv : sigS G v + 1 / ((G.degree h' : ℝ) - 2) ≤ 2) :
    algConn G ≤ 2 := by
  classical
  set cA : ℝ := 1 + ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2) with hcA
  set cB : ℝ := 1 + ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2) with hcB
  have hDpos : ∀ w : V, (0 : ℝ) < (G.degree w : ℝ) - 2 := by
    intro w
    have : (3 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast h3 w
    linarith
  have hterm_nonneg : ∀ w : V, (0 : ℝ) ≤ 1 / ((G.degree w : ℝ) - 2) :=
    fun w => le_of_lt (div_pos one_pos (hDpos w))
  have hcA1 : (1 : ℝ) ≤ cA := by
    rw [hcA]
    have : (0 : ℝ) ≤ ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2) :=
      Finset.sum_nonneg fun w _ => hterm_nonneg w
    linarith
  have hcB1 : (1 : ℝ) ≤ cB := by
    rw [hcB]
    have : (0 : ℝ) ≤ ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2) :=
      Finset.sum_nonneg fun w _ => hterm_nonneg w
    linarith
  have hcA0 : (0 : ℝ) < cA := by linarith
  have hcB0 : (0 : ℝ) < cB := by linarith
  have hhN : h ∈ G.neighborFinset u := (G.mem_neighborFinset u h).mpr hh
  have hh'N : h' ∈ G.neighborFinset v := (G.mem_neighborFinset v h').mpr hh'
  refine algConn_le_two_of_weighted_double_star G u v cB cA
    (fun w => cB / ((G.degree w : ℝ) - 2))
    (fun w => cA / ((G.degree w : ℝ) - 2))
    hne huv hcap hcB0
    (fun w _ => le_of_lt (div_pos hcB0 (hDpos w)))
    (fun w _ => le_of_lt (div_pos hcA0 (hDpos w)))
    ?_ ?_
  · -- balance
    have h1 : ∑ w ∈ G.neighborFinset u, cB / ((G.degree w : ℝ) - 2)
        = cB * ∑ w ∈ G.neighborFinset u, 1 / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ G.neighborFinset v, cA / ((G.degree w : ℝ) - 2)
        = cA * ∑ w ∈ G.neighborFinset v, 1 / ((G.degree w : ℝ) - 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [h1, h2, hcA, hcB]
    ring
  · -- the quadratic-form certificate
    -- abbreviations for the two crossing weights
    have hph : cB / ((G.degree h : ℝ) - 2) = cB * (1 / ((G.degree h : ℝ) - 2)) := by
      ring
    -- the cross sum is at most the single crossing term
    have hcrossle :=
        algConn_le_two_of_sigma_cross_pair_hcrossle (V := V) (G := G) (u := u) (v := v) (h :=
          h) (h' := h') (hh) (hh') (hcross1) (hsu) (hsv) (hhN) (hh'N) (hph)
    -- side sums, with the sharp slot at the crossing vertices when `h ~ h'`
    by_cases hhh' : G.Adj h h'
    · -- sharp slots at `h` and `h'`
      have hsideU :=
          algConn_le_two_of_sigma_cross_pair_hsideU (V := V) (G := G) (u := u) (v := v) (h :=
            h) (h' := h') (h3) (huv) (hh) (hh') (hcross1) (hsu) (hhN) (hh'N) (hph) (hcrossle) (hhh')
      have hsideV :=
          algConn_le_two_of_sigma_cross_pair_hsideV (V := V) (G := G) (u := u) (v := v) (h :=
            h) (h' := h') (h3) (huv) (hh) (hh') (hcross1) (hsv) (hhN) (hh'N) (hcrossle) (hhh')
      -- assemble: the slack absorbs the cross cost
      have hsh : (0 : ℝ) < 1 / ((G.degree h : ℝ) - 2) := div_pos one_pos (hDpos h)
      have hsh' : (0 : ℝ) < 1 / ((G.degree h' : ℝ) - 2) :=
        div_pos one_pos (hDpos h')
      have hsh1 : 1 / ((G.degree h : ℝ) - 2) ≤ 1 := by
        rw [div_le_one (hDpos h)]
        have : (3 : ℝ) ≤ (G.degree h : ℝ) := by exact_mod_cast h3 h
        linarith
      have hsh'1 : 1 / ((G.degree h' : ℝ) - 2) ≤ 1 := by
        rw [div_le_one (hDpos h')]
        have : (3 : ℝ) ≤ (G.degree h' : ℝ) := by exact_mod_cast h3 h'
        linarith
      have hkey :=
          algConn_le_two_of_sigma_cross_pair_hkey (V := V) (G := G) (u := u) (v := v) (h := h)
            (h' := h') (hsu) (hsv) (hsh) (hsh') (hsh1) (hsh'1)
      linarith only [hsideU, hsideV, hcrossle, hkey]
    · -- no cross edge at all: generic slots and zero cross sum suffice
      have hcross0 : ∑ w ∈ G.neighborFinset u, ∑ w' ∈ G.neighborFinset v,
          (if G.Adj w w' then (cB / ((G.degree w : ℝ) - 2)
            + cA / ((G.degree w' : ℝ) - 2)) ^ 2 else 0) = 0 := by
        refine Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun w' hw' => ?_
        refine ite_eq_right fun hadj => ?_
        obtain ⟨rfl, rfl⟩ := hcross1 w hw w' hw' hadj
        exact hhh' hadj
      have hsideU : ∑ w ∈ G.neighborFinset u,
          ((cB - cB / ((G.degree w : ℝ) - 2)) ^ 2)
          + ∑ w ∈ G.neighborFinset u,
            ((G.neighborFinset w \ insert u (G.neighborFinset v)).card : ℝ)
              * (cB / ((G.degree w : ℝ) - 2)) ^ 2
          ≤ cB ^ 2 * sigS G u
            + 2 * ∑ w ∈ G.neighborFinset u, (cB / ((G.degree w : ℝ) - 2)) ^ 2 := by
        have hsum := Finset.sum_le_sum (fun w hw =>
          sigma_slot_le G h3 cB u (G.neighborFinset v) w
            ((G.mem_neighborFinset u w).mp hw))
        rw [Finset.sum_add_distrib] at hsum
        have hrhs : ∑ w ∈ G.neighborFinset u,
            (cB ^ 2 * sigma (G.degree w)
              + 2 * (cB / ((G.degree w : ℝ) - 2)) ^ 2)
            = cB ^ 2 * sigS G u
              + 2 * ∑ w ∈ G.neighborFinset u, (cB / ((G.degree w : ℝ) - 2)) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sigS]
        rw [hrhs] at hsum
        linarith
      have hsideV : ∑ w ∈ G.neighborFinset v,
          ((cA - cA / ((G.degree w : ℝ) - 2)) ^ 2)
          + ∑ w ∈ G.neighborFinset v,
            ((G.neighborFinset w \ insert v (G.neighborFinset u)).card : ℝ)
              * (cA / ((G.degree w : ℝ) - 2)) ^ 2
          ≤ cA ^ 2 * sigS G v
            + 2 * ∑ w ∈ G.neighborFinset v, (cA / ((G.degree w : ℝ) - 2)) ^ 2 := by
        have hsum := Finset.sum_le_sum (fun w hw =>
          sigma_slot_le G h3 cA v (G.neighborFinset u) w
            ((G.mem_neighborFinset v w).mp hw))
        rw [Finset.sum_add_distrib] at hsum
        have hrhs : ∑ w ∈ G.neighborFinset v,
            (cA ^ 2 * sigma (G.degree w)
              + 2 * (cA / ((G.degree w : ℝ) - 2)) ^ 2)
            = cA ^ 2 * sigS G v
              + 2 * ∑ w ∈ G.neighborFinset v, (cA / ((G.degree w : ℝ) - 2)) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sigS]
        rw [hrhs] at hsum
        linarith
      have hsu2 : cB ^ 2 * sigS G u ≤ cB ^ 2 * 2 := by
        have hsh : (0 : ℝ) < 1 / ((G.degree h : ℝ) - 2) :=
          div_pos one_pos (hDpos h)
        exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg cB)
      have hsv2 : cA ^ 2 * sigS G v ≤ cA ^ 2 * 2 := by
        have hsh' : (0 : ℝ) < 1 / ((G.degree h' : ℝ) - 2) :=
          div_pos one_pos (hDpos h')
        exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg cA)
      rw [hcross0]
      linarith [hsideU, hsideV, hsu2, hsv2]

end ACMax

/-! ## The unified σ-transfer (`c = 5/4`)

The supply bound behind `β = 105/128`. Partition each heavy vertex `w`
(degree `d ≥ 5`) into `a₃` degree-3 twins, `f` degree-4 and `j` heavy neighbours
(σ-mass `S_w`), so `sigS w = f/2 + S_w`. The transfer inequality
`σ(d)·(a₃ + j) ≤ (5/4)(d − 4) + S_w` charges `σ(d)` per heavy neighbour and
refunds the σ-mass received; summed over heavies the transfer terms cancel
identically, leaving `Σ σ(d)·a₃ ≤ (5/4)·X + exceptions`. It holds for every heavy
vertex except the `W₅` overflow (`1/12`, `sigma_transfer_w5`) and the SFB-capped
usable classes (`a₃ ≥ d − 2`, `5 ≤ d ≤ 15`). The per-degree certificates are
`(d−4)(d−6+2f) ≥ 0` (non-usable), a triple-gap tie at `d = 5, f = 0`, and
`(d−16)(d−2) ≥ 0` (saturated `d ≥ 16`). -/

namespace ACMax

open Finset

variable {n : ℕ}

/-! ## σ set-sum bounds -/

open Classical in
/-- Any set of heavy σ-values has sum at least `(2/3)·card`. -/
theorem sigma_setsum_ge_free (G : SimpleGraph (Fin n)) (K : Finset (Fin n))
    (hK : ∀ x ∈ K, 5 ≤ G.degree x) :
    (2 / 3 : ℝ) * (K.card : ℝ) ≤ ∑ x ∈ K, sigma (G.degree x) := by
  calc (2 / 3 : ℝ) * (K.card : ℝ) = ∑ _x ∈ K, (2 / 3 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ K, sigma (G.degree x) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have := sigma_mono (by norm_num : 3 ≤ 5) (hK x hx)
        rw [sigma_five] at this
        linarith

open Classical in
/-- Any set of σ-values (degrees ≥ 3) has sum at most `card`. -/
theorem sigma_setsum_le_card (G : SimpleGraph (Fin n)) (K : Finset (Fin n))
    (hK : ∀ x ∈ K, 3 ≤ G.degree x) :
    ∑ x ∈ K, sigma (G.degree x) ≤ (K.card : ℝ) := by
  calc ∑ x ∈ K, sigma (G.degree x) ≤ ∑ _x ∈ K, (1 : ℝ) :=
        Finset.sum_le_sum fun x hx => (sigma_lt_one (hK x hx)).le
    _ = (K.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

open Classical in
/-- **The set triple gap**: a set of heavy σ-values summing strictly above `2`
sums to at least `25/12`.  Either every member has degree 5 — then the sum is
`(2/3)·card > 2`, forcing `card ≥ 4` and sum `≥ 8/3` — or some member has
degree ≥ 6, contributing `≥ 3/4` on top of `≥ 2/3` from each of the `≥ 2`
others. -/
theorem sigma_setsum_triple_gap (G : SimpleGraph (Fin n)) (K : Finset (Fin n))
    (hK : ∀ x ∈ K, 5 ≤ G.degree x)
    (h2 : (2 : ℝ) < ∑ x ∈ K, sigma (G.degree x)) :
    (25 / 12 : ℝ) ≤ ∑ x ∈ K, sigma (G.degree x) := by
  have hcard3 : 3 ≤ K.card := by
    by_contra hcon
    have hle : ∑ x ∈ K, sigma (G.degree x) ≤ (K.card : ℝ) :=
      sigma_setsum_le_card G K (fun x hx => by have := hK x hx; omega)
    have : (K.card : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (by omega)
    linarith
  by_cases hall5 : ∀ x ∈ K, G.degree x = 5
  · -- all degree 5: sum = (2/3)·card > 2 forces card ≥ 4
    have hsum : ∑ x ∈ K, sigma (G.degree x) = (2 / 3 : ℝ) * (K.card : ℝ) := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [hall5 x hx, sigma_five]),
        Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcard4 : 4 ≤ K.card := by
      by_contra hcon
      have h3 : K.card = 3 := by omega
      rw [hsum, h3] at h2
      norm_num at h2
    have : (4 : ℝ) ≤ (K.card : ℝ) := by exact_mod_cast hcard4
    rw [hsum]
    linarith
  · -- some member has degree ≥ 6
    simp only [not_forall] at hall5
    obtain ⟨x, hxK, hx5⟩ := hall5
    have hx6 : 6 ≤ G.degree x := by have := hK x hxK; omega
    have hσx : (3 / 4 : ℝ) ≤ sigma (G.degree x) := by
      have := sigma_mono (by norm_num : 3 ≤ 6) hx6
      rw [sigma_six] at this
      linarith
    have hrest : (2 / 3 : ℝ) * ((K.erase x).card : ℝ)
        ≤ ∑ y ∈ K.erase x, sigma (G.degree y) :=
      sigma_setsum_ge_free G _ (fun y hy => hK y (Finset.mem_of_mem_erase hy))
    have hcarde : (K.erase x).card = K.card - 1 := Finset.card_erase_of_mem hxK
    have hcard2 : 2 ≤ (K.erase x).card := by omega
    have hcard2R : (2 : ℝ) ≤ ((K.erase x).card : ℝ) := by exact_mod_cast hcard2
    have hsplit : ∑ y ∈ K, sigma (G.degree y)
        = sigma (G.degree x) + ∑ y ∈ K.erase x, sigma (G.degree y) :=
      (Finset.add_sum_erase K _ hxK).symm
    rw [hsplit]
    linarith

/-! ## The neighbourhood profile of a heavy vertex -/

open Classical in
/-- The degree-partition of a neighbourhood: with minimum degree 3, the twins,
the degree-4 neighbours, and the heavy neighbours partition `N(w)`. -/
theorem nbr_profile_partition (G : SimpleGraph (Fin n)) (w : Fin n)
    (h3 : ∀ v, 3 ≤ G.degree v) :
    (hubTwins G w).card
      + ((G.neighborFinset w).filter (fun u => G.degree u = 4)).card
      + ((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card
      = G.degree w := by
  classical
  have h1 : (hubTwins G w).card
      = ((G.neighborFinset w).filter (fun u => G.degree u = 3)).card := by
    congr 1
    ext v
    rw [mem_hubTwins_iff, Finset.mem_filter, G.mem_neighborFinset]
  have h2 : ((G.neighborFinset w).filter (fun u => G.degree u = 3)).card
      + ((G.neighborFinset w).filter (fun u => ¬ G.degree u = 3)).card
      = (G.neighborFinset w).card :=
    Finset.card_filter_add_card_filter_not _
  have h3' : ((G.neighborFinset w).filter (fun u => ¬ G.degree u = 3)).card
      = ((G.neighborFinset w).filter (fun u => G.degree u = 4)).card
        + ((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
      (fun u hu4 hu5 => by
        simp only [Finset.mem_filter] at hu4 hu5
        omega))]
    · congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨huN, hne⟩
        have := h3 u
        rcases Nat.lt_or_ge (G.degree u) 5 with h | h
        · exact Or.inl ⟨huN, by omega⟩
        · exact Or.inr ⟨huN, h⟩
      · rintro (⟨huN, h4⟩ | ⟨huN, h5⟩)
        · exact ⟨huN, by omega⟩
        · exact ⟨huN, by omega⟩
  rw [h1, ← SimpleGraph.card_neighborFinset_eq_degree, ← h2, h3']
  ring

open Classical in
/-- The σ-sum decomposition: `sigS w = f/2 + S_w` (twins contribute `σ(3) = 0`,
degree-4 neighbours `1/2` each). -/
theorem sigS_decomp (G : SimpleGraph (Fin n)) (w : Fin n)
    (h3 : ∀ v, 3 ≤ G.degree v) :
    sigS G w
      = (1 / 2 : ℝ)
          * (((G.neighborFinset w).filter (fun u => G.degree u = 4)).card : ℝ)
        + ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u) := by
  classical
  rw [sigS]
  rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset w)
    (fun u => 5 ≤ G.degree u) (fun u => sigma (G.degree u))]
  rw [add_comm]
  congr 1
  -- non-heavy part: degree 3 gives 0, degree 4 gives 1/2
  rw [← Finset.sum_filter_add_sum_filter_not
    ((G.neighborFinset w).filter (fun u => ¬ 5 ≤ G.degree u))
    (fun u => G.degree u = 4) (fun u => sigma (G.degree u))]
  have hz : ∑ u ∈ ((G.neighborFinset w).filter
      (fun u => ¬ 5 ≤ G.degree u)).filter (fun u => ¬ G.degree u = 4),
      sigma (G.degree u) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    simp only [Finset.mem_filter] at hu
    have := h3 u
    have hu3 : G.degree u = 3 := by omega
    rw [hu3, sigma_three]
  have hf : ∑ u ∈ ((G.neighborFinset w).filter
      (fun u => ¬ 5 ≤ G.degree u)).filter (fun u => G.degree u = 4),
      sigma (G.degree u)
      = (1 / 2 : ℝ)
        * (((G.neighborFinset w).filter (fun u => G.degree u = 4)).card : ℝ) := by
    have hset : ((G.neighborFinset w).filter
        (fun u => ¬ 5 ≤ G.degree u)).filter (fun u => G.degree u = 4)
        = (G.neighborFinset w).filter (fun u => G.degree u = 4) := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hN, -⟩, h4⟩
        exact ⟨hN, h4⟩
      · rintro ⟨hN, h4⟩
        exact ⟨⟨hN, by omega⟩, h4⟩
    rw [hset]
    rw [Finset.sum_congr rfl (fun u hu => by
      rw [(Finset.mem_filter.mp hu).2, sigma_four])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hz, hf, add_zero]

/-! ## The pointwise transfer inequalities -/

open Classical in
/-- **Saturated cap** (`d ≥ 16`): `σ(d)·d ≤ (5/4)(d−4)` —
certificate `(d−16)(d−2) ≥ 0`. -/
theorem sigma_transfer_sat {d : ℕ} (hd : 16 ≤ d) :
    sigma d * (d : ℝ) ≤ (5 / 4 : ℝ) * ((d : ℝ) - 4) := by
  have hdR : (16 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  rw [sigma, div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) - 16 by linarith)
    (show (0 : ℝ) ≤ (d : ℝ) - 2 by linarith)]

open Classical in
/-- **The non-usable transfer** (suppressed heavy vertices): if `deg w = d ≥ 5`
and `sigS w > 2`, then `σ(d)(a₃ + j) ≤ (5/4)(d−4) + S_w`.  The real relaxation
`S_w > 2 − f/2` gives the certificate `(d−4)(d−6+2f) ≥ 0` except at
`d = 5, f = 0`, where the triple gap `S_w ≥ 25/12` makes the exact tie
`10/3 = 5/4 + 25/12`. -/
theorem sigma_transfer_nonusable (G : SimpleGraph (Fin n)) (w : Fin n)
    (h3 : ∀ v, 3 ≤ G.degree v) (hd : 5 ≤ G.degree w) (hs : 2 < sigS G w) :
    sigma (G.degree w) * (((hubTwins G w).card : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      ≤ (5 / 4 : ℝ) * ((G.degree w : ℝ) - 4)
        + ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u) := by
  classical
  have hpart := nbr_profile_partition G w h3
  have hdecomp := sigS_decomp G w h3
  set d := G.degree w with hd_def
  set f := ((G.neighborFinset w).filter (fun u => G.degree u = 4)).card with hf_def
  set S := ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
    sigma (G.degree u) with hS_def
  -- `a₃ + j = d − f` as reals
  have haj : ((hubTwins G w).card : ℝ)
      + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ)
      = (d : ℝ) - (f : ℝ) := by
    have h1R : ((hubTwins G w).card : ℝ) + (f : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ)
        = (d : ℝ) := by exact_mod_cast hpart
    linarith
  rw [haj]
  have hSgt : (2 : ℝ) - (1 / 2 : ℝ) * (f : ℝ) < S := by
    rw [hdecomp] at hs
    linarith
  by_cases hcase : d = 5 ∧ f = 0
  · -- the exact tie: `S > 2` over a set of heavy σ-values ⟹ `S ≥ 25/12`
    obtain ⟨hd5, hf0⟩ := hcase
    have hS2 : (2 : ℝ) < S := by
      rw [hf0] at hSgt
      push_cast at hSgt
      linarith
    have hS25 : (25 / 12 : ℝ) ≤ S :=
      sigma_setsum_triple_gap G _ (fun x hx => (Finset.mem_filter.mp hx).2) hS2
    rw [hd5, hf0, sigma_five]
    push_cast
    linarith
  · -- real relaxation: certificate `(d−4)(d−6+2f) ≥ 0`
    have hdfR : (0 : ℝ) ≤ ((d : ℝ) - 4) * ((d : ℝ) - 6 + 2 * (f : ℝ)) := by
      have hd5R : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      rcases Nat.lt_or_ge d 6 with h | h
      · -- d = 5, so f ≥ 1
        have hd5 : d = 5 := by omega
        have hf1 : 1 ≤ f := by
          rcases Nat.eq_zero_or_pos f with h0 | h1
          · exact absurd ⟨hd5, h0⟩ hcase
          · exact h1
        have hf1R : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf1
        rw [hd5]
        push_cast
        nlinarith
      · have h6R : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
        have hfR : (0 : ℝ) ≤ (f : ℝ) := by positivity
        nlinarith
    have hd5R : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
    rw [sigma, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [mul_pos hpos (show (0 : ℝ) < S - (2 - (1 / 2) * (f : ℝ)) by linarith)]

open Classical in
/-- **The usable transfer** (uncapped, non-`W₅`): if `deg w = d ≥ 5`,
`sigS w ≤ 2`, `a₃ ≤ d − 3`, and not (`d = 5` and `a₃ = 2`), then
`σ(d)(a₃ + j) ≤ (5/4)(d−4) + S_w`.  Uses `S_w ≥ (2/3)j` and `f + j ≥ 3`;
certificate `3(d−4)(d−6) + 4f(d−5) + 8j(d−5) ≥ 0` for `d ≥ 6`, while `d = 5`
degenerates to `j = 0, f ≥ 4` via `3f + 4j ≤ 12`. -/
theorem sigma_transfer_usable (G : SimpleGraph (Fin n)) (w : Fin n)
    (h3 : ∀ v, 3 ≤ G.degree v) (hd : 5 ≤ G.degree w) (hs : sigS G w ≤ 2)
    (ha : (hubTwins G w).card + 3 ≤ G.degree w)
    (hW5 : ¬(G.degree w = 5 ∧ (hubTwins G w).card = 2)) :
    sigma (G.degree w) * (((hubTwins G w).card : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      ≤ (5 / 4 : ℝ) * ((G.degree w : ℝ) - 4)
        + ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u) := by
  classical
  have hpart := nbr_profile_partition G w h3
  have hdecomp := sigS_decomp G w h3
  set d := G.degree w with hd_def
  set f := ((G.neighborFinset w).filter (fun u => G.degree u = 4)).card with hf_def
  set j := ((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card with hj_def
  set S := ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
    sigma (G.degree u) with hS_def
  have hSj : (2 / 3 : ℝ) * (j : ℝ) ≤ S := by
    rw [hS_def, hj_def]
    exact sigma_setsum_ge_free G _ (fun x hx => (Finset.mem_filter.mp hx).2)
  have hSle : (1 / 2 : ℝ) * (f : ℝ) + S ≤ 2 := by
    rw [hdecomp] at hs
    linarith
  have hfj3 : 3 ≤ f + j := by omega
  have haj : ((hubTwins G w).card : ℝ) + (j : ℝ) = (d : ℝ) - (f : ℝ) := by
    have h1R : ((hubTwins G w).card : ℝ) + (f : ℝ) + (j : ℝ) = (d : ℝ) := by
      exact_mod_cast hpart
    linarith
  rw [haj]
  rcases Nat.lt_or_ge d 6 with hd5' | hd6
  · -- `d = 5`: the class degenerates to `j = 0, 4 ≤ f`
    have hd5 : d = 5 := by omega
    have h3f4j : 3 * f + 4 * j ≤ 12 := by
      have : (3 : ℝ) * (f : ℝ) + 4 * (j : ℝ) ≤ 12 := by linarith
      exact_mod_cast this
    have ha2 : (hubTwins G w).card ≤ 2 := by omega
    have hane2 : (hubTwins G w).card ≠ 2 := fun h2 => hW5 ⟨hd5, h2⟩
    have hfj4 : 4 ≤ f + j := by omega
    have hj0 : j = 0 ∧ 4 ≤ f := by omega
    obtain ⟨hj0', hf4⟩ := hj0
    have hf4R : (4 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf4
    have hS0 : (0 : ℝ) ≤ S := by
      have := hSj
      rw [hj0'] at this
      push_cast at this
      linarith
    rw [hd5, sigma_five]
    push_cast
    linarith
  · -- `d ≥ 6`
    have hd6R : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
    have hfR : (0 : ℝ) ≤ (f : ℝ) := by positivity
    have hjR : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hfj3R : (3 : ℝ) ≤ (f : ℝ) + (j : ℝ) := by exact_mod_cast hfj3
    have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
    rw [sigma, div_mul_eq_mul_div, div_le_iff₀ hpos]
    -- goal: (d−3)(d−f) ≤ ((5/4)(d−4) + S)(d−2); use S ≥ (2/3)j, j ≥ 3−f
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) - 4 by linarith)
        (show (0 : ℝ) ≤ (d : ℝ) - 6 by linarith),
      mul_nonneg hfR (show (0 : ℝ) ≤ (d : ℝ) - 5 by linarith),
      mul_nonneg hjR (show (0 : ℝ) ≤ (d : ℝ) - 5 by linarith),
      mul_pos hpos (show (0 : ℝ) < (d : ℝ) - 2 by linarith),
      mul_le_mul_of_nonneg_right hSj (le_of_lt hpos)]

open Classical in
/-- **The `W₅` transfer with overflow `1/12`**: a usable degree-5 vertex with
exactly 2 twins satisfies the transfer inequality with an extra `1/12` —
exactly, in all four sub-profiles. -/
theorem sigma_transfer_w5 (G : SimpleGraph (Fin n)) (w : Fin n)
    (hd : G.degree w = 5)
    (ha : (hubTwins G w).card = 2) :
    sigma (G.degree w) * (((hubTwins G w).card : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      ≤ (5 / 4 : ℝ) * ((G.degree w : ℝ) - 4)
        + ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u)
        + 1 / 12 := by
  classical
  have hSj : (2 / 3 : ℝ)
      * ((((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      ≤ ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
          sigma (G.degree u) :=
    sigma_setsum_ge_free G _ (fun x hx => (Finset.mem_filter.mp hx).2)
  rw [hd, ha, sigma_five]
  push_cast
  linarith

/-! ## The extended capped-class count (`d ≤ 15`) -/

open Classical in
/-- The capped overflow is nonnegative for `d ≤ 15`. -/
theorem capped_overflow_nonneg {d : ℕ} (hd5 : 5 ≤ d) (hd15 : d ≤ 15) :
    (0 : ℝ) ≤ sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4) := by
  have hd5R : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd5
  have hd15R : (d : ℝ) ≤ 15 := by exact_mod_cast hd15
  have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  rw [sigma, div_mul_eq_mul_div, sub_nonneg, le_div_iff₀ hpos]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) - 5 by linarith)
    (show (0 : ℝ) ≤ 15 - (d : ℝ) by linarith)]

open Classical in
/-- The per-hub capped overflow is at most `25/12` (attained at `d = 5`). -/
theorem capped_overflow_le_max {d : ℕ} (hd5 : 5 ≤ d) (_hd15 : d ≤ 15) :
    sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4) ≤ 25 / 12 := by
  have hd5R : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd5
  have hpos : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  rw [sigma, div_mul_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ hpos]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) - 5 by linarith)
    (show (0 : ℝ) ≤ (d : ℝ) - 2 by linarith)]

open Classical in
/-- The collapsed capped-overflow grid: with the block law pinning every capped
class to `a = d − 2` exactly, `Σ_{d=5}^{15} (2d−1)·(σ(d)·d − (5/4)(d−4)) ≤ 205`. -/
theorem capped_overflow_grid_collapsed :
    ∑ d ∈ Finset.Icc 5 15, ((2 * d - 1 : ℕ) : ℝ)
        * (sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4)) ≤ 205 := by
  have hicc : Finset.Icc 5 15
      = ({5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} : Finset ℕ) := by decide
  rw [hicc]
  norm_num [Finset.sum_insert, Finset.mem_insert, sigma]

open Classical in
/-- **The capped overflow bound**: the capped classes overflow the `(5/4)`-rate
by total σ-mass at most `214 = 4·(25/12) + Σ (2d−1)·overflow(d)`. -/
theorem capped_overflow_le (n : ℕ) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hb : SeaFatBoundary G) (C : Finset (Fin n))
    (hC : ∀ w ∈ C, 5 ≤ G.degree w ∧ G.degree w ≤ 15
      ∧ G.degree w ≤ (hubTwins G w).card + 2)
    (hblk : ∀ w ∈ C, (hubTwins G w).card + 2 ≤ G.degree w)
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    ∑ w ∈ C, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
      ≤ 214 := by
  classical
  have hEcard := medge_endpoint_hub_card_le_four n G h huniq
  set E : Finset (Fin n) := Finset.univ.filter (fun g : Fin n =>
      4 ≤ G.degree g ∧
      ∃ t ∈ hubTwins G g, ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3) with hE
  set Q : Finset (Fin n) := C \ E with hQ
  have hterm0 : ∀ w ∈ C, (0 : ℝ) ≤ sigma (G.degree w) * ((G.degree w : ℝ))
      - (5 / 4) * ((G.degree w : ℝ) - 4) :=
    fun w hw => capped_overflow_nonneg (hC w hw).1 (hC w hw).2.1
  have hsplitC : ∑ w ∈ C, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
      = ∑ w ∈ C ∩ E, (sigma (G.degree w) * ((G.degree w : ℝ))
          - (5 / 4) * ((G.degree w : ℝ) - 4))
        + ∑ w ∈ C \ E, (sigma (G.degree w) * ((G.degree w : ℝ))
          - (5 / 4) * ((G.degree w : ℝ) - 4)) := by
    have hs := Finset.sum_filter_add_sum_filter_not C (fun w => w ∈ E)
      (fun w => sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
    rw [Finset.filter_mem_eq_inter] at hs
    have hsd : C.filter (fun w => w ∉ E) = C \ E :=
      (Finset.sdiff_eq_filter C E).symm
    rw [hsd] at hs
    linarith [hs]
  have hMpart : ∑ w ∈ C ∩ E, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
      ≤ 4 * (25 / 12) := by
    calc ∑ w ∈ C ∩ E, (sigma (G.degree w) * ((G.degree w : ℝ))
          - (5 / 4) * ((G.degree w : ℝ) - 4))
        ≤ ∑ _w ∈ C ∩ E, (25 / 12 : ℝ) :=
          Finset.sum_le_sum fun w hw =>
            capped_overflow_le_max
              (hC w (Finset.mem_of_mem_inter_left hw)).1
              (hC w (Finset.mem_of_mem_inter_left hw)).2.1
      _ = ((C ∩ E).card : ℝ) * (25 / 12) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * (25 / 12) := by
          have h1 : (C ∩ E).card ≤ 4 :=
            le_trans (Finset.card_le_card Finset.inter_subset_right) hEcard
          have h1R : ((C ∩ E).card : ℝ) ≤ 4 := by exact_mod_cast h1
          nlinarith
  have hQmx : ∀ g ∈ Q, ∀ g' ∈ Q, g ≠ g' → mCross G g g' = 0 := by
    intro g hg g' _ _
    by_contra hmx
    obtain ⟨t, ht, t', ht', hadj⟩ :=
      exists_cross_edge_of_mCross_ne_zero G g g' hmx
    obtain ⟨hgt, ht3, -⟩ := privTwins_spec.mp ht
    obtain ⟨-, ht'3, -⟩ := privTwins_spec.mp ht'
    rw [hQ, Finset.mem_sdiff] at hg
    refine hg.2 ?_
    rw [hE, Finset.mem_filter]
    have h5 := (hC g hg.1).1
    exact ⟨Finset.mem_univ g,
      by omega, t, mem_hubTwins_iff.mpr ⟨hgt, ht3⟩, t', hadj, ht'3⟩
  have hQd : ∀ d, 5 ≤ d → d ≤ 15 →
      (Q.filter (fun g => G.degree g = d)).card ≤ 2 * d - 1 := by
    intro d hd5 hd15
    have hsubd : Q.filter (fun g => G.degree g = d)
        ⊆ (Finset.Icc (d - 2) (d - 2)).biUnion (fun a =>
          Q.filter (fun g => G.degree g = d ∧ (hubTwins G g).card = a)) := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have hgC : g ∈ C := by
        have := hg.1
        rw [hQ, Finset.mem_sdiff] at this
        exact this.1
      obtain ⟨-, -, hle2⟩ := hC g hgC
      have hblk' := hblk g hgC
      rw [Finset.mem_biUnion]
      refine ⟨(hubTwins G g).card, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hg.1, hg.2, rfl⟩
    have hclass : ∀ a ∈ Finset.Icc (d - 2) (d - 2),
        (Q.filter (fun g => G.degree g = d ∧ (hubTwins G g).card = a)).card
          ≤ 1 + d + a := by
      intro a ha
      obtain ⟨had2, had⟩ := Finset.mem_Icc.mp ha
      have hTmem : ∀ g ∈ Q.filter
          (fun g => G.degree g = d ∧ (hubTwins G g).card = a),
          4 ≤ G.degree g ∧ intDeg G g ≤ d - a ∧ (hubTwins G g).card = a := by
        intro g hg
        rw [Finset.mem_filter] at hg
        obtain ⟨hgQ, hgd, hga⟩ := hg
        have hgC : g ∈ C := by
          rw [hQ, Finset.mem_sdiff] at hgQ
          exact hgQ.1
        obtain ⟨h5, -, hle2⟩ := hC g hgC
        have hsum := card_hubTwins_add_intDeg G g
        exact ⟨by omega, by omega, hga⟩
      have hTmx : ∀ g ∈ Q.filter
          (fun g => G.degree g = d ∧ (hubTwins G g).card = a),
          ∀ g' ∈ Q.filter
            (fun g => G.degree g = d ∧ (hubTwins G g).card = a),
          g ≠ g' → mCross G g g' = 0 := by
        intro g hg g' hg' hne
        exact hQmx g (Finset.mem_of_mem_filter _ hg)
          g' (Finset.mem_of_mem_filter _ hg') hne
      have hcap := class_cap_with_adj n G hb a (d - a) (by omega) _ hTmem hTmx
      omega
    calc (Q.filter (fun g => G.degree g = d)).card
        ≤ ∑ a ∈ Finset.Icc (d - 2) (d - 2),
            (Q.filter (fun g =>
              G.degree g = d ∧ (hubTwins G g).card = a)).card :=
          (Finset.card_le_card hsubd).trans Finset.card_biUnion_le
      _ ≤ ∑ a ∈ Finset.Icc (d - 2) (d - 2), (1 + d + a) :=
          Finset.sum_le_sum hclass
      _ ≤ 2 * d - 1 := by
          rw [Finset.Icc_self, Finset.sum_singleton]
          omega
  have hQpart : ∑ w ∈ Q, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
      ≤ ∑ d ∈ Finset.Icc 5 15, ((2 * d - 1 : ℕ) : ℝ)
          * (sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4)) := by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 5 15 : Finset ℕ))
        (fun d => Q.filter (fun g => G.degree g = d)) := by
      refine fun d₁ _ d₂ _ hne => Finset.disjoint_left.mpr fun g hg₁ hg₂ => ?_
      rw [Finset.mem_filter] at hg₁ hg₂
      exact hne (hg₁.2 ▸ hg₂.2)
    have hQsub : Q ⊆ (Finset.Icc 5 15).biUnion
        (fun d => Q.filter (fun g => G.degree g = d)) := by
      intro g hg
      have hgC : g ∈ C := by
        have := hg
        rw [hQ, Finset.mem_sdiff] at this
        exact this.1
      obtain ⟨h5, h15, -⟩ := hC g hgC
      exact Finset.mem_biUnion.mpr ⟨G.degree g, Finset.mem_Icc.mpr ⟨h5, h15⟩,
        Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
    calc ∑ w ∈ Q, (sigma (G.degree w) * ((G.degree w : ℝ))
          - (5 / 4) * ((G.degree w : ℝ) - 4))
        ≤ ∑ w ∈ (Finset.Icc 5 15).biUnion
            (fun d => Q.filter (fun g => G.degree g = d)),
            (sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hQsub fun w hw _ => ?_
          obtain ⟨d, hd, hwd⟩ := Finset.mem_biUnion.mp hw
          rw [Finset.mem_filter] at hwd
          obtain ⟨hd5, hd15⟩ := Finset.mem_Icc.mp hd
          exact capped_overflow_nonneg (hwd.2 ▸ hd5) (hwd.2 ▸ hd15)
      _ = ∑ d ∈ Finset.Icc 5 15, ∑ w ∈ Q.filter (fun g => G.degree g = d),
            (sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4)) :=
          Finset.sum_biUnion hdisj
      _ ≤ ∑ d ∈ Finset.Icc 5 15, ((2 * d - 1 : ℕ) : ℝ)
            * (sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hd5, hd15⟩ := Finset.mem_Icc.mp hd
          have hval : ∀ w ∈ Q.filter (fun g => G.degree g = d),
              sigma (G.degree w) * ((G.degree w : ℝ))
                - (5 / 4) * ((G.degree w : ℝ) - 4)
              = sigma d * (d : ℝ) - (5 / 4) * ((d : ℝ) - 4) := by
            intro w hw
            rw [(Finset.mem_filter.mp hw).2]
          rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
          have hov := capped_overflow_nonneg hd5 hd15
          have hcard := hQd d hd5 hd15
          have hcardR : ((Q.filter (fun g => G.degree g = d)).card : ℝ)
              ≤ ((2 * d - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcardR hov
  have hgrid := capped_overflow_grid_collapsed
  rw [hsplitC]
  have hQC : ∑ w ∈ C \ E, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4))
      = ∑ w ∈ Q, (sigma (G.degree w) * ((G.degree w : ℝ))
        - (5 / 4) * ((G.degree w : ℝ) - 4)) := by rw [hQ]
  rw [hQC]
  nlinarith [hMpart, hQpart, hgrid]

/-! ## The exchange identity and the summed transfer -/

open Classical in
/-- **The σ-exchange identity**: over the heavy set, paying `σ(d_w)` per heavy
neighbour equals receiving the neighbours' σ-mass — both sides count ordered
heavy-heavy adjacencies. -/
theorem sigma_exchange (G : SimpleGraph (Fin n)) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
        sigma (G.degree w)
          * ((((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      = ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
          ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u) := by
  classical
  set H := Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w) with hH
  have hset : ∀ w : Fin n, (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)
      = H.filter (fun u => G.Adj w u) := by
    intro w
    ext u
    rw [hH]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact and_comm
  calc ∑ w ∈ H, sigma (G.degree w)
        * ((((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      = ∑ w ∈ H, ∑ u ∈ H, (if G.Adj w u then sigma (G.degree w) else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hset w, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ u ∈ H, ∑ w ∈ H, (if G.Adj w u then sigma (G.degree w) else 0) :=
        Finset.sum_comm
    _ = ∑ w ∈ H, ∑ u ∈ H, (if G.Adj u w then sigma (G.degree u) else 0) := rfl
    _ = ∑ w ∈ H, ∑ u ∈ H, (if G.Adj w u then sigma (G.degree u) else 0) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
        rw [G.adj_comm]
    _ = ∑ w ∈ H, ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
          sigma (G.degree u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hset w]
        exact (Finset.sum_filter _ _).symm

open Classical in
/-- **The summed σ-transfer** (`c = 5/4`): on the boundary of the compact cell,

  `Σ_{deg w ≥ 5} σ(deg w)·|hubTwins w| ≤ (5/4)·X + (1/12)·N₅ + 214`,

where `N₅` counts the usable degree-5 hubs with exactly two twins (`W₅`) and
`862` charges the capped classes only their OVERFLOW beyond the `(5/4)`-rate
(`capped_overflow_le`) — their base `(5/4)(d−4)` share rides in the `X`-term.  The transfer terms
cancel
exactly via `sigma_exchange`. -/
theorem sigma_transfer_sum (n : ℕ) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hb : SeaFatBoundary G)
    (hblk : ∀ w : Fin n, 5 ≤ G.degree w → G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w)
    (_hml : ∀ z : Fin n, G.degree z ≤ 4 →
      ((G.neighborFinset z).filter (fun t => G.degree t = 3)).card
        ≤ G.degree z - 2)
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
        sigma (G.degree w) * ((hubTwins G w).card : ℝ)
      ≤ (5 / 4 : ℝ) * (excessX n G : ℝ)
        + (1 / 12 : ℝ) * ((Finset.univ.filter (fun w : Fin n =>
            G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)).card : ℝ)
        + 214 := by
  classical
  have h3 := h.min_degree
  set H := Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w) with hH
  -- the pointwise master bound with both overflow indicators
  have hpt : ∀ w ∈ H,
      sigma (G.degree w) * (((hubTwins G w).card : ℝ)
          + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
        ≤ (5 / 4 : ℝ) * ((G.degree w : ℝ) - 4)
          + (∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
              sigma (G.degree u))
          + ((if G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
              then (1 / 12 : ℝ) else 0)
            + (if G.degree w ≤ 15 ∧ G.degree w ≤ (hubTwins G w).card + 2
              then sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4) else 0)) := by
    intro w hw
    have hw5 : 5 ≤ G.degree w := by
      rw [hH] at hw
      exact (Finset.mem_filter.mp hw).2
    have hw5R : (5 : ℝ) ≤ (G.degree w : ℝ) := by exact_mod_cast hw5
    have hS0 : (0 : ℝ) ≤ ∑ u ∈ (G.neighborFinset w).filter
        (fun u => 5 ≤ G.degree u), sigma (G.degree u) :=
      Finset.sum_nonneg fun u hu =>
        sigma_nonneg (by have := (Finset.mem_filter.mp hu).2; omega)
    have hd40 : (0 : ℝ) ≤ (5 / 4 : ℝ) * ((G.degree w : ℝ) - 4) := by linarith
    have hite1 : (0 : ℝ) ≤ (if G.degree w = 5 ∧ sigS G w ≤ 2
        ∧ (hubTwins G w).card = 2 then (1 / 12 : ℝ) else 0) := by
      split <;> norm_num
    have hite2 : (0 : ℝ) ≤ (if G.degree w ≤ 15
        ∧ G.degree w ≤ (hubTwins G w).card + 2
        then sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4) else 0) := by
      split
      · next hcap => exact capped_overflow_nonneg hw5 hcap.1
      · norm_num
    have hpartw := nbr_profile_partition G w h3
    have hajd : ((hubTwins G w).card : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ)
        ≤ (G.degree w : ℝ) := by
      have : (hubTwins G w).card
          + ((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card
          ≤ G.degree w := by omega
      exact_mod_cast this
    have hσ0 : (0 : ℝ) ≤ sigma (G.degree w) := sigma_nonneg (by omega)
    by_cases hcap : G.degree w ≤ 15 ∧ G.degree w ≤ (hubTwins G w).card + 2
    · -- capped class: charged its exact delivery `σ·d`
      have h1 : sigma (G.degree w) * (((hubTwins G w).card : ℝ)
          + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
          ≤ sigma (G.degree w) * (G.degree w : ℝ) :=
        mul_le_mul_of_nonneg_left hajd hσ0
      rw [ite_eq_left hcap]
      linarith
    · by_cases hus : 2 < sigS G w
      · have := sigma_transfer_nonusable G w h3 hw5 hus
        linarith
      · have husle : sigS G w ≤ 2 := le_of_not_gt hus
        by_cases h16 : 16 ≤ G.degree w
        · have h1 : sigma (G.degree w) * (((hubTwins G w).card : ℝ)
              + (((G.neighborFinset w).filter
                  (fun u => 5 ≤ G.degree u)).card : ℝ))
              ≤ sigma (G.degree w) * (G.degree w : ℝ) :=
            mul_le_mul_of_nonneg_left hajd hσ0
          have h2 := sigma_transfer_sat h16
          linarith
        · have ha3 : (hubTwins G w).card + 3 ≤ G.degree w := by omega
          by_cases hW5 : G.degree w = 5 ∧ (hubTwins G w).card = 2
          · have := sigma_transfer_w5 G w hW5.1 hW5.2
            rw [ite_eq_left ⟨hW5.1, husle, hW5.2⟩]
            linarith
          · have := sigma_transfer_usable G w h3 hw5 husle ha3 hW5
            linarith
  have hsum := Finset.sum_le_sum hpt
  -- distribute both sides
  have hLHS : ∑ w ∈ H, sigma (G.degree w) * (((hubTwins G w).card : ℝ)
        + (((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ))
      = ∑ w ∈ H, sigma (G.degree w) * ((hubTwins G w).card : ℝ)
        + ∑ w ∈ H, sigma (G.degree w)
          * ((((G.neighborFinset w).filter (fun u => 5 ≤ G.degree u)).card : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hRHS : ∑ w ∈ H, ((5 / 4 : ℝ) * ((G.degree w : ℝ) - 4)
        + (∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u))
        + ((if G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            then (1 / 12 : ℝ) else 0)
          + (if G.degree w ≤ 15 ∧ G.degree w ≤ (hubTwins G w).card + 2
            then sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4) else 0)))
      = (5 / 4 : ℝ) * (∑ w ∈ H, ((G.degree w : ℝ) - 4))
        + (∑ w ∈ H, ∑ u ∈ (G.neighborFinset w).filter (fun u => 5 ≤ G.degree u),
            sigma (G.degree u))
        + ((∑ w ∈ H, (if G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            then (1 / 12 : ℝ) else 0))
          + ∑ w ∈ H, (if G.degree w ≤ 15 ∧ G.degree w ≤ (hubTwins G w).card + 2
            then sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4) else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  -- the excess cast
  have hX : (excessX n G : ℝ) = ∑ w ∈ H, ((G.degree w : ℝ) - 4) := by
    rw [excessX, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h5 : 5 ≤ G.degree w := (Finset.mem_filter.mp hw).2
    have h4 : 4 ≤ G.degree w := by omega
    rw [Nat.cast_sub h4]
    norm_num
  -- the W₅ indicator sums to the W₅ count
  have hW5sum : ∑ w ∈ H, (if G.degree w = 5 ∧ sigS G w ≤ 2
        ∧ (hubTwins G w).card = 2 then (1 / 12 : ℝ) else 0)
      = (1 / 12 : ℝ) * ((Finset.univ.filter (fun w : Fin n =>
          G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)).card : ℝ) := by
    have hfeq : H.filter (fun w => G.degree w = 5 ∧ sigS G w ≤ 2
          ∧ (hubTwins G w).card = 2)
        = Finset.univ.filter (fun w : Fin n => G.degree w = 5 ∧ sigS G w ≤ 2
          ∧ (hubTwins G w).card = 2) := by
      rw [hH, Finset.filter_filter]
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hp⟩
        exact hp
      · rintro ⟨h5, hs, ha⟩
        exact ⟨by omega, h5, hs, ha⟩
    rw [← Finset.sum_filter, hfeq, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- the capped indicator sums to the overflow bound `862`
  have hcapsum : ∑ w ∈ H, (if G.degree w ≤ 15
        ∧ G.degree w ≤ (hubTwins G w).card + 2
        then sigma (G.degree w) * ((G.degree w : ℝ))
              - (5 / 4) * ((G.degree w : ℝ) - 4) else 0)
      ≤ 214 := by
    rw [← Finset.sum_filter]
    refine capped_overflow_le n G h hb _ (fun w hw => ?_) (fun w hw => ?_) huniq
    · rw [Finset.mem_filter, hH, Finset.mem_filter] at hw
      exact ⟨hw.1.2, hw.2.1, hw.2.2⟩
    · rw [Finset.mem_filter, hH, Finset.mem_filter] at hw
      exact hblk w hw.1.2 hw.2.1
  -- the exchange cancels the transfer terms
  have hexch := sigma_exchange G
  rw [← hH] at hexch
  rw [hLHS, hRHS] at hsum
  rw [← hX] at hsum
  linarith [hsum, hexch, hW5sum, hcapsum]

/-! ## The `W₅ᵇ` cloud bound

`W₅ᵇ` — usable degree-5 hubs with two twins and a big neighbour — is the sole
class obstructing `β < 7/8`; it is bounded by a two-round pair coverage driven by
the σ-laws. Each member has neighbourhood `{h, ≤4, ≤4, 3, 3}` with `deg h ≥ 9` the
unique non-light neighbour (`w5big_structure`), so LAW A / LAW B fire at side-σ
exactly `1` / slack `1/(deg h − 2)`. Unless a σ-law fires, every member pair has a
light-endpoint common neighbour or cross (`w5big_pair_mechanism`), each big hub
carrying `≤ 269` members (`w5big_cloud_le`), giving `|W₅ᵇ| ≤ 5441`
(`w5big_card_le`). -/

open Classical in
/-- The `W₅ᵇ` class: usable degree-5 hubs with exactly two twins and a big
neighbour. -/
noncomputable def w5big (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun w : Fin n =>
    G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
      ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)

open Classical in
/-- **Structure of a `W₅ᵇ` member**: a unique big neighbour `h`, every other
neighbour light, and `sigS = 1 + σ(deg h)` exactly. -/
theorem w5big_structure (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (u : Fin n) (hu : u ∈ w5big G) :
    ∃ h, G.Adj u h ∧ 9 ≤ G.degree h
      ∧ (∀ x ∈ G.neighborFinset u, x ≠ h → G.degree x ≤ 4)
      ∧ sigS G u = 1 + sigma (G.degree h) := by
  classical
  rw [w5big, Finset.mem_filter] at hu
  obtain ⟨-, hd5, hsig, ha2, x, hxN, hx9⟩ := hu
  have hpart := nbr_profile_partition G u h3
  have hdecomp := sigS_decomp G u h3
  set H := (G.neighborFinset u).filter (fun w => 5 ≤ G.degree w) with hH
  set F := (G.neighborFinset u).filter (fun w => G.degree w = 4) with hF
  have hxH : x ∈ H := by
    rw [hH, Finset.mem_filter]
    exact ⟨hxN, by omega⟩
  have hσx : (6 / 7 : ℝ) ≤ sigma (G.degree x) := by
    have := sigma_mono (by norm_num : 3 ≤ 9) hx9
    have h9v : sigma 9 = 6 / 7 := by norm_num [sigma]
    linarith
  have hj1 : H.card = 1 := by
    by_contra hcon
    have hj2 : 2 ≤ H.card := by
      have : 1 ≤ H.card := Finset.card_pos.mpr ⟨x, hxH⟩
      omega
    have hj3 : H.card ≤ 3 := by omega
    -- σ-mass of the heavy filter: `≥ σ(x) + (2/3)(j−1)`
    have hfree := sigma_setsum_ge_free G (H.erase x)
      (fun y hy => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)).2)
    have hcarde : (H.erase x).card = H.card - 1 := Finset.card_erase_of_mem hxH
    have hcardeR : ((H.erase x).card : ℝ) = (H.card : ℝ) - 1 := by
      rw [hcarde]
      have : 1 ≤ H.card := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hsplit : ∑ w ∈ H, sigma (G.degree w)
        = sigma (G.degree x) + ∑ w ∈ H.erase x, sigma (G.degree w) :=
      (Finset.add_sum_erase H _ hxH).symm
    -- the degree-4 count as a real
    have hfnat : F.card + H.card = 3 := by omega
    have hfR : (F.card : ℝ) = 3 - (H.card : ℝ) := by
      have : F.card = 3 - H.card := by omega
      rw [this]
      have : H.card ≤ 3 := hj3
      push_cast [Nat.cast_sub this]
      ring
    have hjR : (2 : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hj2
    rw [hdecomp] at hsig
    rw [hcardeR] at hfree
    -- `2 ≥ (3−j)/2 + 6/7 + (2/3)(j−1) = 71/42 + j/6 ≥ 85/42` — contradiction
    rw [hsplit] at hsig
    rw [hfR] at hsig
    linarith
  -- the heavy filter is exactly `{x}`
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hj1
  have hax : a = x := by
    have := hxH
    rw [ha, Finset.mem_singleton] at this
    exact this.symm
  rw [hax] at ha
  refine ⟨x, (G.mem_neighborFinset u x).mp hxN, hx9, ?_, ?_⟩
  · intro y hyN hyx
    by_contra hcon
    have hyH : y ∈ H := by
      rw [hH, Finset.mem_filter]
      exact ⟨hyN, by omega⟩
    rw [ha, Finset.mem_singleton] at hyH
    exact hyx hyH
  · have hf2 : F.card = 2 := by omega
    rw [hdecomp]
    rw [ha, Finset.sum_singleton, hf2]
    norm_num

open Classical in
/-- Mid-degree vertices (degree 5–8) carry no `W₅ᵇ` members. -/
theorem w5big_no_mid_inc (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (w : Fin n) (h5 : 5 ≤ G.degree w) (h8 : G.degree w ≤ 8) :
    G.neighborFinset w ∩ w5big G = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  rw [Finset.mem_inter] at hu
  obtain ⟨h, -, hbig, hlight, -⟩ := w5big_structure G h3 u hu.2
  have hwN : w ∈ G.neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu.1.symm
  by_cases hwh : w = h
  · rw [hwh] at h8
    omega
  · have := hlight w hwN hwh
    omega

open Classical in
/-- Every vertex carries at most `K + 4` members, given the big-hub cap `K`. -/
theorem w5big_inc_le (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (K : ℕ) (hK : ∀ w : Fin n, 9 ≤ G.degree w →
      (G.neighborFinset w ∩ w5big G).card ≤ K) (y : Fin n) :
    (G.neighborFinset y ∩ w5big G).card ≤ K + 4 := by
  classical
  by_cases hbig : 9 ≤ G.degree y
  · exact le_trans (hK y hbig) (Nat.le_add_right K 4)
  by_cases h5 : 5 ≤ G.degree y
  · rw [w5big_no_mid_inc G h3 y h5 (by omega)]
    simp
  · calc (G.neighborFinset y ∩ w5big G).card
        ≤ (G.neighborFinset y).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree y := G.card_neighborFinset_eq_degree y
      _ ≤ K + 4 := by omega

open Classical in
/-- Per-member light-neighbour count: at most `4`. -/
theorem w5big_light_nbrs_le (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (u : Fin n) (hu : u ∈ w5big G) :
    ((G.neighborFinset u).filter (fun w => G.degree w ≤ 4)).card ≤ 4 := by
  classical
  obtain ⟨h, hadj, hbig, -, -⟩ := w5big_structure G h3 u hu
  have hhN : h ∈ G.neighborFinset u := (G.mem_neighborFinset u h).mpr hadj
  have hsub : (G.neighborFinset u).filter (fun w => G.degree w ≤ 4)
      ⊆ (G.neighborFinset u).erase h := by
    intro z hz
    rw [Finset.mem_filter] at hz
    refine Finset.mem_erase.mpr ⟨?_, hz.1⟩
    intro hzh
    rw [hzh] at hz
    omega
  have hu5 : G.degree u = 5 := by
    rw [w5big, Finset.mem_filter] at hu
    exact hu.2.1
  calc ((G.neighborFinset u).filter (fun w => G.degree w ≤ 4)).card
      ≤ ((G.neighborFinset u).erase h).card := Finset.card_le_card hsub
    _ = G.degree u - 1 := by
        rw [Finset.card_erase_of_mem hhN, G.card_neighborFinset_eq_degree]
    _ ≤ 4 := by omega

open Classical in
/-- Per-member big-neighbour count: exactly one, so at most `1`. -/
theorem w5big_big_nbrs_le_one (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (u : Fin n) (hu : u ∈ w5big G) :
    ((G.neighborFinset u).filter (fun w => 9 ≤ G.degree w)).card ≤ 1 := by
  classical
  obtain ⟨h, -, -, hlight, -⟩ := w5big_structure G h3 u hu
  have hsub : (G.neighborFinset u).filter (fun w => 9 ≤ G.degree w) ⊆ {h} := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_singleton]
    by_contra hzh
    have := hlight z hz.1 hzh
    omega
  calc ((G.neighborFinset u).filter (fun w => 9 ≤ G.degree w)).card
      ≤ ({h} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton h

open Classical in
/-- Subset light-slot exchange: for `T ⊆ W₅ᵇ` and any class `S` of degree-≤8
vertices, `Σ_{w ∈ S} |N(w) ∩ T| ≤ 4·|T|`. -/
theorem w5big_light_slots_le' (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (T : Finset (Fin n)) (hT : T ⊆ w5big G)
    (S : Finset (Fin n)) (hS : ∀ w ∈ S, G.degree w ≤ 8) :
    ∑ w ∈ S, (G.neighborFinset w ∩ T).card ≤ 4 * T.card := by
  classical
  rw [sum_nbr_inter_comm G S T]
  calc ∑ u ∈ T, (G.neighborFinset u ∩ S).card
      ≤ ∑ _u ∈ T, 4 := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨h, hadj, hbig, -, -⟩ := w5big_structure G h3 u (hT hu)
        have hhN : h ∈ G.neighborFinset u := (G.mem_neighborFinset u h).mpr hadj
        have hsub : G.neighborFinset u ∩ S ⊆ (G.neighborFinset u).erase h := by
          intro z hz
          rw [Finset.mem_inter] at hz
          refine Finset.mem_erase.mpr ⟨?_, hz.1⟩
          intro hzh
          have := hS z hz.2
          rw [hzh] at this
          omega
        have hu5 : G.degree u = 5 := by
          have := hT hu
          rw [w5big, Finset.mem_filter] at this
          exact this.2.1
        calc (G.neighborFinset u ∩ S).card
            ≤ ((G.neighborFinset u).erase h).card := Finset.card_le_card hsub
          _ = G.degree u - 1 := by
              rw [Finset.card_erase_of_mem hhN, G.card_neighborFinset_eq_degree]
          _ ≤ 4 := by omega
    _ = 4 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring

open Classical in
/-- The law hypotheses of a member at its big hub: `sigS ≤ 1 + σ(deg h)`
(the erase-free LAW A side condition) and the LAW B slack
`sigS + 1/(deg h − 2) ≤ 2`. -/
theorem w5big_law_hypotheses (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (u h : Fin n) (hu : u ∈ w5big G)
    (hadj : G.Adj u h) (hbig : 9 ≤ G.degree h) :
    sigS G u ≤ 1 + sigma (G.degree h)
      ∧ sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2 := by
  classical
  obtain ⟨h₀, hadj₀, hbig₀, hlight₀, hsig₀⟩ := w5big_structure G h3 u hu
  have hhh₀ : h = h₀ := by
    by_contra hne
    have := hlight₀ h ((G.mem_neighborFinset u h).mpr hadj) hne
    omega
  subst hhh₀
  constructor
  · rw [hsig₀]
  · have hD : (0 : ℝ) < (G.degree h : ℝ) - 2 := by
      have : (9 : ℝ) ≤ (G.degree h : ℝ) := by exact_mod_cast hbig
      linarith
    have hone : sigma (G.degree h) + 1 / ((G.degree h : ℝ) - 2) = 1 := by
      rw [sigma]
      field_simp
      ring
    rw [hsig₀]
    linarith

end ACMax

namespace ACMax

open Finset

section GenericV

variable {V : Type*} [Fintype V]

open Classical in
/-- **The σ-law firing configuration**: either a LAW A apex configuration or
a LAW B cross configuration exists (stated erase-free: the LAW A side
condition is `sigS ≤ 1 + σ(deg g)` and the no-cross condition is pure
adjacency). -/
def W5LawConfig (G : SimpleGraph V) : Prop :=
  (∃ u v g : V, u ≠ v ∧ ¬G.Adj u v ∧ G.Adj u g ∧ G.Adj v g
    ∧ (∀ w : V, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w))
    ∧ (∀ w w' : V, G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g → ¬G.Adj w w')
    ∧ sigS G u ≤ 1 + sigma (G.degree g)
    ∧ sigS G v ≤ 1 + sigma (G.degree g))
  ∨ (∃ u v h h' : V, u ≠ v ∧ ¬G.Adj u v
    ∧ (∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    ∧ G.Adj u h ∧ G.Adj v h'
    ∧ (∀ w w' : V, G.Adj u w → G.Adj v w' → G.Adj w w' → w = h ∧ w' = h')
    ∧ sigS G u + 1 / ((G.degree h : ℝ) - 2) ≤ 2
    ∧ sigS G v + 1 / ((G.degree h' : ℝ) - 2) ≤ 2)

open Classical in
/-- A firing configuration closes the conjecture. -/
theorem w5LawConfig_closes [Nonempty V] (G : SimpleGraph V)
    (h3 : ∀ v, 3 ≤ G.degree v) (hcfg : W5LawConfig G) : algConn G ≤ 2 := by
  classical
  rcases hcfg with ⟨u, v, g, hne, huv, hgu, hgv, hcap, hnc, hsu, hsv⟩ |
    ⟨u, v, h, h', hne, huv, hcap, hh, hh', hcross1, hsu, hsv⟩
  · have hgN : g ∈ G.neighborFinset u := (G.mem_neighborFinset u g).mpr hgu
    have hgN' : g ∈ G.neighborFinset v := (G.mem_neighborFinset v g).mpr hgv
    refine algConn_le_two_of_sigma_apex_pair G u v g h3 hne huv hgu hgv hcap ?_ ?_ ?_
    · intro w hw w' hw'
      obtain ⟨hwg, hwN⟩ := Finset.mem_erase.mp hw
      obtain ⟨hw'g, hw'N⟩ := Finset.mem_erase.mp hw'
      exact hnc w w' ((G.mem_neighborFinset u w).mp hwN) hwg
        ((G.mem_neighborFinset v w').mp hw'N) hw'g
    · have hsplit : sigS G u = sigma (G.degree g)
          + ∑ w ∈ (G.neighborFinset u).erase g, sigma (G.degree w) := by
        rw [sigS]
        exact (Finset.add_sum_erase _ _ hgN).symm
      linarith [hsplit ▸ hsu]
    · have hsplit : sigS G v = sigma (G.degree g)
          + ∑ w ∈ (G.neighborFinset v).erase g, sigma (G.degree w) := by
        rw [sigS]
        exact (Finset.add_sum_erase _ _ hgN').symm
      linarith [hsplit ▸ hsv]
  · refine algConn_le_two_of_sigma_cross_pair G u v h h' h3 hne huv hcap hh hh'
      ?_ hsu hsv
    intro w hw w' hw' hadj
    exact hcross1 w w' ((G.mem_neighborFinset u w).mp hw)
      ((G.mem_neighborFinset v w').mp hw') hadj

end GenericV

variable {n : ℕ}

open Classical in
/-- Members are pairwise non-adjacent. -/
theorem w5big_not_adj (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (u v : Fin n) (hu : u ∈ w5big G) (hv : v ∈ w5big G) : ¬G.Adj u v := by
  intro hadj
  obtain ⟨h, -, hbig, hlight, -⟩ := w5big_structure G h3 u hu
  have hv5 : G.degree v = 5 := by
    rw [w5big, Finset.mem_filter] at hv
    exact hv.2.1
  have hvN : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
  by_cases hvh : v = h
  · rw [hvh] at hv5
    omega
  · have := hlight v hvN hvh
    omega

open Classical in
/-- **The global pair mechanism**: unless a σ-law fires, every member pair
has a common neighbour or a cross edge with a light endpoint. -/
theorem w5big_pair_mechanism (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v)
    (hnofire : ¬W5LawConfig G) (u v : Fin n)
    (hu : u ∈ w5big G) (hv : v ∈ w5big G) (hne : u ≠ v) :
    (∃ w, G.Adj u w ∧ G.Adj v w) ∨
    (∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
      (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)) := by
  classical
  have husig : sigS G u ≤ 2 := by
    rw [w5big, Finset.mem_filter] at hu
    exact hu.2.2.1
  have hvsig : sigS G v ≤ 2 := by
    rw [w5big, Finset.mem_filter] at hv
    exact hv.2.2.1
  have hnadj : ¬G.Adj u v := w5big_not_adj G h3 u v hu hv
  by_cases hcom : ∃ w, G.Adj u w ∧ G.Adj v w
  · exact Or.inl hcom
  push Not at hcom
  by_cases hlx : ∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
      (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)
  · exact Or.inr hlx
  push Not at hlx
  -- neither: assemble a LAW B configuration and contradict `hnofire`
  exfalso
  obtain ⟨hU, hUadj, hUbig, hUlight, -⟩ := w5big_structure G h3 u hu
  obtain ⟨hV, hVadj, hVbig, hVlight, -⟩ := w5big_structure G h3 v hv
  refine hnofire (Or.inr ⟨u, v, hU, hV, hne, hnadj,
    fun w hw => hcom w hw.1 hw.2, hUadj, hVadj, ?_, ?_, ?_⟩)
  · intro w w' hwadj hw'adj hadj
    have hwN : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hwadj
    have hw'N : w' ∈ G.neighborFinset v := (G.mem_neighborFinset v w').mpr hw'adj
    have hwl := hlx w w' hwadj hw'adj hadj
    constructor
    · by_contra hwh
      have := hUlight w hwN hwh
      omega
    · by_contra hwh
      have := hVlight w' hw'N hwh
      omega
  · exact (w5big_law_hypotheses G h3 u hU hu hUadj hUbig).2
  · exact (w5big_law_hypotheses G h3 v hV hv hVadj hVbig).2

open Classical in
/-- **The same-cloud pair mechanism**: unless a σ-law fires, every pair
sharing the big hub `h` has a *light* common neighbour or a cross edge with
*both* endpoints light. -/
theorem w5big_cloud_pair_mechanism (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (hnofire : ¬W5LawConfig G)
    (h : Fin n) (hbig : 9 ≤ G.degree h) (u v : Fin n)
    (hu : u ∈ G.neighborFinset h ∩ w5big G)
    (hv : v ∈ G.neighborFinset h ∩ w5big G) (hne : u ≠ v) :
    (∃ w, G.Adj u w ∧ G.Adj v w ∧ G.degree w ≤ 4) ∨
    (∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
      G.degree w ≤ 4 ∧ G.degree w' ≤ 4) := by
  classical
  rw [Finset.mem_inter] at hu hv
  have hUadj : G.Adj u h := G.adj_symm ((G.mem_neighborFinset h u).mp hu.1)
  have hVadj : G.Adj v h := G.adj_symm ((G.mem_neighborFinset h v).mp hv.1)
  obtain ⟨hU, hUadj', hUbig, hUlight, -⟩ := w5big_structure G h3 u hu.2
  obtain ⟨hV, hVadj', hVbig, hVlight, -⟩ := w5big_structure G h3 v hv.2
  have hnadj : ¬G.Adj u v := w5big_not_adj G h3 u v hu.2 hv.2
  by_cases hlc : ∃ w, G.Adj u w ∧ G.Adj v w ∧ G.degree w ≤ 4
  · exact Or.inl hlc
  push Not at hlc
  by_cases hllx : ∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
      G.degree w ≤ 4 ∧ G.degree w' ≤ 4
  · exact Or.inr hllx
  push Not at hllx
  -- neither: assemble a LAW A configuration at the apex `h`
  exfalso
  have hUh : hU = h := by
    by_contra hUh'
    have := hUlight h ((G.mem_neighborFinset u h).mpr hUadj) (Ne.symm hUh')
    omega
  have hVh : hV = h := by
    by_contra hVh'
    have := hVlight h ((G.mem_neighborFinset v h).mpr hVadj) (Ne.symm hVh')
    omega
  refine hnofire (Or.inl ⟨u, v, h, hne, hnadj, hUadj, hVadj, ?_, ?_, ?_, ?_⟩)
  · -- no second common neighbour
    intro w hwh hw
    have hwN : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hw.1
    have hwlight : G.degree w ≤ 4 := by
      by_cases hwhU : w = hU
      · -- `w` would be `u`'s big hub, but `w ≠ h` and the big hub is unique;
        -- since `h` is a big neighbour of `u`, `hU = h`, contradiction
        exfalso
        have hUh : hU = h := by
          by_contra hUh
          have := hUlight h ((G.mem_neighborFinset u h).mpr hUadj) (Ne.symm hUh)
          omega
        rw [hwhU, hUh] at hwh
        exact hwh rfl
      · exact hUlight w hwN hwhU
    exact absurd hwlight (by
      have := hlc w hw.1 hw.2
      omega)
  · -- no crosses between the punctured neighbourhoods (erase-free form)
    intro w w' hwadj hwne hw'adj hw'ne hadj
    have hwN : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hwadj
    have hw'N : w' ∈ G.neighborFinset v := (G.mem_neighborFinset v w').mpr hw'adj
    have hwl : G.degree w ≤ 4 := by
      refine hUlight w hwN ?_
      rw [hUh]
      exact hwne
    have hw'l : G.degree w' ≤ 4 := by
      refine hVlight w' hw'N ?_
      rw [hVh]
      exact hw'ne
    have := hllx w w' hwadj hw'adj hadj hwl
    omega
  · exact (w5big_law_hypotheses G h3 u h hu.2 hUadj hbig).1
  · exact (w5big_law_hypotheses G h3 v h hv.2 hVadj hbig).1

open Classical in
/-- A `W₅ᵇ` member has at most `2` degree-4 neighbours: its five slots are one
big vertex, exactly two degree-3 twins, and the rest. -/
theorem w5big_deg4_nbrs_le (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (u : Fin n) (hu : u ∈ w5big G) :
    ((G.neighborFinset u).filter (fun w => G.degree w = 4)).card ≤ 2 := by
  classical
  obtain ⟨h, huh, hh9, hlight, -⟩ := w5big_structure G h3 u hu
  have hu5 : G.degree u = 5 := by
    have := hu
    rw [w5big, Finset.mem_filter] at this
    exact this.2.1
  have ha2 : ((G.neighborFinset u).filter (fun w => G.degree w = 3)).card = 2 := by
    have h2 : (G.neighborFinset u).filter (fun w => G.degree w = 3)
        = hubTwins G u := by
      rw [hubTwins]
      ext t
      simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
    rw [h2]
    have := hu
    rw [w5big, Finset.mem_filter] at this
    exact this.2.2.2.1
  have hsub : (G.neighborFinset u).filter (fun w => G.degree w = 4)
      ⊆ ((G.neighborFinset u).erase h) \
        ((G.neighborFinset u).filter (fun w => G.degree w = 3)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_sdiff, Finset.mem_erase]
    refine ⟨⟨?_, hw.1⟩, ?_⟩
    · rintro rfl
      have := hw.2
      omega
    · rw [Finset.mem_filter]
      rintro ⟨-, h3'⟩
      have := hw.2
      omega
  have hhN : h ∈ G.neighborFinset u := (G.mem_neighborFinset u h).mpr huh
  have h3sub : (G.neighborFinset u).filter (fun w => G.degree w = 3)
      ⊆ (G.neighborFinset u).erase h := by
    intro w hw
    rw [Finset.mem_filter] at hw
    refine Finset.mem_erase.mpr ⟨?_, hw.1⟩
    rintro rfl
    omega
  calc ((G.neighborFinset u).filter (fun w => G.degree w = 4)).card
      ≤ (((G.neighborFinset u).erase h) \
          ((G.neighborFinset u).filter (fun w => G.degree w = 3))).card :=
        Finset.card_le_card hsub
    _ ≤ ((G.neighborFinset u).erase h).card
        - ((G.neighborFinset u).filter (fun w => G.degree w = 3)).card := by
        have h1 := Finset.card_sdiff_add_card_inter
          ((G.neighborFinset u).erase h)
          ((G.neighborFinset u).filter (fun w => G.degree w = 3))
        have h2 : (((G.neighborFinset u).erase h) ∩
            ((G.neighborFinset u).filter (fun w => G.degree w = 3))).card
            = ((G.neighborFinset u).filter (fun w => G.degree w = 3)).card := by
          rw [Finset.inter_eq_right.mpr h3sub]
        omega
    _ ≤ 2 := by
        rw [Finset.card_erase_of_mem hhN, G.card_neighborFinset_eq_degree,
          hu5, ha2]

open Classical in
/-- The weighted light-slot exchange: summing `(deg−1)·|N(w) ∩ T|` over light
vertices costs `2` per twin-slot and `3` per degree-4 slot — total `10|T|`. -/
theorem light_weighted_slots_le (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (T : Finset (Fin n)) (hT : T ⊆ w5big G) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4),
      (G.degree w - 1) * (G.neighborFinset w ∩ T).card ≤ 10 * T.card := by
  classical
  have hpartcomm : ∀ (d : ℕ),
      ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = d),
        (G.neighborFinset w ∩ T).card
      = ∑ u ∈ T, ((G.neighborFinset u).filter
          (fun w => G.degree w = d)).card := by
    intro d
    rw [sum_nbr_inter_comm G _ T]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      and_comm]
  have h3sum : ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 3),
      (G.neighborFinset w ∩ T).card ≤ 2 * T.card := by
    rw [hpartcomm 3]
    calc ∑ u ∈ T, ((G.neighborFinset u).filter
          (fun w => G.degree w = 3)).card
        ≤ ∑ _u ∈ T, 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          have h2 : (G.neighborFinset u).filter (fun w => G.degree w = 3)
              = hubTwins G u := by
            rw [hubTwins]
            ext w
            simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
          rw [h2]
          have := hT hu
          rw [w5big, Finset.mem_filter] at this
          omega
      _ = 2 * T.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  have h4sum : ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 4),
      (G.neighborFinset w ∩ T).card ≤ 2 * T.card := by
    rw [hpartcomm 4]
    calc ∑ u ∈ T, ((G.neighborFinset u).filter
          (fun w => G.degree w = 4)).card
        ≤ ∑ _u ∈ T, 2 := Finset.sum_le_sum fun u hu =>
          w5big_deg4_nbrs_le G h3 u (hT hu)
      _ = 2 * T.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4),
      (G.degree w - 1) * (G.neighborFinset w ∩ T).card
      = ∑ w ∈ (Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4)).filter
            (fun w => G.degree w = 3),
          (G.degree w - 1) * (G.neighborFinset w ∩ T).card
        + ∑ w ∈ (Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4)).filter
            (fun w => ¬G.degree w = 3),
          (G.degree w - 1) * (G.neighborFinset w ∩ T).card :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 3),
          2 * (G.neighborFinset w ∩ T).card
        + ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 4),
          3 * (G.neighborFinset w ∩ T).card := by
        refine Nat.add_le_add ?_ ?_
        · calc ∑ w ∈ (Finset.univ.filter
              (fun w : Fin n => G.degree w ≤ 4)).filter
                (fun w => G.degree w = 3),
              (G.degree w - 1) * (G.neighborFinset w ∩ T).card
              = ∑ w ∈ (Finset.univ.filter
                  (fun w : Fin n => G.degree w ≤ 4)).filter
                    (fun w => G.degree w = 3),
                2 * (G.neighborFinset w ∩ T).card := by
                refine Finset.sum_congr rfl fun w hw => ?_
                rw [Finset.mem_filter] at hw
                rw [hw.2]
            _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 3),
                2 * (G.neighborFinset w ∩ T).card := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                  (fun _ _ _ => Nat.zero_le _)
                intro w hw
                rw [Finset.mem_filter, Finset.mem_filter] at hw
                rw [Finset.mem_filter]
                exact ⟨Finset.mem_univ w, hw.2⟩
        · calc ∑ w ∈ (Finset.univ.filter
              (fun w : Fin n => G.degree w ≤ 4)).filter
                (fun w => ¬G.degree w = 3),
              (G.degree w - 1) * (G.neighborFinset w ∩ T).card
              = ∑ w ∈ (Finset.univ.filter
                  (fun w : Fin n => G.degree w ≤ 4)).filter
                    (fun w => ¬G.degree w = 3),
                3 * (G.neighborFinset w ∩ T).card := by
                refine Finset.sum_congr rfl fun w hw => ?_
                rw [Finset.mem_filter, Finset.mem_filter] at hw
                have h4 : G.degree w = 4 := by
                  have := h3 w
                  omega
                rw [h4]
            _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 4),
                3 * (G.neighborFinset w ∩ T).card := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                  (fun _ _ _ => Nat.zero_le _)
                intro w hw
                rw [Finset.mem_filter, Finset.mem_filter] at hw
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ w, ?_⟩
                have := h3 w
                omega
    _ = 2 * ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 3),
          (G.neighborFinset w ∩ T).card
        + 3 * ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w = 4),
          (G.neighborFinset w ∩ T).card := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (2 * T.card) + 3 * (2 * T.card) := by
        have := Nat.mul_le_mul_left 2 h3sum
        have := Nat.mul_le_mul_left 3 h4sum
        omega
    _ = 10 * T.card := by ring

open Classical in
/-- A `W₅ᵇ` member has **no** `w5big` neighbours: its neighbourhood is one big
vertex and four light ones, none of degree `5`. -/
theorem w5big_nbr_inter_self_empty (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) (u : Fin n) (hu : u ∈ w5big G) :
    G.neighborFinset u ∩ w5big G = ∅ := by
  classical
  obtain ⟨h, huh, hh9, hlight, -⟩ := w5big_structure G h3 u hu
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [Finset.mem_inter] at hy
  have hy5 : G.degree y = 5 := by
    have := hy.2
    rw [w5big, Finset.mem_filter] at this
    exact this.2.1
  by_cases hyh : y = h
  · rw [hyh] at hy5
    omega
  · have := hlight y hy.1 hyh
    omega

open Classical in
/-- Quadratic escape: `c(c−1) ≤ b·c` forces `c ≤ b + 1`. -/
theorem w5_quad {c b : ℕ} (h : c * (c - 1) ≤ b * c) : c ≤ b + 1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · omega
  · have h2 : (c - 1) * c ≤ b * c := by
      rw [Nat.mul_comm]
      exact h
    have := Nat.le_of_mul_le_mul_right h2 hc
    omega

open Classical in
private theorem w5big_cloud_le_hP3le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3
  ≤ G.degree v) (h : Fin n),
  let T := G.neighborFinset h ∩ w5big G;
  ∀ (_ : T ⊆ w5big G),
    let P3 := {p ∈ T.offDiag | ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧ G.degree w ≤ 4 ∧
      G.degree w' ≤ 4};
    ∀ (P : Finset (Fin n)) (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤
      4})
      (_ : ∀ x ∈ P, G.degree x ≤ 4) (_ : #({x ∈ P | G.degree x = 3}) ≤ 2 * #T)
      (_ : #({x ∈ P | ¬G.degree x = 3}) ≤ 2 * #T), #P3 ≤ 78 * #T := by
  classical
  intro n G h3 h T hTsub P3 P hPdef hPlight hP3c hP4c
  have hsub : P3 ⊆ P.biUnion (fun x =>
      ((G.neighborFinset x).filter (fun y => G.degree y ≤ 4)).biUnion (fun y =>
        (G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T))) := by
    intro p hp
    obtain ⟨hpd, w, w', hw, hw', hww', hw4, hw'4⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    have hwP : w ∈ P := by
      rw [hPdef]
      exact Finset.mem_biUnion.mpr ⟨p.1, hp1,
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p.1 w).mpr hw, hw4⟩⟩
    refine Finset.mem_biUnion.mpr ⟨w, hwP, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨w', Finset.mem_filter.mpr
      ⟨(G.mem_neighborFinset w w').mpr hww', hw'4⟩, ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩,
       Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩⟩
  have hnotT : ∀ z : Fin n, G.degree z ≤ 4 → z ∉ T := by
    intro z hz4 hzT
    have hz5 : G.degree z = 5 := by
      have := hTsub hzT
      rw [w5big, Finset.mem_filter] at this
      exact this.2.1
    omega
  have hcell : ∀ x ∈ P, ∀ y ∈ (G.neighborFinset x).filter
      (fun y => G.degree y ≤ 4),
      ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)).card
        ≤ (G.degree x - 1) * 3 := by
    intro x hx y hy
    rw [Finset.mem_filter] at hy
    have hyx : x ∈ G.neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset]
      exact G.adj_symm ((G.mem_neighborFinset x y).mp hy.1)
    have h1 : (G.neighborFinset x ∩ T).card ≤ G.degree x - 1 := by
      have hsub : G.neighborFinset x ∩ T ⊆ (G.neighborFinset x).erase y := by
        intro z hz
        rw [Finset.mem_inter] at hz
        refine Finset.mem_erase.mpr ⟨?_, hz.1⟩
        intro hzy
        exact hnotT y hy.2 (hzy ▸ hz.2)
      calc (G.neighborFinset x ∩ T).card
          ≤ ((G.neighborFinset x).erase y).card := Finset.card_le_card hsub
        _ = G.degree x - 1 := by
            rw [Finset.card_erase_of_mem hy.1, G.card_neighborFinset_eq_degree]
    have h2 : (G.neighborFinset y ∩ T).card ≤ 3 := by
      have hsub : G.neighborFinset y ∩ T ⊆ (G.neighborFinset y).erase x := by
        intro z hz
        rw [Finset.mem_inter] at hz
        refine Finset.mem_erase.mpr ⟨?_, hz.1⟩
        intro hzx
        exact hnotT x (hPlight x hx) (hzx ▸ hz.2)
      calc (G.neighborFinset y ∩ T).card
          ≤ ((G.neighborFinset y).erase x).card := Finset.card_le_card hsub
        _ = G.degree y - 1 := by
            rw [Finset.card_erase_of_mem hyx, G.card_neighborFinset_eq_degree]
        _ ≤ 3 := by
            have := hy.2
            omega
    rw [Finset.card_product]
    exact Nat.mul_le_mul h1 h2
  calc P3.card
      ≤ ∑ x ∈ P, (((G.neighborFinset x).filter
          (fun y => G.degree y ≤ 4)).biUnion (fun y =>
          (G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T))).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ x ∈ P, ∑ y ∈ (G.neighborFinset x).filter (fun y => G.degree y ≤ 4),
          ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)).card :=
        Finset.sum_le_sum fun x _ => Finset.card_biUnion_le
    _ ≤ ∑ x ∈ P, ∑ _y ∈ (G.neighborFinset x).filter (fun y => G.degree y ≤ 4),
          ((G.degree x - 1) * 3) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        exact hcell x hx y hy
    _ ≤ ∑ x ∈ P, (G.degree x - 1) * ((G.degree x - 1) * 3) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.sum_const, smul_eq_mul]
        obtain ⟨u, huT, hxu⟩ := Finset.mem_biUnion.mp (by
          rw [hPdef] at hx
          exact hx)
        have hu5 : G.degree u = 5 := by
          have := hTsub huT
          rw [w5big, Finset.mem_filter] at this
          exact this.2.1
        have huN : u ∈ G.neighborFinset x := by
          rw [SimpleGraph.mem_neighborFinset]
          exact ((G.mem_neighborFinset u x).mp
            (Finset.mem_of_mem_filter x hxu)).symm
        have hcard3 : ((G.neighborFinset x).filter
            (fun y => G.degree y ≤ 4)).card ≤ G.degree x - 1 := by
          have hsub2 : (G.neighborFinset x).filter (fun y => G.degree y ≤ 4)
              ⊆ (G.neighborFinset x).erase u := by
            intro y hy
            rw [Finset.mem_filter] at hy
            refine Finset.mem_erase.mpr ⟨?_, hy.1⟩
            rintro rfl
            omega
          calc ((G.neighborFinset x).filter
              (fun y => G.degree y ≤ 4)).card
              ≤ ((G.neighborFinset x).erase u).card :=
                Finset.card_le_card hsub2
            _ = G.degree x - 1 := by
                rw [Finset.card_erase_of_mem huN,
                  G.card_neighborFinset_eq_degree]
        exact Nat.mul_le_mul_right _ hcard3
    _ = ∑ x ∈ P, (G.degree x - 1) * (G.degree x - 1) * 3 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ 26 * T.card * 3 := by
        rw [← Finset.sum_mul]
        refine Nat.mul_le_mul_right 3 ?_
        calc ∑ x ∈ P, (G.degree x - 1) * (G.degree x - 1)
            = ∑ x ∈ P.filter (fun x => G.degree x = 3),
                (G.degree x - 1) * (G.degree x - 1)
              + ∑ x ∈ P.filter (fun x => ¬G.degree x = 3),
                (G.degree x - 1) * (G.degree x - 1) :=
              (Finset.sum_filter_add_sum_filter_not P _ _).symm
          _ ≤ ∑ _x ∈ P.filter (fun x => G.degree x = 3), 4
              + ∑ _x ∈ P.filter (fun x => ¬G.degree x = 3), 9 := by
              refine Nat.add_le_add (Finset.sum_le_sum fun x hx => ?_)
                (Finset.sum_le_sum fun x hx => ?_)
              · rw [Finset.mem_filter] at hx
                rw [hx.2]
              · rw [Finset.mem_filter] at hx
                have h4 := hPlight x hx.1
                have h3x := h3 x
                have hx4 : G.degree x = 4 := by omega
                rw [hx4]
          _ = (P.filter (fun x => G.degree x = 3)).card * 4
              + (P.filter (fun x => ¬G.degree x = 3)).card * 9 := by
              rw [Finset.sum_const, Finset.sum_const, smul_eq_mul,
                smul_eq_mul]
          _ ≤ (2 * T.card) * 4 + (2 * T.card) * 9 :=
              Nat.add_le_add (Nat.mul_le_mul_right 4 hP3c)
                (Nat.mul_le_mul_right 9 hP4c)
          _ = 26 * T.card := by ring
    _ = 78 * T.card := by ring

open Classical in
/-- **The per-cloud cap**: unless a σ-law fires, each big hub carries at most
`89` members: same-cloud pairs mediate through light-only channels
(per-degree refined cells: `(deg−1)²·3`-weights). -/
theorem w5big_cloud_le (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (hnofire : ¬W5LawConfig G) (h : Fin n) (hbig : 9 ≤ G.degree h) :
    (G.neighborFinset h ∩ w5big G).card ≤ 89 := by
  classical
  set T := G.neighborFinset h ∩ w5big G with hT
  have hTsub : T ⊆ w5big G := Finset.inter_subset_right
  have hcard : T.card * (T.card - 1) = T.offDiag.card := by
    rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]
  set P2 : Finset (Fin n × Fin n) := T.offDiag.filter
    (fun p => ∃ w, G.Adj p.1 w ∧ G.Adj p.2 w ∧ G.degree w ≤ 4) with hP2def
  set P3 : Finset (Fin n × Fin n) := T.offDiag.filter
    (fun p => ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧
      G.degree w ≤ 4 ∧ G.degree w' ≤ 4) with hP3def
  have hcover : T.offDiag ⊆ P2 ∪ P3 := by
    intro p hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
    rcases w5big_cloud_pair_mechanism G h3 hnofire h hbig p.1 p.2 hp1 hp2 hpne with
      hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hc⟩)
  have hsplit : T.offDiag.card ≤ P2.card + P3.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  -- light-common channel
  have hP2le : P2.card ≤ 10 * T.card := by
    have hsub : P2 ⊆ (Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4)).biUnion
        (fun w => (G.neighborFinset w ∩ T).offDiag) := by
      intro p hp
      obtain ⟨hpd, w, hw1, hw2, hw4⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
      refine Finset.mem_biUnion.mpr ⟨w,
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw4⟩, ?_⟩
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw1.symm, hp1⟩,
         Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.2).mpr hw2.symm, hp2⟩, hpne⟩
    calc P2.card
        ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4),
            (G.neighborFinset w ∩ T).offDiag.card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 4),
            (G.degree w - 1) * (G.neighborFinset w ∩ T).card := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          have hb : (G.neighborFinset w ∩ T).card ≤ G.degree w := by
            calc (G.neighborFinset w ∩ T).card
                ≤ (G.neighborFinset w).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = G.degree w := G.card_neighborFinset_eq_degree w
          rw [Finset.offDiag_card, Nat.sub_one_mul]
          exact Nat.sub_le_sub_right
            (Nat.mul_le_mul_right (G.neighborFinset w ∩ T).card hb) _
      _ ≤ 10 * T.card := light_weighted_slots_le G h3 T hTsub
  -- both-light cross channel via the partner set
  set P : Finset (Fin n) := T.biUnion
    (fun t => (G.neighborFinset t).filter (fun w => G.degree w ≤ 4)) with hPdef
  have hPcard : P.card ≤ 4 * T.card := by
    calc P.card ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun w => G.degree w ≤ 4)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 4 :=
          Finset.sum_le_sum fun t ht => w5big_light_nbrs_le G h3 t (hTsub ht)
      _ = 4 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hPlight : ∀ x ∈ P, G.degree x ≤ 4 := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxt).2
  have hP3c : (P.filter (fun x => G.degree x = 3)).card ≤ 2 * T.card := by
    calc (P.filter (fun x => G.degree x = 3)).card
        ≤ (T.biUnion (fun t => (G.neighborFinset t).filter
            (fun w => G.degree w = 3))).card := by
          refine Finset.card_le_card ?_
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp (by
            rw [hPdef] at hx
            exact hx.1)
          refine Finset.mem_biUnion.mpr ⟨t, htT, ?_⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_filter x hxt, hx.2⟩
      _ ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
            (fun w => G.degree w = 3)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          have h2 : (G.neighborFinset t).filter (fun w => G.degree w = 3)
              = hubTwins G t := by
            rw [hubTwins]
            ext w
            simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
          rw [h2]
          have := hTsub ht
          rw [w5big, Finset.mem_filter] at this
          omega
      _ = 2 * T.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  have hP4c : (P.filter (fun x => ¬G.degree x = 3)).card ≤ 2 * T.card := by
    calc (P.filter (fun x => ¬G.degree x = 3)).card
        ≤ (T.biUnion (fun t => (G.neighborFinset t).filter
            (fun w => G.degree w = 4))).card := by
          refine Finset.card_le_card ?_
          intro x hx
          rw [Finset.mem_filter] at hx
          have hx4 : G.degree x = 4 := by
            have h1 := hPlight x hx.1
            have h2 := h3 x
            have h3' := hx.2
            omega
          obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp (by
            rw [hPdef] at hx
            exact hx.1)
          refine Finset.mem_biUnion.mpr ⟨t, htT, ?_⟩
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_of_mem_filter x hxt, hx4⟩
      _ ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
            (fun w => G.degree w = 4)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 2 := Finset.sum_le_sum fun t ht =>
          w5big_deg4_nbrs_le G h3 t (hTsub ht)
      _ = 2 * T.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
  have hPsum : ∑ x ∈ P, (G.degree x - 1) ≤ 10 * T.card := by
    calc ∑ x ∈ P, (G.degree x - 1)
        = ∑ x ∈ P.filter (fun x => G.degree x = 3), (G.degree x - 1)
          + ∑ x ∈ P.filter (fun x => ¬G.degree x = 3), (G.degree x - 1) :=
          (Finset.sum_filter_add_sum_filter_not P _ _).symm
      _ ≤ ∑ _x ∈ P.filter (fun x => G.degree x = 3), 2
          + ∑ _x ∈ P.filter (fun x => ¬G.degree x = 3), 3 := by
          refine Nat.add_le_add (Finset.sum_le_sum fun x hx => ?_)
            (Finset.sum_le_sum fun x hx => ?_)
          · rw [Finset.mem_filter] at hx
            omega
          · rw [Finset.mem_filter] at hx
            have := hPlight x hx.1
            omega
      _ = (P.filter (fun x => G.degree x = 3)).card * 2
          + (P.filter (fun x => ¬G.degree x = 3)).card * 3 := by
          rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      _ ≤ (2 * T.card) * 2 + (2 * T.card) * 3 :=
          Nat.add_le_add (Nat.mul_le_mul_right 2 hP3c)
            (Nat.mul_le_mul_right 3 hP4c)
      _ = 10 * T.card := by ring
  have hP3le :=
      w5big_cloud_le_hP3le (n := n) (G := G) (h3) (h := h) (hTsub) (P := P)
        (hPdef) (hPlight) (hP3c) (hP4c)
  have hquad : T.card * (T.card - 1) ≤ 88 * T.card := by
    calc T.card * (T.card - 1) = T.offDiag.card := hcard
      _ ≤ P2.card + P3.card := hsplit
      _ ≤ 10 * T.card + 78 * T.card := Nat.add_le_add hP2le hP3le
      _ = 88 * T.card := by ring
  exact w5_quad hquad

open Classical in
private theorem w5big_card_le_hP2le : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3 ≤
  G.degree v)
  (T : Finset (Fin n)) (_ : T = w5big G) (_ : ∀ (w : Fin n), 9 ≤ G.degree w →
    #(G.neighborFinset w ∩ T) ≤ 89),
  let P2 := {p ∈ T.offDiag | ∃ w, G.Adj p.1 w ∧ G.Adj p.2 w};
  #P2 ≤ 100 * #T := by
  classical
  intro n G h3 T hTdef hK P2
  have hsub : P2 ⊆ Finset.univ.biUnion
      (fun w : Fin n => (G.neighborFinset w ∩ T).offDiag) := by
    intro p hp
    obtain ⟨hpd, w, hw1, hw2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, ?_⟩
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw1.symm, hp1⟩,
       Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.2).mpr hw2.symm, hp2⟩, hpne⟩
  have hbig : ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
      (G.neighborFinset w ∩ T).offDiag.card ≤ 88 * T.card := by
    calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
        (G.neighborFinset w ∩ T).offDiag.card
        ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
          88 * (G.neighborFinset w ∩ T).card := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          rw [Finset.offDiag_card]
          have hcap := hK w hw.2
          have : (G.neighborFinset w ∩ T).card * ((G.neighborFinset w ∩ T).card - 1)
              ≤ (G.neighborFinset w ∩ T).card * 88 :=
            Nat.mul_le_mul_left _ (by omega)
          calc (G.neighborFinset w ∩ T).card * (G.neighborFinset w ∩ T).card
                - (G.neighborFinset w ∩ T).card
              = (G.neighborFinset w ∩ T).card
                * ((G.neighborFinset w ∩ T).card - 1) := by
                rw [Nat.mul_sub, Nat.mul_one]
            _ ≤ (G.neighborFinset w ∩ T).card * 88 := this
            _ = 88 * (G.neighborFinset w ∩ T).card := Nat.mul_comm _ _
      _ = 88 * ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
            (G.neighborFinset w ∩ T).card := by rw [Finset.mul_sum]
      _ ≤ 88 * T.card := by
          refine Nat.mul_le_mul_left 88 ?_
          rw [sum_nbr_inter_comm G _ T]
          calc ∑ u ∈ T, (G.neighborFinset u
                ∩ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w)).card
              ≤ ∑ _u ∈ T, 1 := by
                refine Finset.sum_le_sum fun u hu => ?_
                have := w5big_big_nbrs_le_one G h3 u (hTdef ▸ hu)
                calc (G.neighborFinset u
                      ∩ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w)).card
                    = ((G.neighborFinset u).filter
                        (fun w => 9 ≤ G.degree w)).card := by
                      congr 1
                      ext z
                      simp only [Finset.mem_inter, Finset.mem_filter,
                        Finset.mem_univ, true_and]
                  _ ≤ 1 := this
            _ = T.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  have hsmall : ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
      (G.neighborFinset w ∩ T).offDiag.card ≤ 12 * T.card := by
    calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
        (G.neighborFinset w ∩ T).offDiag.card
        ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
          3 * (G.neighborFinset w ∩ T).card := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          have hb : (G.neighborFinset w ∩ T).card ≤ 4 := by
            by_cases h5 : 5 ≤ G.degree w
            · rw [hTdef, w5big_no_mid_inc G h3 w h5 (by omega)]
              simp
            · calc (G.neighborFinset w ∩ T).card
                  ≤ (G.neighborFinset w).card :=
                    Finset.card_le_card Finset.inter_subset_left
                _ = G.degree w := G.card_neighborFinset_eq_degree w
                _ ≤ 4 := by omega
          rw [Finset.offDiag_card]
          have := Nat.mul_le_mul_right (G.neighborFinset w ∩ T).card hb
          omega
      _ = 3 * ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
            (G.neighborFinset w ∩ T).card := by rw [Finset.mul_sum]
      _ ≤ 3 * (4 * T.card) := by
          refine Nat.mul_le_mul_left 3 ?_
          exact w5big_light_slots_le' G h3 T (fun z hz => hTdef ▸ hz)
            _ (fun w hw => by
              rw [Finset.mem_filter] at hw
              omega)
      _ = 12 * T.card := by ring
  calc P2.card
      ≤ ∑ w : Fin n, (G.neighborFinset w ∩ T).offDiag.card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
          (G.neighborFinset w ∩ T).offDiag.card
        + ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
          (G.neighborFinset w ∩ T).offDiag.card :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ 88 * T.card + 12 * T.card := Nat.add_le_add hbig hsmall
    _ = 100 * T.card := by ring

open Classical in
private theorem w5big_card_le_hP3c : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
  (_ : T = w5big G),
  let P := T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4};
  ∀ (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4}),
    #({x ∈ P | G.degree x = 3}) ≤ 2 * #T := by
  classical
  intro n G T hTdef P hPdef
  calc (P.filter (fun x => G.degree x = 3)).card
      ≤ (T.biUnion (fun t => (G.neighborFinset t).filter
          (fun w => G.degree w = 3))).card := by
        refine Finset.card_le_card ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp (by
          rw [hPdef] at hx
          exact hx.1)
        refine Finset.mem_biUnion.mpr ⟨t, htT, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_of_mem_filter x hxt, hx.2⟩
    _ ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun w => G.degree w = 3)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        have h2 : (G.neighborFinset t).filter (fun w => G.degree w = 3)
            = hubTwins G t := by
          rw [hubTwins]
          ext w
          simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
        rw [h2]
        have := hTdef ▸ ht
        rw [w5big, Finset.mem_filter] at this
        omega
    _ = 2 * T.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

open Classical in
private theorem w5big_card_le_hP4c : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3 ≤
  G.degree v)
  (T : Finset (Fin n)) (_ : T = w5big G),
  let P := T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4};
  ∀ (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4}) (_ : ∀ x ∈ P,
    G.degree x ≤ 4),
    #({x ∈ P | ¬G.degree x = 3}) ≤ 2 * #T := by
  classical
  intro n G h3 T hTdef P hPdef hPlight
  calc (P.filter (fun x => ¬G.degree x = 3)).card
      ≤ (T.biUnion (fun t => (G.neighborFinset t).filter
          (fun w => G.degree w = 4))).card := by
        refine Finset.card_le_card ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        have hx4 : G.degree x = 4 := by
          have h1 := hPlight x hx.1
          have h2 := h3 x
          have h3' := hx.2
          omega
        obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp (by
          rw [hPdef] at hx
          exact hx.1)
        refine Finset.mem_biUnion.mpr ⟨t, htT, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_of_mem_filter x hxt, hx4⟩
    _ ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun w => G.degree w = 4)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 2 := Finset.sum_le_sum fun t ht =>
        w5big_deg4_nbrs_le G h3 t (hTdef ▸ ht)
    _ = 2 * T.card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

open Classical in
private theorem w5big_card_le_hsub : ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
  let T := w5big G;
  let P3 := {p ∈ T.offDiag | ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧ (G.degree w ≤ 4 ∨
    G.degree w' ≤ 4)};
  ∀ (P : Finset (Fin n)) (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4}),
    P3 ⊆
      P.biUnion fun x =>
        (G.neighborFinset x).biUnion fun y =>
          (G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T) ∪
            (G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T) := by
  classical
  intro n G T P3 P hPdef p hp
  obtain ⟨hpd, w, w', hw, hw', hww', htag⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
  rcases htag with hw4 | hw'4
  · have hwP : w ∈ P := by
      rw [hPdef]
      exact Finset.mem_biUnion.mpr ⟨p.1, hp1,
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p.1 w).mpr hw, hw4⟩⟩
    refine Finset.mem_biUnion.mpr ⟨w, hwP, ?_⟩
    refine Finset.mem_biUnion.mpr
      ⟨w', (G.mem_neighborFinset w w').mpr hww', ?_⟩
    refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩
  · have hw'P : w' ∈ P := by
      rw [hPdef]
      exact Finset.mem_biUnion.mpr ⟨p.2, hp2,
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p.2 w').mpr hw', hw'4⟩⟩
    refine Finset.mem_biUnion.mpr ⟨w', hw'P, ?_⟩
    refine Finset.mem_biUnion.mpr
      ⟨w, (G.mem_neighborFinset w' w).mpr hww'.symm, ?_⟩
    refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩

open Classical in
private theorem w5big_card_le_hperx : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3 ≤
  G.degree v)
  (T : Finset (Fin n)) (_ : T = w5big G) (_ : ∀ (w : Fin n), 9 ≤ G.degree w →
    #(G.neighborFinset w ∩ T) ≤ 89),
  let P := T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4};
  ∀ (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4}) (_ : ∀ x ∈ P,
    G.degree x ≤ 4)
    (_ : ∀ (A B : Finset (Fin n)) (a b : ℕ), #A ≤ a → #B ≤ b → #(A ×ˢ B ∪ B ×ˢ A) ≤ a * b +
      b * a)
    (_ : ∀ (nxt b : ℕ), nxt + b ≤ 3 → b ≤ 2 → b * (178 * nxt) + (2 - b) * (8 * nxt) ≤ 372)
    (_ : ∀ (nxt b : ℕ), nxt + b ≤ 4 → b ≤ 3 → b * (178 * nxt) + (3 - b) * (8 * nxt) ≤ 728),
    ∀ x ∈ P,
      ∑ y ∈ G.neighborFinset x,
          #((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T) ∪
              (G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T)) ≤
        if G.degree x = 3 then 372 else 728 := by
  classical
  intro n G h3 T hTdef hK P hPdef hPlight hcardUB harith3 harith4 x hx
  have hdeg : G.degree x = 3 ∨ G.degree x = 4 := by
    have h1 := hPlight x hx
    have h2 := h3 x
    omega
  obtain ⟨u, huT, hxu⟩ := Finset.mem_biUnion.mp (by
    rw [hPdef] at hx
    exact hx)
  have huN : u ∈ G.neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    exact ((G.mem_neighborFinset u x).mp
      (Finset.mem_of_mem_filter x hxu)).symm
  have hNuT : G.neighborFinset u ∩ T = ∅ := by
    rw [hTdef]
    exact w5big_nbr_inter_self_empty G h3 u (hTdef ▸ huT)
  have hzero : (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset u ∩ T)) ∪
        ((G.neighborFinset u ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.union_eq_empty]
    refine ⟨?_, ?_⟩
    · rw [Finset.product_eq_empty]
      exact Or.inr hNuT
    · rw [Finset.product_eq_empty]
      exact Or.inl hNuT
  rw [← Finset.add_sum_erase _ _ huN, hzero, Nat.zero_add]
  set E := (G.neighborFinset x).erase u with hEdef
  have hEcard : E.card = G.degree x - 1 := by
    rw [hEdef, Finset.card_erase_of_mem huN,
      G.card_neighborFinset_eq_degree]
  have hbxub : (E.filter (fun y => 9 ≤ G.degree y)).card ≤ E.card :=
    Finset.card_filter_le _ _
  have hdisj : Disjoint (G.neighborFinset x ∩ T)
      (E.filter (fun y => 9 ≤ G.degree y)) := by
    rw [Finset.disjoint_left]
    intro z hzT hzB
    rw [Finset.mem_inter] at hzT
    rw [Finset.mem_filter] at hzB
    have hz5 : G.degree z = 5 := by
      have := hTdef ▸ hzT.2
      rw [w5big, Finset.mem_filter] at this
      exact this.2.1
    omega
  have hunionsub : (G.neighborFinset x ∩ T) ∪
      (E.filter (fun y => 9 ≤ G.degree y)) ⊆ G.neighborFinset x := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact Finset.mem_of_mem_inter_left hz
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter z hz)
  have hrefine : (G.neighborFinset x ∩ T).card
      + (E.filter (fun y => 9 ≤ G.degree y)).card ≤ G.degree x := by
    have hc := Finset.card_le_card hunionsub
    rwa [Finset.card_union_of_disjoint hdisj,
      G.card_neighborFinset_eq_degree] at hc
  have hnotcard : (E.filter (fun y => ¬ 9 ≤ G.degree y)).card
      = E.card - (E.filter (fun y => 9 ≤ G.degree y)).card := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := E) (p := fun y => 9 ≤ G.degree y)
    omega
  have hcellB : ∀ y ∈ E.filter (fun y => 9 ≤ G.degree y),
      (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
        ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
      ≤ 178 * (G.neighborFinset x ∩ T).card := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have hb : (G.neighborFinset y ∩ T).card ≤ 89 := hK y hy.2
    calc (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
          ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
        ≤ (G.neighborFinset x ∩ T).card * 89
            + 89 * (G.neighborFinset x ∩ T).card :=
          hcardUB _ _ _ 89 (le_refl _) hb
      _ = 178 * (G.neighborFinset x ∩ T).card := by ring
  have hcellS : ∀ y ∈ E.filter (fun y => ¬ 9 ≤ G.degree y),
      (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
        ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
      ≤ 8 * (G.neighborFinset x ∩ T).card := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have hb : (G.neighborFinset y ∩ T).card ≤ 4 := by
      by_cases h5 : 5 ≤ G.degree y
      · rw [hTdef, w5big_no_mid_inc G h3 y h5 (by omega)]
        simp
      · calc (G.neighborFinset y ∩ T).card
            ≤ (G.neighborFinset y).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = G.degree y := G.card_neighborFinset_eq_degree y
          _ ≤ 4 := by
              have := hy.2
              omega
    calc (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
          ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
        ≤ (G.neighborFinset x ∩ T).card * 4
            + 4 * (G.neighborFinset x ∩ T).card :=
          hcardUB _ _ _ 4 (le_refl _) hb
      _ = 8 * (G.neighborFinset x ∩ T).card := by ring
  have hsumsplit : (∑ y ∈ E,
      (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
        ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card)
      ≤ (E.filter (fun y => 9 ≤ G.degree y)).card
          * (178 * (G.neighborFinset x ∩ T).card)
        + (E.card - (E.filter (fun y => 9 ≤ G.degree y)).card)
          * (8 * (G.neighborFinset x ∩ T).card) := by
    rw [← Finset.sum_filter_add_sum_filter_not E
      (fun y => 9 ≤ G.degree y)]
    refine Nat.add_le_add ?_ ?_
    · calc (∑ y ∈ E.filter (fun y => 9 ≤ G.degree y),
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
              ((G.neighborFinset y ∩ T) ×ˢ
                (G.neighborFinset x ∩ T))).card)
          ≤ ∑ _y ∈ E.filter (fun y => 9 ≤ G.degree y),
              178 * (G.neighborFinset x ∩ T).card :=
            Finset.sum_le_sum hcellB
        _ = (E.filter (fun y => 9 ≤ G.degree y)).card
            * (178 * (G.neighborFinset x ∩ T).card) := by
            rw [Finset.sum_const, smul_eq_mul]
    · calc (∑ y ∈ E.filter (fun y => ¬ 9 ≤ G.degree y),
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
              ((G.neighborFinset y ∩ T) ×ˢ
                (G.neighborFinset x ∩ T))).card)
          ≤ ∑ _y ∈ E.filter (fun y => ¬ 9 ≤ G.degree y),
              8 * (G.neighborFinset x ∩ T).card :=
            Finset.sum_le_sum hcellS
        _ = (E.card - (E.filter (fun y => 9 ≤ G.degree y)).card)
            * (8 * (G.neighborFinset x ∩ T).card) := by
            rw [Finset.sum_const, smul_eq_mul, hnotcard]
  refine le_trans hsumsplit ?_
  rcases hdeg with hd3 | hd4
  · rw [ite_eq_left hd3]
    have hE2 : E.card = 2 := by rw [hEcard, hd3]
    rw [hE2]
    exact harith3 _ _ (by rw [← hd3]; exact hrefine)
      (by rw [← hE2]; exact hbxub)
  · rw [ite_eq_right (by omega)]
    have hE3 : E.card = 3 := by rw [hEcard, hd4]
    rw [hE3]
    exact harith4 _ _ (by rw [← hd4]; exact hrefine)
      (by rw [← hE3]; exact hbxub)

open Classical in
/-- **The global `W₅ᵇ` bound**: unless a σ-law fires,
`|W₅ᵇ| ≤ 100 + 2200 + 1 = 2301`.  The `P3` slot trade-off: a light `x` that
mediates `b` big neighbours spends `b` of its degree slots on them, so it keeps
at most `deg x − b` `T`-neighbours; balancing the `b` big cells (`≤ 2·89` each)
against the `deg x − 1 − b` small cells (`≤ 2·4` each) caps the per-`x` `P3`
contribution at `728` (`deg 4`) / `372` (`deg 3`). -/
theorem w5big_card_le (G : SimpleGraph (Fin n)) (h3 : ∀ v, 3 ≤ G.degree v)
    (hnofire : ¬W5LawConfig G) :
    (w5big G).card ≤ 2301 := by
  classical
  set T := w5big G with hTdef
  have hK : ∀ w : Fin n, 9 ≤ G.degree w →
      (G.neighborFinset w ∩ T).card ≤ 89 :=
    fun w hw => w5big_cloud_le G h3 hnofire w hw
  have hincle : ∀ y : Fin n, (G.neighborFinset y ∩ T).card ≤ 93 :=
    fun y => w5big_inc_le G h3 89 hK y
  have hcard : T.card * (T.card - 1) = T.offDiag.card := by
    rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]
  set P2 : Finset (Fin n × Fin n) := T.offDiag.filter
    (fun p => ∃ w, G.Adj p.1 w ∧ G.Adj p.2 w) with hP2def
  set P3 : Finset (Fin n × Fin n) := T.offDiag.filter
    (fun p => ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧
      (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)) with hP3def
  have hcover : T.offDiag ⊆ P2 ∪ P3 := by
    intro p hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
    rcases w5big_pair_mechanism G h3 hnofire p.1 p.2 hp1 hp2 hpne with hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hc⟩)
  have hsplit : T.offDiag.card ≤ P2.card + P3.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  -- common channel: big mediators via the cloud cap, small via light slots
  have hP2le :=
      w5big_card_le_hP2le (n := n) (G := G) (h3) (T := T) (hTdef) (hK)
  -- light-endpoint cross channel via the partner set
  set P : Finset (Fin n) := T.biUnion
    (fun t => (G.neighborFinset t).filter (fun w => G.degree w ≤ 4)) with hPdef
  have hPcard : P.card ≤ 4 * T.card := by
    calc P.card ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun w => G.degree w ≤ 4)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 4 :=
          Finset.sum_le_sum fun t ht => w5big_light_nbrs_le G h3 t (hTdef ▸ ht)
      _ = 4 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hPlight : ∀ x ∈ P, G.degree x ≤ 4 := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxt).2
  have hP3c := w5big_card_le_hP3c (n := n) (G := G) (T := T) (hTdef) (hPdef)
  have hP4c := w5big_card_le_hP4c (n := n) (G := G) (h3) (T := T) (hTdef) (hPdef) (hPlight)
  have hPsum : ∑ x ∈ P, (G.degree x - 1) ≤ 10 * T.card := by
    calc ∑ x ∈ P, (G.degree x - 1)
        = ∑ x ∈ P.filter (fun x => G.degree x = 3), (G.degree x - 1)
          + ∑ x ∈ P.filter (fun x => ¬G.degree x = 3), (G.degree x - 1) :=
          (Finset.sum_filter_add_sum_filter_not P _ _).symm
      _ ≤ ∑ _x ∈ P.filter (fun x => G.degree x = 3), 2
          + ∑ _x ∈ P.filter (fun x => ¬G.degree x = 3), 3 := by
          refine Nat.add_le_add (Finset.sum_le_sum fun x hx => ?_)
            (Finset.sum_le_sum fun x hx => ?_)
          · rw [Finset.mem_filter] at hx
            omega
          · rw [Finset.mem_filter] at hx
            have := hPlight x hx.1
            omega
      _ = (P.filter (fun x => G.degree x = 3)).card * 2
          + (P.filter (fun x => ¬G.degree x = 3)).card * 3 := by
          rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      _ ≤ (2 * T.card) * 2 + (2 * T.card) * 3 :=
          Nat.add_le_add (Nat.mul_le_mul_right 2 hP3c)
            (Nat.mul_le_mul_right 3 hP4c)
      _ = 10 * T.card := by ring
  have hP3le : P3.card ≤ 2200 * T.card := by
    have hsub := w5big_card_le_hsub (n := n) (G := G) (P := P) (hPdef)
    have hcardUB : ∀ (A B : Finset (Fin n)) (a b : ℕ),
        A.card ≤ a → B.card ≤ b →
        ((A ×ˢ B) ∪ (B ×ˢ A)).card ≤ a * b + b * a := by
      intro A B a b hA hB
      calc ((A ×ˢ B) ∪ (B ×ˢ A)).card
          ≤ (A ×ˢ B).card + (B ×ˢ A).card := Finset.card_union_le _ _
        _ = A.card * B.card + B.card * A.card := by
            rw [Finset.card_product, Finset.card_product]
        _ ≤ a * b + b * a :=
            Nat.add_le_add (Nat.mul_le_mul hA hB) (Nat.mul_le_mul hB hA)
    have harith3 : ∀ nxt b : ℕ, nxt + b ≤ 3 → b ≤ 2 →
        b * (178 * nxt) + (2 - b) * (8 * nxt) ≤ 372 := by
      intro nxt b h1 h2
      interval_cases b <;> omega
    have harith4 : ∀ nxt b : ℕ, nxt + b ≤ 4 → b ≤ 3 →
        b * (178 * nxt) + (3 - b) * (8 * nxt) ≤ 728 := by
      intro nxt b h1 h2
      interval_cases b <;> omega
    have hperx :=
        w5big_card_le_hperx (n := n) (G := G) (h3) (T := T) (hTdef) (hK)
          (hPdef) (hPlight) (hcardUB) (harith3) (harith4)
    calc P3.card
        ≤ ∑ x ∈ P, ((G.neighborFinset x).biUnion (fun y : Fin n =>
            ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
            ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T)))).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ x ∈ P, ∑ y ∈ G.neighborFinset x,
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
              ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card :=
          Finset.sum_le_sum fun x _ => Finset.card_biUnion_le
      _ ≤ ∑ x ∈ P, (if G.degree x = 3 then 372 else 728) :=
          Finset.sum_le_sum hperx
      _ ≤ 2200 * T.card := by
          calc ∑ x ∈ P, (if G.degree x = 3 then (372 : ℕ) else 728)
              = ∑ x ∈ P.filter (fun x => G.degree x = 3),
                  (if G.degree x = 3 then (372 : ℕ) else 728)
                + ∑ x ∈ P.filter (fun x => ¬G.degree x = 3),
                  (if G.degree x = 3 then (372 : ℕ) else 728) :=
                (Finset.sum_filter_add_sum_filter_not P _ _).symm
            _ = ∑ _x ∈ P.filter (fun x => G.degree x = 3), (372 : ℕ)
                + ∑ _x ∈ P.filter (fun x => ¬G.degree x = 3), (728 : ℕ) := by
                congr 1
                · refine Finset.sum_congr rfl fun x hx => ?_
                  rw [Finset.mem_filter] at hx
                  rw [ite_eq_left hx.2]
                · refine Finset.sum_congr rfl fun x hx => ?_
                  rw [Finset.mem_filter] at hx
                  rw [ite_eq_right hx.2]
            _ = (P.filter (fun x => G.degree x = 3)).card * 372
                + (P.filter (fun x => ¬G.degree x = 3)).card * 728 := by
                rw [Finset.sum_const, Finset.sum_const, smul_eq_mul,
                  smul_eq_mul]
            _ ≤ (2 * T.card) * 372 + (2 * T.card) * 728 :=
                Nat.add_le_add (Nat.mul_le_mul_right 372 hP3c)
                  (Nat.mul_le_mul_right 728 hP4c)
            _ = 2200 * T.card := by ring
  have hquad : T.card * (T.card - 1) ≤ 2300 * T.card := by
    calc T.card * (T.card - 1) = T.offDiag.card := hcard
      _ ≤ P2.card + P3.card := hsplit
      _ ≤ 100 * T.card + 2200 * T.card := Nat.add_le_add hP2le hP3le
      _ = 2300 * T.card := by ring
  exact w5_quad hquad

open Classical in
/-- **A saturated small vertex fires the block cut.**  ANY vertex of degree
`d ≤ 15` with at least `d − 1` degree-3 twins fires
`algConn_le_two_of_hub_block` as soon as `n ≥ 512 ≥ 2(k+1)²` — in particular
a degree-3 vertex with 2 degree-3 neighbours and a degree-4 vertex with 3. -/
theorem hub_saturated_fires (n : ℕ) [Nonempty (Fin n)] (hn : 512 ≤ n)
    (G : SimpleGraph (Fin n)) (w : Fin n)
    (h15 : G.degree w ≤ 15)
    (ha : G.degree w ≤ (hubTwins G w).card + 1) :
    algConn G ≤ 2 := by
  classical
  have hK3 : ∀ t ∈ hubTwins G w, G.degree t = 3 :=
    fun t ht => (mem_hubTwins_iff.mp ht).2
  have hKadj : ∀ t ∈ hubTwins G w, G.Adj w t :=
    fun t ht => (mem_hubTwins_iff.mp ht).1
  have hwK : w ∉ hubTwins G w := fun hw =>
    G.irrefl (mem_hubTwins_iff.mp hw).1
  have hkle : (hubTwins G w).card ≤ G.degree w := hubTwins_card_le_degree G w
  have hcardV : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine algConn_le_two_of_hub_block' G w (hubTwins G w) hwK hKadj hK3 ?_ ?_
  · rw [hcardV]
    omega
  · rw [hcardV]
    set k := (hubTwins G w).card with hk
    have h1 : G.degree w + k ≤ 2 * k + 1 := by omega
    have h2 : 2 * (k + 1) * (k + 1) ≤ 512 := by
      have : k ≤ 15 := by omega
      nlinarith
    have hkn : k + 1 ≤ n := by omega
    have key : n * (G.degree w + k) + 2 * (k + 1) * (k + 1)
        ≤ 2 * (k + 1) * n := by
      calc n * (G.degree w + k) + 2 * (k + 1) * (k + 1)
          ≤ n * (2 * k + 1) + 512 :=
            Nat.add_le_add (Nat.mul_le_mul_left n h1) h2
        _ ≤ n * (2 * k + 1) + n := Nat.add_le_add_left hn _
        _ = 2 * (k + 1) * n := by ring
    have hexp : 2 * (k + 1) * (n - (k + 1)) + 2 * (k + 1) * (k + 1)
        = 2 * (k + 1) * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hkn]
    rw [← hexp] at key
    exact Nat.le_of_add_le_add_right key

open Classical in
/-- **The block dichotomy**: either some degree-`≤ 15` vertex is twin-saturated
(and the graph fires), or EVERY vertex of degree `d ≤ 15` has at most `d − 2`
degree-3 neighbours — degree-3 vertices at most one (`M` is a matching),
degree-4 vertices at most two. -/
theorem blocks_or_smallcap (n : ℕ) [Nonempty (Fin n)] (hn : 512 ≤ n)
    (G : SimpleGraph (Fin n)) :
    algConn G ≤ 2 ∨ ∀ w : Fin n, G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w := by
  classical
  by_cases hsat : ∃ w : Fin n, G.degree w ≤ 15
      ∧ G.degree w ≤ (hubTwins G w).card + 1
  · obtain ⟨w, h15, ha⟩ := hsat
    exact Or.inl (hub_saturated_fires n hn G w h15 ha)
  · push Not at hsat
    refine Or.inr fun w h15 => ?_
    have := hsat w h15
    omega

open Classical in
/-- **The β-ledger** (`β = 105/128 < 7/8`): on the boundary of the compact
cell, either a σ-law fires (closing the conjecture outright), or the
suppressed count obeys the sharpened supply bound

  `(32/21)·s ≤ (5/4)·X + 423`

— i.e. `s ≤ (105/128)·X + C`, breaking the `β = 7/8` ledger wall.  The
constant is `214` (capped overflow) plus `(206 + 2301)/12` (the `W₅`
overflow through the Moore bound and the refined cloud bound). -/
theorem suppressed_ledger_beta (n : ℕ) [Nonempty (Fin n)] (hn : 512 ≤ n)
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G) (hb : SeaFatBoundary G)
    (hcpt : ¬HasUsableFarPair G) :
    algConn G ≤ 2 ∨
    (32 / 21 : ℝ) * ((Finset.univ.filter
        (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v)).card : ℝ)
      ≤ (5 / 4 : ℝ) * (excessX n G : ℝ) + 423 := by
  classical
  by_cases hfire : W5LawConfig G
  · exact Or.inl (w5LawConfig_closes G h.min_degree hfire)
  rcases blocks_or_smallcap n hn G with hblkfire | hblkfull
  · exact Or.inl hblkfire
  rcases medges_or_single n (by omega) G with hmfire | huniq
  · exact Or.inl hmfire
  · have hblk : ∀ w : Fin n, 5 ≤ G.degree w → G.degree w ≤ 15 →
        (hubTwins G w).card + 2 ≤ G.degree w :=
      fun w _ h15 => hblkfull w h15
    have hml : ∀ z : Fin n, G.degree z ≤ 4 →
        ((G.neighborFinset z).filter (fun t => G.degree t = 3)).card
          ≤ G.degree z - 2 := by
      intro z hz4
      have h1 := hblkfull z (by omega)
      have h2 : (G.neighborFinset z).filter (fun t => G.degree t = 3)
          = hubTwins G z := by
        rw [hubTwins]
        ext t
        simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
      rw [h2]
      omega
    refine Or.inr ?_
    have hledger := weighted_heavy_ledger_sharp G h.min_degree
    have htransfer := sigma_transfer_sum n G h hb hblk hml huniq
    -- the `W₅` count through the split and the cloud bound
    have hsplit := w5_card_split n G hcpt
    have hcloud := w5big_card_le G h.min_degree hfire
    have hcloudR : ((Finset.univ.filter (fun w : Fin n =>
        G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
          ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)).card : ℝ) ≤ 2301 := by
      have : (Finset.univ.filter (fun w : Fin n =>
          G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)).card ≤ 2301 := by
        have heq : Finset.univ.filter (fun w : Fin n =>
            G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
              ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x) = w5big G := by
          rw [w5big]
        rw [heq]
        exact hcloud
      exact_mod_cast this
    have hN5 : ((Finset.univ.filter (fun w : Fin n =>
        G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)).card : ℝ)
        ≤ 2507 := by
      linarith [hsplit, hcloudR]
    linarith [hledger, htransfer, hN5]

end ACMax
