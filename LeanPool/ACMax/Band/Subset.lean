/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Band.Sum
public import LeanPool.ACMax.Counting.V9Discharge

/-!
# The SUM band-discharge subset wrapper (B5)

This file lands the census-free subset/`2`-core wrapper for the SUM (vertex-ball) Moore refutation
(node B5 of the band discharge): it instantiates the abstract girth bound `ahl_ball_girth_bound`
(`Band.Sum`) at the induced graph on the `2`-core of a subset `S`, producing a short cycle inside
`S`
in the exact `ZMod k` cyclic-map form demanded by `GirthExcessBound`.  It mirrors the SQRT discharge
plumbing (`Counting.SqrtDischarge`) **minus the component descent** — the Alon–Hoory–Linial AM–GM
walk count and the ball injectivity are global
sums, so no connectivity is needed and the `2`-core alone suffices.

## The `v`-transport

The SUM side condition is verified at `v = S.card`, but the `2`-core shrinks to `v' = S'.card ≤ v`.
The single genuinely-new arithmetic step is the **`v`-transport** `ball_side_transport`: the
per-cell
SUM inequality (in vertex-ball sum form) is monotone the right way, so it descends from `v` to any
`v' ≤ v`.  The proof is term-by-term over the geometric sum, each summand comparison reducing to the
three base facts `v' - 1 ≤ v - 1`, `(v + t)·v' ≤ (v' + t)·v`, `(v + 2t)·v' ≤ (v' + 2t)·v` (all
`↔ v' ≤ v`) plus `Nat.pow_le_pow_left` — no `nlinarith`, matching the doc's `0/9000`-violation
verification.

## Contents

* **`ball_side_transport`** — the `v`-transport of the SUM side condition (sum form) from `v` to
  `v' ≤ v`.
* **`ahl_ball_girth_subset`** — the subset wrapper: a nonempty `S` with edge excess
  `2|S| + 2t ≤ pairs(S)` meeting the SUM side condition
  `t(|S| − 1)|S|^(L/2) < (|S| + t)((|S| + 2t)^(L/2) − |S|^(L/2))` (`6 ≤ L`) carries a cycle of
  length
  `3 ≤ k ≤ L` inside `S`, in the `ZMod k` cyclic-map form.
-/

public section

namespace ACMax

open SimpleGraph Finset

open Classical in
/-- **The `v`-transport of the SUM side condition.**  In vertex-ball sum form
`(v − 1)·v^ℓ < 2(v + t)·Σ_{k<ℓ}(v + 2t)^k v^(ℓ−1−k)`, the condition descends from `v` to any
`v' ≤ v`.  The proof is term-by-term over the geometric sum: each summand comparison, after
peeling a
common `v'^(ℓ−1−k)·v^(ℓ−1−k)` factor, reduces to `v' − 1 ≤ v − 1`, `(v + t)v' ≤ (v' + t)v` and
`((v + 2t)v')^k ≤ ((v' + 2t)v)^k` (all consequences of `v' ≤ v`); a cross-multiplied cancellation
finishes. -/
theorem ball_side_transport {t ℓ v v' : ℕ} (ht : 1 ≤ t) (hℓ : 1 ≤ ℓ) (hvv' : v' ≤ v)
    (hQ : (v - 1) * v ^ ℓ
      < 2 * (v + t) * ∑ k ∈ Finset.range ℓ, (v + 2 * t) ^ k * v ^ (ℓ - 1 - k)) :
    (v' - 1) * v' ^ ℓ
      < 2 * (v' + t) * ∑ k ∈ Finset.range ℓ, (v' + 2 * t) ^ k * v' ^ (ℓ - 1 - k) := by
  set Sv := ∑ k ∈ Finset.range ℓ, (v + 2 * t) ^ k * v ^ (ℓ - 1 - k) with hSvdef
  set Sv' := ∑ k ∈ Finset.range ℓ, (v' + 2 * t) ^ k * v' ^ (ℓ - 1 - k) with hSv'def
  have hXM : (v' - 1) * v' ^ ℓ * (2 * (v + t) * Sv)
      ≤ (v - 1) * v ^ ℓ * (2 * (v' + t) * Sv') := by
    calc (v' - 1) * v' ^ ℓ * (2 * (v + t) * Sv)
        = ∑ k ∈ Finset.range ℓ,
            (v' - 1) * v' ^ ℓ * (2 * (v + t)) * ((v + 2 * t) ^ k * v ^ (ℓ - 1 - k)) := by
          rw [hSvdef, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ ∑ k ∈ Finset.range ℓ,
            (v - 1) * v ^ ℓ * (2 * (v' + t)) * ((v' + 2 * t) ^ k * v' ^ (ℓ - 1 - k)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hklt : k < ℓ := Finset.mem_range.mp hk
          have hpk : v' ^ ℓ = v' ^ (k + 1) * v' ^ (ℓ - 1 - k) := by
            rw [← pow_add]; congr 1; omega
          have hqk : v ^ ℓ = v ^ (k + 1) * v ^ (ℓ - 1 - k) := by
            rw [← pow_add]; congr 1; omega
          have h1 : v' - 1 ≤ v - 1 := by omega
          have h2 : (v + t) * v' ≤ (v' + t) * v := by
            calc (v + t) * v' = v * v' + t * v' := by ring
              _ ≤ v * v' + t * v := Nat.add_le_add_left (Nat.mul_le_mul (le_refl t) hvv') _
              _ = (v' + t) * v := by ring
          have h3 : (v + 2 * t) * v' ≤ (v' + 2 * t) * v := by
            calc (v + 2 * t) * v' = v * v' + 2 * t * v' := by ring
              _ ≤ v * v' + 2 * t * v := Nat.add_le_add_left (Nat.mul_le_mul (le_refl (2 * t))
                hvv') _
              _ = (v' + 2 * t) * v := by ring
          have h3k : ((v + 2 * t) * v') ^ k ≤ ((v' + 2 * t) * v) ^ k := Nat.pow_le_pow_left h3 k
          have hAB : (v' - 1) * ((v + t) * v') * ((v + 2 * t) * v') ^ k
              ≤ (v - 1) * ((v' + t) * v) * ((v' + 2 * t) * v) ^ k :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3k
          have keyL : (v' - 1) * v' ^ ℓ * (2 * (v + t)) * ((v + 2 * t) ^ k * v ^ (ℓ - 1 - k))
              = 2 * (v' ^ (ℓ - 1 - k) * v ^ (ℓ - 1 - k))
                  * ((v' - 1) * ((v + t) * v') * ((v + 2 * t) * v') ^ k) := by
            rw [mul_pow, hpk]; ring
          have keyR : (v - 1) * v ^ ℓ * (2 * (v' + t)) * ((v' + 2 * t) ^ k * v' ^ (ℓ - 1 - k))
              = 2 * (v' ^ (ℓ - 1 - k) * v ^ (ℓ - 1 - k))
                  * ((v - 1) * ((v' + t) * v) * ((v' + 2 * t) * v) ^ k) := by
            rw [mul_pow, hqk]; ring
          rw [keyL, keyR]
          exact Nat.mul_le_mul (le_refl _) hAB
      _ = (v - 1) * v ^ ℓ * (2 * (v' + t) * Sv') := by
          rw [hSv'def, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
  have hSv'pos : 0 < Sv' := by
    rw [hSv'def]
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · refine ⟨ℓ - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show ℓ - 1 - (ℓ - 1) = 0 by omega, pow_zero, mul_one]
      exact Nat.one_le_pow _ _ (by omega)
  have hYpos : 0 < 2 * (v' + t) * Sv' :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hSv'pos
  have hcombine : 2 * (v + t) * Sv * ((v' - 1) * v' ^ ℓ)
      < 2 * (v + t) * Sv * (2 * (v' + t) * Sv') := by
    calc 2 * (v + t) * Sv * ((v' - 1) * v' ^ ℓ)
        = (v' - 1) * v' ^ ℓ * (2 * (v + t) * Sv) := by ring
      _ ≤ (v - 1) * v ^ ℓ * (2 * (v' + t) * Sv') := hXM
      _ < 2 * (v + t) * Sv * (2 * (v' + t) * Sv') := mul_lt_mul_of_pos_right hQ hYpos
  exact Nat.lt_of_mul_lt_mul_left hcombine

open Classical in
/-- **The SUM band-discharge subset wrapper.**  For a nonempty `S : Finset (Fin n)` with edge excess
`2|S| + 2t ≤ pairs(S)` (i.e. the induced graph on `S` has `≥ |S| + t` edges) meeting the SUM Moore
side condition `t(|S| − 1)|S|^(L/2) < (|S| + t)((|S| + 2t)^(L/2) − |S|^(L/2))` with `6 ≤ L`, there
is
a cycle of length `3 ≤ k ≤ L` inside `S`, given as an injective cyclic map `c : ZMod k → Fin n`.
Assembly (mirrors `girth_excess_bound_holds` minus the component descent): extract the
minimum-degree-`2` `2`-core `S'` (`two_core_aux`), instantiate `ahl_ball_girth_bound` at the induced
graph on `S'` — the side condition transports from `|S|` to `|S'|` (`ball_side_transport`) and the
degree bound `D ≥ 2(|S'| + t)` supplies the remaining term-wise monotonicity — then lift the short
`2`-core cycle to `G` (`Embedding.induce`, `Walk.map`) and convert with `cycle_walk_to_zmod`. -/
theorem ahl_ball_girth_subset {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (t L : ℕ)
    (_hSne : S.Nonempty) (hL6 : 6 ≤ L)
    (hexc : 2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q : Fin n × Fin n => G.Adj q.1 q.2)).card)
    (hside : t * (S.card - 1) * S.card ^ (L / 2)
      < (S.card + t) * ((S.card + 2 * t) ^ (L / 2) - S.card ^ (L / 2))) :
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ L ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S) := by
  classical
  set ℓ := L / 2 with hℓdef
  have hℓ1 : 1 ≤ ℓ := by omega
  -- The side condition forces a positive excess.
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hside
    · exact h
  -- The geometric identity at `v = S.card`, then the sum-form side condition `Q(S.card)`.
  have hgeomv : (∑ k ∈ Finset.range ℓ, (S.card + 2 * t) ^ k * S.card ^ (ℓ - 1 - k)) * (2 * t)
      = (S.card + 2 * t) ^ ℓ - S.card ^ ℓ := by
    have h := geom_sum₂_mul_of_ge (show S.card ≤ S.card + 2 * t by omega) ℓ
    rw [show S.card + 2 * t - S.card = 2 * t by omega] at h
    exact h
  have hmul : t * ((S.card - 1) * S.card ^ ℓ)
      < t * (2 * (S.card + t)
          * ∑ k ∈ Finset.range ℓ, (S.card + 2 * t) ^ k * S.card ^ (ℓ - 1 - k)) := by
    calc t * ((S.card - 1) * S.card ^ ℓ)
        = t * (S.card - 1) * S.card ^ ℓ := by ring
      _ < (S.card + t) * ((S.card + 2 * t) ^ ℓ - S.card ^ ℓ) := hside
      _ = (S.card + t)
            * ((∑ k ∈ Finset.range ℓ, (S.card + 2 * t) ^ k * S.card ^ (ℓ - 1 - k)) * (2 * t)) := by
          rw [hgeomv]
      _ = t * (2 * (S.card + t)
            * ∑ k ∈ Finset.range ℓ, (S.card + 2 * t) ^ k * S.card ^ (ℓ - 1 - k)) := by ring
  have hQv : (S.card - 1) * S.card ^ ℓ
      < 2 * (S.card + t)
          * ∑ k ∈ Finset.range ℓ, (S.card + 2 * t) ^ k * S.card ^ (ℓ - 1 - k) :=
    Nat.lt_of_mul_lt_mul_left hmul
  -- Extract the minimum-within-degree-`2` `2`-core carrying the excess.
  have hpairs' : 2 * S.card + 2 * t ≤ edgeSumWithin G S := by
    rw [edgeSumWithin_eq_pairs]; exact hexc
  obtain ⟨S', hS'sub, hS'ne, hS'min, hS'inv⟩ := two_core_aux G ht1 S hpairs'
  have hQv' : (S'.card - 1) * S'.card ^ ℓ
      < 2 * (S'.card + t)
          * ∑ k ∈ Finset.range ℓ, (S'.card + 2 * t) ^ k * S'.card ^ (ℓ - 1 - k) :=
    ball_side_transport ht1 hℓ1 (Finset.card_le_card hS'sub) hQv
  -- The induced graph on the `2`-core.
  set H : SimpleGraph (↥(↑S' : Set (Fin n))) := G.induce (↑S' : Set (Fin n)) with hHdef
  have : Nonempty (↥(↑S' : Set (Fin n))) := (Finset.coe_nonempty.mpr hS'ne).to_subtype
  have hcardV' : Fintype.card (↥(↑S' : Set (Fin n))) = S'.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  have hDS : edgeSumWithin G S' = 2 * H.edgeFinset.card := by
    rw [edgeSumWithin_eq_pairs]; exact induced_pairs_eq_two_mul_edges G S'
  have hsumdeg : ∑ w, H.degree w = edgeSumWithin G S' := by
    rw [H.sum_degrees_eq_twice_card_edges, hDS]
  have hDge : 2 * (S'.card + t) ≤ ∑ w, H.degree w := by rw [hsumdeg]; omega
  have hδ2 : ∀ w : ↥(↑S' : Set (Fin n)), 2 ≤ H.degree w := by
    intro w
    have hh : H.degree w = degWithin G S' w.val := induce_degree_eq_degWithin G S' w
    rw [hh]
    exact hS'min w.val (Finset.mem_coe.mp w.2)
  -- The SUM Moore bound is violated on `H`, forcing a short `H`-cycle.
  have hbig : Fintype.card (↥(↑S' : Set (Fin n))) ^ ℓ * (Fintype.card (↥(↑S' : Set (Fin n))) - 1)
      < (∑ w, H.degree w) * ∑ k ∈ Finset.range ℓ,
          ((∑ w, H.degree w) - Fintype.card (↥(↑S' : Set (Fin n)))) ^ k
            * Fintype.card (↥(↑S' : Set (Fin n))) ^ (ℓ - 1 - k) := by
    rw [hcardV']
    calc S'.card ^ ℓ * (S'.card - 1)
        = (S'.card - 1) * S'.card ^ ℓ := by ring
      _ < 2 * (S'.card + t)
            * ∑ k ∈ Finset.range ℓ, (S'.card + 2 * t) ^ k * S'.card ^ (ℓ - 1 - k) := hQv'
      _ ≤ (∑ w, H.degree w) * ∑ k ∈ Finset.range ℓ,
            ((∑ w, H.degree w) - S'.card) ^ k * S'.card ^ (ℓ - 1 - k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k _
          have hd2 : S'.card + 2 * t ≤ (∑ w, H.degree w) - S'.card := by omega
          have hd2k : (S'.card + 2 * t) ^ k ≤ ((∑ w, H.degree w) - S'.card) ^ k :=
            Nat.pow_le_pow_left hd2 k
          calc 2 * (S'.card + t) * ((S'.card + 2 * t) ^ k * S'.card ^ (ℓ - 1 - k))
              = 2 * (S'.card + t) * (S'.card + 2 * t) ^ k * S'.card ^ (ℓ - 1 - k) := by ring
            _ ≤ (∑ w, H.degree w) * ((∑ w, H.degree w) - S'.card) ^ k * S'.card ^ (ℓ - 1 - k) :=
                Nat.mul_le_mul (Nat.mul_le_mul hDge hd2k) (le_refl _)
            _ = (∑ w, H.degree w)
                  * (((∑ w, H.degree w) - S'.card) ^ k * S'.card ^ (ℓ - 1 - k)) := by ring
  obtain ⟨u, wc, hwcyc, hwlen⟩ := ahl_ball_girth_bound hδ2 hℓ1 hbig
  -- Lift the short cycle from `H` to `G` and convert to the `ZMod` cyclic-map form.
  set emb := Embedding.induce (G := G) (↑S' : Set (Fin n)) with hembdef
  have hwc2 : (wc.map emb.toHom).IsCycle := hwcyc.map emb.injective
  have hsupp : ∀ x ∈ (wc.map emb.toHom).support, x ∈ S := by
    intro x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hS'sub (Finset.mem_coe.mp y.2)
  obtain ⟨hk3, hex⟩ := cycle_walk_to_zmod hwc2 hsupp
  refine ⟨(wc.map emb.toHom).length, hk3, ?_, hex⟩
  rw [SimpleGraph.Walk.length_map]
  omega

end ACMax
