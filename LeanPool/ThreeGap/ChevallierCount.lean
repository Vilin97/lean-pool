/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.ChevallierGapBound
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Chevallier's Lemma: the gap count is `≤ n − m + 1` (Chevallier 1996, Lemma 1.3)

The combinatorial heart of the higher-dimensional three-distance bounds (`g_∞ ≤ 2^d+1`, `g_2 ≤ 5`),
following N. Chevallier, *Distances dans la suite des multiples d'un point du tore à deux
dimensions*,
Acta Arith. **74** (1996), Lemma 1.3.

For a base point with an isometry, the nearest-neighbour distance of the `q`-th orbit point among
`{x_0, …, x_N}` is `D_q = min_{1 ≤ j ≤ max(q, N−q)} d(x_0, x_j)`, because (isometry) the distances
from
`x_q` are `d(x_0, x_{j})` for offsets `j`, and the offset range is `max(q, N−q)`. The minimum of the
"cost" `r(j) = d(x_0, x_j)` over `[1, M]` is attained at the **record denominator** `q_{i*}` with
`q_{i*} ≤ M < q_{i*+1}`. As `q` ranges over `[0,N]`, `M = max(q, N−q) ∈ [⌈N/2⌉, N]`, so `i* ∈ [m,
n]`
where `q_n ≤ N < q_{n+1}` and `2q_m ≤ N < 2q_{m+1}`. Hence the distinct gap values lie in
`{r(q_m), …, r(q_n)}` — **at most `n − m + 1`** of them. This is exactly the input
`ChevallierGapBound.gap_count_doubling` needs (`g_dist = n−m` or `n−m+1`).

This file isolates the count as a pure statement about a cost function `r : ℕ → ℝ` and its records
(`ChevallierGapBound.bestDenom`); the isometry reduction `D_q = min … r` is the geometric input.

Axiom-clean.
-/

namespace ThreeGap.Chevallier

variable (r : ℕ → ℝ)

/-- The record costs `r(q_i)` are **strictly decreasing in `i`** (each record is a strictly better
minimum). -/
theorem bestDenom_cost_strictAnti (hr : RecordsContinue r) :
    StrictAnti (fun n => r (bestDenom r hr n)) :=
  strictAnti_nat_of_succ_lt (fun n => bestDenom_cost_lt r hr n)

/-- The record costs `r(q_i)` are **non-increasing in `i`** (each record is a new minimum). -/
theorem bestDenom_cost_antitone (hr : RecordsContinue r) {k i : ℕ} (h : k ≤ i) :
    r (bestDenom r hr i) ≤ r (bestDenom r hr k) :=
  (bestDenom_cost_strictAnti r hr).antitone h

/-- **Strict record floor.** Every `j ∈ [1, q_k)` has cost **strictly** above the record `r(q_k)`:
`r(q_k) < r j` for `1 ≤ j < q_k`. (This is the full best-approximation property: `q_k` strictly
beats
*every* smaller positive denominator, not just those in its own bracket.) -/
theorem bestDenom_strict_floor (hr : RecordsContinue r) (k : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j < bestDenom r hr k) : r (bestDenom r hr k) < r j := by
  obtain ⟨i, hi1, hi2⟩ := bestDenom_bracket r hr hj1
  have hik : i < k := by
    by_contra hc
    push Not at hc
    have : bestDenom r hr k ≤ bestDenom r hr i := (bestDenom_strictMono r hr).monotone hc
    omega
  have hlt : r (bestDenom r hr k) < r (bestDenom r hr i) := bestDenom_cost_strictAnti r hr hik
  have hle : r (bestDenom r hr i) ≤ r j := by
    rcases eq_or_lt_of_le hi1 with h | h
    · rw [h]
    · exact bestDenom_record r hr i h hi2
  exact lt_of_lt_of_le hlt hle

/-- **Record floor.** Every `j ∈ [1, q_{i+1})` has cost `≥ r(q_i)`: the cost stays above the `i`-th
record until the `(i+1)`-th. (So `min_{1 ≤ j ≤ M} r(j) = r(q_i)` when `q_i ≤ M < q_{i+1}`.) -/
theorem record_floor (hr : RecordsContinue r) (i : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j < bestDenom r hr (i + 1)) : r (bestDenom r hr i) ≤ r j := by
  obtain ⟨k, hk1, hk2⟩ := bestDenom_bracket r hr hj1
  have hki : k ≤ i := by
    by_contra hc
    push Not at hc
    have : bestDenom r hr (i + 1) ≤ bestDenom r hr k :=
      (bestDenom_strictMono r hr).monotone (by omega)
    omega
  have hrk : r (bestDenom r hr k) ≤ r j := by
    rcases eq_or_lt_of_le hk1 with h | h
    · rw [h]
    · exact bestDenom_record r hr k h hk2
  exact le_trans (bestDenom_cost_antitone r hr hki) hrk

/-- The nearest-neighbour distance of the `q`-th point among `{x_0,…,x_N}`, abstractly: the minimum
cost `min_{1 ≤ j ≤ max(q, N−q)} r(j)` (junk `0` outside the valid range). -/
noncomputable def gapVal (N q : ℕ) : ℝ :=
  if h : (Finset.Icc 1 (max q (N - q))).Nonempty then
    (Finset.Icc 1 (max q (N - q))).inf' h r else 0

/-- **The gap value is a record cost in the band `[m, n]`.** For `q ∈ [0,N]` (`N ≥ 2`), with `n, m`
the record indices bracketing `N` and `N/2`, the nearest-neighbour distance `gapVal N q` equals
`r(q_i)` for some `i ∈ [m, n]`. -/
theorem gapVal_eq_record (hr : RecordsContinue r) {N : ℕ} (hN : 2 ≤ N) {n m : ℕ}
    (_hn1 : bestDenom r hr n ≤ N) (hn2 : N < bestDenom r hr (n + 1))
    (hm1 : 2 * bestDenom r hr m ≤ N) (_hm2 : N < 2 * bestDenom r hr (m + 1))
    {q : ℕ} (hq : q ≤ N) :
    ∃ i, m ≤ i ∧ i ≤ n ∧ gapVal r N q = r (bestDenom r hr i) := by
  have hMq : q ≤ max q (N - q) := le_max_left _ _
  have hMNq : N - q ≤ max q (N - q) := le_max_right _ _
  have hM1 : 1 ≤ max q (N - q) := by omega
  have hne : (Finset.Icc 1 (max q (N - q))).Nonempty := ⟨1, by rw [Finset.mem_Icc]; omega⟩
  obtain ⟨i, hi1, hi2⟩ := bestDenom_bracket r hr hM1
  have hin : i ≤ n := by
    by_contra hc; push Not at hc
    have : bestDenom r hr (n + 1) ≤ bestDenom r hr i :=
      (bestDenom_strictMono r hr).monotone (by omega)
    omega
  have hmi : m ≤ i := by
    by_contra hc; push Not at hc
    have hmono : bestDenom r hr (i + 1) ≤ bestDenom r hr m :=
      (bestDenom_strictMono r hr).monotone (by omega)
    omega
  refine ⟨i, hmi, hin, ?_⟩
  have hgap : gapVal r N q = (Finset.Icc 1 (max q (N - q))).inf' hne r := by
    rw [gapVal, dif_pos hne]
  rw [hgap]
  apply le_antisymm
  · exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨bestDenom_pos r hr i, hi1⟩)
  · refine Finset.le_inf' _ _ (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    exact record_floor r hr i hj.1 (by omega)

/-- **Chevallier's Lemma, upper bound (`g_dist ≤ n − m + 1`).** For `N ≥ 2`, the number of distinct
nearest-neighbour distances `{gapVal N q : 0 ≤ q ≤ N}` is at most `n − m + 1`, where `q_n ≤ N <
q_{n+1}` and `2q_m ≤ N < 2q_{m+1}`. This is exactly the gap-count hypothesis fed to
`ChevallierGapBound.gap_count_doubling` to obtain `g ≤ K + 1`. -/
theorem chevallier_count (hr : RecordsContinue r) {N : ℕ} (hN : 2 ≤ N) {n m : ℕ}
    (hn1 : bestDenom r hr n ≤ N) (hn2 : N < bestDenom r hr (n + 1))
    (hm1 : 2 * bestDenom r hr m ≤ N) (hm2 : N < 2 * bestDenom r hr (m + 1)) :
    ((Finset.range (N + 1)).image (gapVal r N)).card ≤ n - m + 1 := by
  have hsub : (Finset.range (N + 1)).image (gapVal r N)
      ⊆ (Finset.Icc m n).image (fun i => r (bestDenom r hr i)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    rw [Finset.mem_range] at hq
    obtain ⟨i, hmi, hin, hgap⟩ :=
      gapVal_eq_record r hr hN hn1 hn2 hm1 hm2 (q := q) (by omega)
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_Icc.mpr ⟨hmi, hin⟩, hgap.symm⟩
  calc ((Finset.range (N + 1)).image (gapVal r N)).card
      ≤ ((Finset.Icc m n).image (fun i => r (bestDenom r hr i))).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc m n).card := Finset.card_image_le
    _ = n + 1 - m := Nat.card_Icc m n
    _ ≤ n - m + 1 := by omega

/-- **`g_dist ≤ K + 1`, abstractly (Chevallier's count + the growth inequality).** If the record
denominators satisfy the doubling growth `2 q_k ≤ q_{k+K}` (Shutov: `K = 2^d` for `L^∞`, Romanov:
`K = 4` for the Euclidean plane), then the number of distinct nearest-neighbour distances is at most
`K + 1`. Proof: `chevallier_count` gives `≤ n − m + 1`, and `index_bound_doubling` gives `n − m ≤ K`
from the growth. This is the complete combinatorial core of `g_∞ ≤ 2^d + 1` and `g_2 ≤ 5` — only the
geometric isometry reduction (actual nearest-neighbour distance `=` `gapVal`) and the growth for the
specific cost remain to instantiate. -/
theorem chevallier_gap_count_le (hr : RecordsContinue r) (K : ℕ)
    (hgrowth : ∀ k, 2 * bestDenom r hr k ≤ bestDenom r hr (k + K))
    {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.range (N + 1)).image (gapVal r N)).card ≤ K + 1 := by
  obtain ⟨n, hn1, hn2⟩ := bestDenom_bracket r hr (by omega : 1 ≤ N)
  obtain ⟨m, hm1, hm2⟩ := bestDenom_bracket2 r hr hN
  have hcount := chevallier_count r hr hN hn1 hn2 hm1 hm2
  have hnm : n ≤ m + K :=
    index_bound_doubling (fun k => (bestDenom r hr k : ℤ)) (bestDenom_int_strictMono r hr) K
      (fun k => by exact_mod_cast hgrowth k) (N := (N : ℤ)) (m := m) (n := n)
      (by exact_mod_cast hn1) (by exact_mod_cast hm2)
  omega

end ThreeGap.Chevallier
