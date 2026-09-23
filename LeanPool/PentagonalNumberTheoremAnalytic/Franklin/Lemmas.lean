/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Defs
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Helpers

/-!
# Pentagonal Number Theorem — Lemmas

This file contains the key lemmas for the Pentagonal Number Theorem,
following Franklin's involution argument.

## Main results

* `distinct_parts_disjoint_union`: the partition classes α/β/special are disjoint with union
* `special_partition_char`: characterization of special partitions
* `franklin_involution_bijection`: Franklin's involution is a bijection
* `parity_flip`: Franklin's involution flips even/odd parity
* `signed_partition_main`: pe(n) - po(n) = (-1)^k for pentagonal n, 0 otherwise
-/

@[expose] public section

open Finset

namespace PentagonalNumberTheorem.Franklin

/-- α-partitions and β-partitions are disjoint. -/
theorem DPalpha_inter_DPbeta (n : ℕ) :
    distinctPartitionsAlpha n ∩ distinctPartitionsBeta n = ∅ := by
  simp only [distinctPartitionsAlpha, distinctPartitionsBeta, ← filter_and, filter_eq_empty_iff]
  intro S _
  omega
/-- α-partitions and special partitions are disjoint. -/
theorem DPalpha_inter_DPspecial (n : ℕ) :
    distinctPartitionsAlpha n ∩ distinctPartitionsSpecial n = ∅ := by
  simp only [distinctPartitionsAlpha, distinctPartitionsSpecial, ← filter_and, filter_eq_empty_iff]
  intro S _
  omega
/-- β-partitions and special partitions are disjoint. -/
theorem DPbeta_inter_DPspecial (n : ℕ) :
    distinctPartitionsBeta n ∩ distinctPartitionsSpecial n = ∅ := by
  simp only [distinctPartitionsBeta, distinctPartitionsSpecial, ← filter_and, filter_eq_empty_iff]
  intro S _
  omega
/-- Every distinct partition is in exactly one of α, β, or special. -/
theorem DP_eq_union (n : ℕ) :
    distinctPartitions n =
    distinctPartitionsAlpha n ∪ distinctPartitionsBeta n ∪ distinctPartitionsSpecial n := by
  simp only [distinctPartitionsAlpha, distinctPartitionsBeta, distinctPartitionsSpecial,
    ← filter_or]
  exact (filter_true_of_mem fun S _ => by omega).symm
/-- The pentagonal identity `a * (3 * a - 1) = 3 * a ^ 2 - a`, stated without truncated
subtraction so that `omega` can use it. -/
theorem mul_three_sub_one_add_self (a : ℕ) : a * (3 * a - 1) + a = 3 * a ^ 2 := by
  cases a with
  | zero => rfl
  | succ b => rw [show 3 * (b + 1) - 1 = 3 * b + 2 by omega]; ring
/-- The set smkSet(k) has exactly k elements. -/
theorem SmkSet_card (k : ℕ) (hk : 1 ≤ k) : (smkSet k).card = k := by
  unfold smkSet; rw [Nat.card_Icc]; omega
/-- The sum of smkSet(k) equals (3k²-k)/2. -/
theorem SmkSet_sum (k : ℕ) (hk : 1 ≤ k) : (smkSet k).sum id = (3 * k ^ 2 - k) / 2 := by
  have key := mul_three_sub_one_add_self k
  rw [smkSet, Icc_sum_id, show 2 * k - 1 + 1 - k = k by omega,
    show k + (2 * k - 1) = 3 * k - 1 by omega]
  omega
/-- The set spkSet(k) has exactly k elements. -/
theorem SpkSet_card (k : ℕ) (hk : 1 ≤ k) : (spkSet k).card = k := by
  unfold spkSet; rw [Nat.card_Icc]; omega
/-- The sum of spkSet(k) equals (3k²+k)/2. -/
theorem SpkSet_sum (k : ℕ) (hk : 1 ≤ k) : (spkSet k).sum id = (3 * k ^ 2 + k) / 2 := by
  rw [spkSet, Icc_sum_id, show 2 * k + 1 - (k + 1) = k by omega]
  congr 1
  ring
/-- A nonempty distinct partition whose top run reaches all the way down to its base is the
whole interval `Icc (partBase S) (partMax S)`. -/
theorem DP_eq_Icc_of_run_reaches_base (S : Finset ℕ) (hne : S.Nonempty)
    (h : partMax S - partSlope S + 1 ≤ partBase S) :
    S = Icc (partBase S) (partMax S) := by
  refine Subset.antisymm (fun x hx => mem_Icc.mpr ⟨partBase_le S hne hx, le_partMax S hne hx⟩)
    fun x hx => ?_
  obtain ⟨h1, h2⟩ := mem_Icc.mp hx
  have hs := partSlope_pos S hne
  have hmem := ctr_mem_of_lt S (partMax S) (partMax S - x)
    (show partMax S - x < partSlope S by omega)
  rwa [Nat.sub_sub_self h2] at hmem
/-- A nonempty *special* partition of `n` is exactly the interval `Icc b m` running from its
base `b` to its max `m`. Consequently its slope is the full length `m - b + 1` of that interval,
and `2 * n = s * (b + m)` by Gauss' summation formula. -/
theorem DPspecial_eq_Icc (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsSpecial n)
    (hne : S.Nonempty) :
    S = Icc (partBase S) (partMax S) ∧ partSlope S = partMax S - partBase S + 1 ∧
      2 * n = partSlope S * (partBase S + partMax S) := by
  obtain ⟨hDP, hcond⟩ := mem_filter.mp hS
  have hbm : partBase S ≤ partMax S := partBase_le_partMax S hne
  have hlow : partMax S - partSlope S + 1 ≤ partBase S := by
    rcases hcond with h | h
    · exact absurd (card_pos.mpr hne) (by omega)
    · exact h.2.1
  have hSeq : S = Icc (partBase S) (partMax S) :=
    DP_eq_Icc_of_run_reaches_base S hne hlow
  have hslope : partSlope S = partMax S - partBase S + 1 := by
    conv_lhs => rw [hSeq]
    exact partSlope_Icc hbm
  refine ⟨hSeq, hslope, ?_⟩
  have hsum : S.sum id = n := DP_sum n S hDP
  rw [hSeq] at hsum
  have h2 := Icc_sum_id_mul_two (partBase S) (partMax S)
  rw [hsum, show partMax S + 1 - partBase S = partSlope S by omega] at h2
  omega
/-- For non-pentagonal n ≥ 1, there are no special partitions. -/
theorem DPspecial_empty_of_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    distinctPartitionsSpecial n = ∅ := by
  refine eq_empty_of_forall_notMem fun S hS => ?_
  obtain ⟨hDP, hcond⟩ := mem_filter.mp hS
  have hne : S.Nonempty := by
    rcases hcond with h | h
    · exfalso
      have h0 := DP_sum n S hDP
      rw [card_eq_zero.mp h] at h0
      simp at h0
      omega
    · exact card_pos.mp h.1
  have hcase : partBase S = partSlope S ∨ partBase S = partSlope S + 1 := by
    rcases hcond with h | h
    · exact absurd (card_pos.mpr hne) (by omega)
    · exact h.2.2
  obtain ⟨-, hslope, hsum⟩ := DPspecial_eq_Icc n S hS hne
  have hbm : partBase S ≤ partMax S := partBase_le_partMax S hne
  obtain ⟨t, ht⟩ : ∃ t, partSlope S = t + 1 := ⟨partSlope S - 1, by omega⟩
  have e2 : 3 * (t + 1) ^ 2 = 3 * t ^ 2 + 6 * t + 3 := by ring
  rcases hcase with hc | hc
  · refine h1 (t + 1) (by omega) ?_
    rw [ht, show partBase S = t + 1 by omega, show partMax S = 2 * t + 1 by omega] at hsum
    have e1 : (t + 1) * (t + 1 + (2 * t + 1)) = 3 * t ^ 2 + 5 * t + 2 := by ring
    omega
  · refine h2 (t + 1) (by omega) ?_
    rw [ht, show partBase S = t + 2 by omega, show partMax S = 2 * t + 2 by omega] at hsum
    have e1 : (t + 1) * (t + 2 + (2 * t + 2)) = 3 * t ^ 2 + 7 * t + 4 := by ring
    omega
/-- `x ↦ 3x² − x` is injective on `ℕ`, stated without truncated subtraction. -/
theorem pent_minus_inj {a b : ℕ} (h : 3 * a ^ 2 + b = 3 * b ^ 2 + a) : a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    exfalso; nlinarith
  · exact h'
  · obtain ⟨d, rfl⟩ : ∃ d, a = b + 1 + d := ⟨a - b - 1, by omega⟩
    exfalso; nlinarith
/-- The two pentagonal families never collide: `3j² + j ≠ 3k² − k` when `1 ≤ k`. -/
theorem pent_plus_ne_pent_minus {j k : ℕ} (hk : 1 ≤ k)
    (h : 3 * j ^ 2 + j + k = 3 * k ^ 2) : False := by
  rcases lt_or_ge j k with hjk | hjk
  · obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - j - 1, by omega⟩
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
    nlinarith
/-- For n = (3k²-k)/2 (pentagonal minus), the only special partition is smkSet(k). -/
theorem DPspecial_pent_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    distinctPartitionsSpecial n = {smkSet k} := by
  have ek := mul_three_sub_one_add_self k
  have hk3 : k < 3 * k ^ 2 := by nlinarith
  have hn2 : 2 * n + k = 3 * k ^ 2 := by omega
  have hkk : k ≤ 2 * k - 1 := by omega
  have hsum : (smkSet k).sum id = n := by rw [SmkSet_sum k hk]; omega
  refine eq_singleton_iff_unique_mem.mpr ⟨?_, fun S hS => ?_⟩
  · refine mem_filter.mpr ⟨(mem_DP n _).mpr ⟨?_, hsum⟩, Or.inr ⟨?_, ?_, Or.inl ?_⟩⟩
    · have h5 : 5 * k ≤ 3 * k ^ 2 + 2 := by nlinarith
      simp only [smkSet]
      exact Icc_subset_Icc hk (by omega)
    · rw [SmkSet_card k hk]; omega
    · rw [smkSet, partMax_Icc hkk, partSlope_Icc hkk, partBase_Icc hkk]; omega
    · rw [smkSet, partSlope_Icc hkk, partBase_Icc hkk]; omega
  · obtain ⟨hSDP, hc | ⟨hc, hle, hbs⟩⟩ := mem_filter.mp hS
    · rw [card_eq_zero] at hc
      have h0 := DP_sum n S hSDP
      rw [hc, sum_empty] at h0
      exfalso; omega
    · have hne : S.Nonempty := card_pos.mp hc
      obtain ⟨hSeq, hslope, hsum2⟩ := DPspecial_eq_Icc n S hS hne
      have hbm : partBase S ≤ partMax S := partBase_le_partMax S hne
      have hb1 : 1 ≤ partBase S := DP_pos_mem n S hSDP (partBase_mem S hne)
      rcases hbs with hbs | hbs
      · have hm2 : partMax S = 2 * partBase S - 1 := by omega
        rw [show partSlope S = partBase S by omega,
          show partBase S + partMax S = 3 * partBase S - 1 by omega] at hsum2
        have eb := mul_three_sub_one_add_self (partBase S)
        rw [hSeq, hm2, pent_minus_inj (a := partBase S) (b := k) (by omega)]
        rfl
      · exfalso
        obtain ⟨j, hj⟩ : ∃ j, partBase S = j + 1 := ⟨partBase S - 1, by omega⟩
        rw [show partSlope S = j by omega,
          show partBase S + partMax S = 3 * j + 1 by omega] at hsum2
        have e : j * (3 * j + 1) = 3 * j ^ 2 + j := by ring
        exact pent_plus_ne_pent_minus (j := j) hk (by omega)
/-- The base of `spkSet k` is `k + 1`. -/
theorem partBase_spkSet {k : ℕ} (hk : 1 ≤ k) : partBase (spkSet k) = k + 1 := by
  rw [spkSet]; exact partBase_Icc (by omega)
/-- The largest part of `spkSet k` is `2 * k`. -/
theorem partMax_spkSet {k : ℕ} (hk : 1 ≤ k) : partMax (spkSet k) = 2 * k := by
  rw [spkSet]; exact partMax_Icc (by omega)
/-- `spkSet k` is one single run, so its slope is its whole length `k`. -/
theorem partSlope_spkSet {k : ℕ} (hk : 1 ≤ k) : partSlope (spkSet k) = k := by
  rw [spkSet, partSlope_Icc (show k + 1 ≤ 2 * k by omega)]; omega
/-- The pentagonal numbers of the second kind are pairwise distinct: `a ↦ a * (3 * a + 1)`
is injective. -/
theorem pent_plus_inj {a b : ℕ} (h : a * (3 * a + 1) = 3 * b ^ 2 + b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso; nlinarith
  · exact hab
  · exfalso; nlinarith
/-- No pentagonal number of the first kind is also one of the second kind: with `a = c + 1`,
`a * (3 * a - 1) = (c + 1) * (3 * c + 2)` never equals `b * (3 * b + 1)`. -/
theorem pent_minus_ne_pent_plus (c b : ℕ) : (c + 1) * (3 * c + 2) ≠ 3 * b ^ 2 + b := by
  intro hc
  have e : (c + 1) * (3 * c + 2) + (c + 1) = 3 * (c + 1) ^ 2 := by ring
  exact pent_plus_ne_pent_minus (j := b) (k := c + 1) (by omega) (by omega)
/-- For n = (3k²+k)/2 (pentagonal plus), the only special partition is spkSet(k). -/
theorem DPspecial_pent_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    distinctPartitionsSpecial n = {spkSet k} := by
  have hb : partBase (spkSet k) = k + 1 := partBase_spkSet hk
  have hm : partMax (spkSet k) = 2 * k := partMax_spkSet hk
  have hs : partSlope (spkSet k) = k := partSlope_spkSet hk
  have hspk : spkSet k ∈ distinctPartitionsSpecial n := by
    refine mem_filter.mpr ⟨(mem_DP n _).mpr ⟨?_, ?_⟩, Or.inr ⟨?_, by omega, Or.inr (by omega)⟩⟩
    · rw [spkSet]; exact Icc_subset_Icc (by omega) (by nlinarith)
    · rw [SpkSet_sum k hk]; omega
    · rw [SpkSet_card k hk]; omega
  ext S
  simp only [mem_singleton]
  refine ⟨fun hS => ?_, fun h => h ▸ hspk⟩
  obtain ⟨hSDP, hcond⟩ := mem_filter.mp hS
  have hsum : S.sum id = n := DP_sum n S hSDP
  rcases hcond with hcard | ⟨hcard, hbase, hbs⟩
  · rw [card_eq_zero] at hcard
    rw [hcard, sum_empty] at hsum
    exfalso; omega
  have hne : S.Nonempty := card_pos.mp hcard
  have hs_pos : 0 < partSlope S := partSlope_pos S hne
  have hbm : partBase S ≤ partMax S := partBase_le_partMax S hne
  obtain ⟨hSeq, hslope, hsum2⟩ := DPspecial_eq_Icc n S hS hne
  rcases hbs with hbs | hbs
  · -- `base = slope` would make `n` pentagonal of the first kind, which is impossible.
    obtain ⟨c, hc⟩ : ∃ c, partSlope S = c + 1 := ⟨partSlope S - 1, by omega⟩
    refine absurd ?_ (pent_minus_ne_pent_plus c k)
    rw [← hn, hsum2, hc, show partBase S + partMax S = 3 * c + 2 by omega]
  · -- `base = slope + 1` forces `slope = k`, hence `S = Icc (k + 1) (2 * k) = spkSet k`.
    have hsk : partSlope S = k := by
      refine pent_plus_inj ?_
      rw [← hn, hsum2, show partBase S + partMax S = 3 * partSlope S + 1 by omega]
    rw [hSeq, show partBase S = k + 1 by omega, show partMax S = 2 * k by omega, spkSet]
/-- The Franklin α-operation maps α-partitions into β-partitions. -/
theorem alphaOp_mem_DPbeta (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    alphaOp S ∈ distinctPartitionsBeta n := by
  have hne := DPalpha_nonempty n S hS
  have hDP := DPalpha_mem_DP n S hS
  have hsum : (alphaOp S).sum id = n := by rw [alphaOp_sum n S hS, DP_sum n S hDP]
  have hne' : (alphaOp S).Nonempty := ⟨partMax S + 1, mem_insert_self _ _⟩
  have hlow : ∀ x ∈ alphaOp S, partBase S + 1 ≤ x := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx'
    · have := partBase_le_partMax S hne
      omega
    · have h1 := partBase_le S hne (mem_of_mem_erase (mem_of_mem_erase hx'))
      have h2 := ne_of_mem_erase (mem_of_mem_erase hx')
      omega
  refine mem_filter.mpr ⟨(mem_DP n _).mpr ⟨fun x hx => mem_Icc.mpr ⟨?_, ?_⟩, hsum⟩, ?_⟩
  · have := hlow x hx
    omega
  · exact hsum ▸ single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
  · have hbase := hlow _ (partBase_mem _ hne')
    have hslope := alphaOp_partSlope n S hS
    have hmax := alphaOp_partMax n S hS
    have hcard := card_pos.mpr hne'
    have h2b := DPalpha_max_ge_2base n S hS
    omega
/-- The Franklin β-operation maps β-partitions into α-partitions. -/
theorem betaOp_mem_DPalpha (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    betaOp S ∈ distinctPartitionsAlpha n := by
  have hne := DPbeta_nonempty n S hS
  have hDP := DPbeta_mem_DP n S hS
  have h0 := DP_zero_not_mem n S hDP
  have hspos := partSlope_pos S hne
  have hm2 := DPbeta_max_ge_2slope_add_1 n S hS
  have hmn : partMax S ≤ n := DP_le_mem n S hDP (partMax_mem S hne)
  have hbm := betaOp_partMax n S hS
  have hDP' : betaOp S ∈ distinctPartitions n := by
    refine (mem_DP n _).mpr ⟨fun x hx => ?_, betaOp_sum n S hS ▸ DP_sum n S hDP⟩
    simp only [betaOp, mem_erase, mem_insert] at hx
    obtain ⟨-, rfl | rfl | hx'⟩ := hx
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · exact mem_Icc.mpr ⟨DP_pos_mem n S hDP hx', DP_le_mem n S hDP hx'⟩
  have hsmem : partSlope S ∈ betaOp S := by
    simp only [betaOp, mem_erase, mem_insert]
    exact ⟨by omega, Or.inl trivial⟩
  have hcard : 0 < (betaOp S).card := card_pos.mpr ⟨_, hsmem⟩
  have hrun : ∀ j < partSlope S, partMax S - 1 - j ∈ betaOp S := by
    intro j hj
    have hps : partSlope S = consecutiveTopRun S (partMax S) := rfl
    simp only [betaOp, mem_erase, mem_insert]
    refine ⟨by omega, ?_⟩
    rcases Nat.lt_or_ge (j + 1) (partSlope S) with h | h
    · refine Or.inr (Or.inr ?_)
      rw [Nat.sub_sub]
      exact ctr_mem_of_lt S _ (1 + j) (by omega)
    · exact Or.inr (Or.inl (by omega))
  have hslope : partSlope S ≤ partSlope (betaOp S) := by
    by_contra hcon
    have hlt := not_le.mp hcon
    refine ctr_not_mem_boundary (betaOp S) (partMax (betaOp S))
      (DP_zero_not_mem n _ hDP') (partMax_mem _ (card_pos.mp hcard)) ?_
    change partMax (betaOp S) - partSlope (betaOp S) ∈ betaOp S
    rw [hbm]
    exact hrun _ hlt
  have hbase := betaOp_partBase n S hS
  exact mem_filter.mpr ⟨hDP', by omega⟩
/-- The β-operation is a left inverse of the α-operation. -/
theorem betaOp_alphaOp (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    betaOp (alphaOp S) = S := by
  have hne := DPalpha_nonempty n S hS
  have hbm := partBase_le_partMax S hne
  have hb_mem := partBase_mem S hne
  have hmb_mem := DPalpha_m_sub_b_add_1_mem n S hS
  simp only [betaOp, alphaOp_partSlope n S hS, alphaOp_partMax n S hS]
  simp only [alphaOp]
  ext x
  simp only [mem_insert, mem_erase, ne_eq]
  constructor
  · rintro ⟨hx, rfl | rfl | rfl | ⟨-, -, hx'⟩⟩
    · exact hb_mem
    · rw [show partMax S + 1 - partBase S = partMax S - partBase S + 1 by omega]
      exact hmb_mem
    · exact absurd rfl hx
    · exact hx'
  · intro hx
    have hle := le_partMax S hne hx
    refine ⟨by omega, ?_⟩
    by_cases h1 : x = partBase S
    · exact Or.inl h1
    · by_cases h2 : x = partMax S - partBase S + 1
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inr ⟨h2, h1, hx⟩))
/-- The α-operation is a left inverse of the β-operation. -/
theorem alphaOp_betaOp (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    alphaOp (betaOp S) = S := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have hspos := partSlope_pos S hne
  have hm2 := DPbeta_max_ge_2slope_add_1 n S hS
  have hs_not := DPbeta_slope_not_mem n S hS
  have hms_not := DPbeta_m_sub_s_not_mem n S hS
  have hmax := partMax_mem S hne
  simp only [alphaOp, betaOp_partBase n S hS, betaOp_partMax n S hS]
  simp only [betaOp]
  ext x
  simp only [mem_insert, mem_erase, ne_eq]
  constructor
  · rintro (rfl | ⟨h1, h2, -, rfl | rfl | hx⟩)
    · rw [show partMax S - 1 + 1 = partMax S by omega]
      exact hmax
    · exact absurd rfl h2
    · exact absurd (by omega) h1
    · exact hx
  · intro hx
    by_cases hxm : x = partMax S
    · exact Or.inl (by omega)
    · refine Or.inr ⟨?_, ?_, hxm, Or.inr (Or.inr hx)⟩
      · rintro rfl
        exact hms_not (by rwa [show partMax S - 1 - partSlope S + 1 = partMax S - partSlope S
          by omega] at hx)
      · rintro rfl
        exact hs_not hx
/-- `alphaOp` is injective on `distinctPartitionsAlpha n`, since `betaOp` is a left inverse. -/
theorem alphaOp_inj (n : ℕ) {S T : Finset ℕ} (hS : S ∈ distinctPartitionsAlpha n)
    (hT : T ∈ distinctPartitionsAlpha n) (h : alphaOp S = alphaOp T) : S = T := by
  rw [← betaOp_alphaOp n S hS, ← betaOp_alphaOp n T hT, h]
/-- Franklin's involution gives a bijection: |α(n)| = |β(n)|. -/
theorem DPalpha_card_eq_DPbeta_card (n : ℕ) :
    (distinctPartitionsAlpha n).card = (distinctPartitionsBeta n).card :=
  card_bij (fun S _ => alphaOp S) (fun S hS => alphaOp_mem_DPbeta n S hS)
    (fun _ h₁ _ h₂ h => alphaOp_inj n h₁ h₂ h)
    fun T hT => ⟨betaOp T, betaOp_mem_DPalpha n T hT, alphaOp_betaOp n T hT⟩
/-- The α-operation preserves the number of parts. -/
theorem alphaOp_card (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    (alphaOp S).card + 1 = S.card := by
  have hne := DPalpha_nonempty n S hS
  have hb : partBase S ∈ S := partBase_mem S hne
  have hm : partMax S - partBase S + 1 ∈ S := DPalpha_m_sub_b_add_1_mem n S hS
  have hbm : partBase S ≠ partMax S - partBase S + 1 := DPalpha_base_ne_m_sub_b_add_1 n S hS
  have h2 : 1 < S.card := one_lt_card.mpr ⟨_, hb, _, hm, hbm⟩
  have hnot : partMax S + 1 ∉ (S.erase (partBase S)).erase (partMax S - partBase S + 1) :=
    fun h => partMax_succ_not_mem S hne (mem_of_mem_erase (mem_of_mem_erase h))
  simp only [alphaOp]
  rw [card_insert_of_notMem hnot, card_erase_of_mem (mem_erase_of_ne_of_mem hbm.symm hm),
    card_erase_of_mem hb]
  omega
/-- The β-operation preserves the number of parts. -/
theorem betaOp_card (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    (betaOp S).card = S.card + 1 := by
  have hs : partSlope S ∉ S := DPbeta_slope_not_mem n S hS
  have hms : partMax S - partSlope S ∉ S := DPbeta_m_sub_s_not_mem n S hS
  have hne : partSlope S ≠ partMax S - partSlope S := DPbeta_slope_ne_m_sub_slope n S hS
  have hm : partMax S ∈ S := partMax_mem S (DPbeta_nonempty n S hS)
  simp only [betaOp]
  rw [card_erase_of_mem (mem_insert_of_mem (mem_insert_of_mem hm)),
    card_insert_of_notMem (by simp [hne, hs]), card_insert_of_notMem hms]
  omega
/-- Franklin's involution refined by a condition on the number of parts: `α` matches the members
of `𝒫_α(n)` whose size satisfies `p` with those of `𝒫_β(n)` whose size satisfies `q`, provided
`p (a + 1)` and `q a` always agree (recall `|α(S)| + 1 = |S|`). -/
theorem DPalpha_filter_card_eq (n : ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a : ℕ, p (a + 1) ↔ q a) :
    ((distinctPartitionsAlpha n).filter fun S => p S.card).card =
      ((distinctPartitionsBeta n).filter fun S => q S.card).card := by
  refine card_bij (fun S _ => alphaOp S) ?_ (fun _ h₁ _ h₂ h =>
    alphaOp_inj n (mem_filter.mp h₁).1 (mem_filter.mp h₂).1 h) ?_
  · intro S hS
    obtain ⟨hS, hp⟩ := mem_filter.mp hS
    exact mem_filter.mpr ⟨alphaOp_mem_DPbeta n S hS, (hpq _).mp (by rwa [alphaOp_card n S hS])⟩
  · intro T hT
    obtain ⟨hT, hq⟩ := mem_filter.mp hT
    refine ⟨betaOp T, mem_filter.mpr ⟨betaOp_mem_DPalpha n T hT, ?_⟩, alphaOp_betaOp n T hT⟩
    rw [betaOp_card n T hT]
    exact (hpq _).mpr hq
/-- |{S ∈ α(n) : |S| odd}| = |{S ∈ β(n) : |S| even}|. -/
theorem DPalpha_odd_card_eq_DPbeta_even_card (n : ℕ) :
    ((distinctPartitionsAlpha n).filter (fun S => S.card % 2 = 1)).card =
    ((distinctPartitionsBeta n).filter (fun S => S.card % 2 = 0)).card :=
  DPalpha_filter_card_eq n (· % 2 = 1) (· % 2 = 0) fun _ => by omega
/-- |{S ∈ α(n) : |S| even}| = |{S ∈ β(n) : |S| odd}|. -/
theorem DPalpha_even_card_eq_DPbeta_odd_card (n : ℕ) :
    ((distinctPartitionsAlpha n).filter (fun S => S.card % 2 = 0)).card =
    ((distinctPartitionsBeta n).filter (fun S => S.card % 2 = 1)).card :=
  DPalpha_filter_card_eq n (· % 2 = 0) (· % 2 = 1) fun _ => by omega
/-- Any filtered count of `distinctPartitions n` splits along the α/β/special decomposition. -/
theorem DP_card_filter_split (n : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] :
    ((distinctPartitions n).filter P).card =
      ((distinctPartitionsAlpha n).filter P).card + ((distinctPartitionsBeta n).filter P).card +
        ((distinctPartitionsSpecial n).filter P).card := by
  have hab : Disjoint (distinctPartitionsAlpha n) (distinctPartitionsBeta n) :=
    disjoint_iff_inter_eq_empty.mpr (DPalpha_inter_DPbeta n)
  have hac : Disjoint (distinctPartitionsAlpha n) (distinctPartitionsSpecial n) :=
    disjoint_iff_inter_eq_empty.mpr (DPalpha_inter_DPspecial n)
  have hbc : Disjoint (distinctPartitionsBeta n) (distinctPartitionsSpecial n) :=
    disjoint_iff_inter_eq_empty.mpr (DPbeta_inter_DPspecial n)
  rw [DP_eq_union, filter_union, filter_union,
    card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_filter_filter hac, disjoint_filter_filter hbc⟩),
    card_union_of_disjoint (disjoint_filter_filter hab)]
/-- pe(n) - po(n) equals the signed count of special partitions. -/
theorem pe_minus_po_eq_special (n : ℕ) :
    (pe n : ℤ) - po n =
    ((distinctPartitionsSpecial n).filter (fun S => S.card % 2 = 0)).card -
    ((distinctPartitionsSpecial n).filter (fun S => S.card % 2 = 1)).card := by
  have h0 := DP_card_filter_split n fun S => S.card % 2 = 0
  have h1 := DP_card_filter_split n fun S => S.card % 2 = 1
  have he := DPalpha_even_card_eq_DPbeta_odd_card n
  have ho := DPalpha_odd_card_eq_DPbeta_even_card n
  simp only [pe, po, distinctPartitionsEven, distinctPartitionsOdd]
  omega
/-- **Lemma 24 (Source), case n = 0**: `p_e(0) − p_o(0) = 1`. -/
theorem pe_minus_po_zero : (pe 0 : ℤ) - po 0 = 1 := by decide
/-- For non-pentagonal n ≥ 1, pe(n) - po(n) = 0. -/
theorem pe_minus_po_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = 0 := by
  rw [pe_minus_po_eq_special, DPspecial_empty_of_nonpent n hn h1 h2]
  simp
/-- The signed count of a one-element family of partitions with `k` parts is `(-1) ^ k`. -/
theorem signed_card_of_singleton (T : Finset ℕ) (k : ℕ) (hT : T.card = k) :
    ((({T} : Finset (Finset ℕ)).filter (fun S => S.card % 2 = 0)).card : ℤ) -
      (({T} : Finset (Finset ℕ)).filter (fun S => S.card % 2 = 1)).card = (-1) ^ k := by
  rw [filter_singleton, filter_singleton, hT]
  rcases Nat.even_or_odd k with h | h
  · have hk : k % 2 = 0 := Nat.even_iff.mp h
    rw [ite_eq_left hk, ite_eq_right (by omega), h.neg_one_pow]
    simp
  · have hk : k % 2 = 1 := Nat.odd_iff.mp h
    rw [ite_eq_right (by omega), ite_eq_left hk, h.neg_one_pow]
    simp
/-- For n = (3k²-k)/2, pe(n) - po(n) = (-1)^k. -/
theorem pe_minus_po_pent_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    (pe n : ℤ) - po n = (-1) ^ k := by
  rw [pe_minus_po_eq_special, DPspecial_pent_minus n k hk hn]
  exact signed_card_of_singleton _ k (SmkSet_card k hk)
/-- For n = (3k²+k)/2, pe(n) - po(n) = (-1)^k. -/
theorem pe_minus_po_pent_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    (pe n : ℤ) - po n = (-1) ^ k := by
  rw [pe_minus_po_eq_special, DPspecial_pent_plus n k hk hn]
  exact signed_card_of_singleton _ k (SpkSet_card k hk)

end PentagonalNumberTheorem.Franklin
