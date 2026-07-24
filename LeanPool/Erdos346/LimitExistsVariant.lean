/-
Copyright (c) 2026 KitaKen1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KitaKen1
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 346, limit-exists interpretation

This file formalizes an attempted Lean 4 proof of the limit-exists
interpretation of Erdős Problem 346.

Original problem:
T. F. Bloom, Erdős Problem #346,
https://www.erdosproblems.com/346

Background references:
* P. Erdős and R. L. Graham, Old and New Problems and Results in
  Combinatorial Number Theory, Monographie No. 28 de L'Enseignement
  Mathématique, 1980.
* R. L. Graham, "A Property of Fibonacci Numbers", Fibonacci Quarterly 2
  (1964), 1-10.

Forum relation:
In the Erdős Problems discussion thread for Problem #346, Liam Price submitted
an answer for the convergence-from-hypotheses interpretation.  Dogmachine then
proposed the limit-exists interpretation, citing ambiguity in the Erdős-Graham
phrasing and Graham's earlier formulation.  This file formalizes that
limit-exists interpretation:

if the two deletion hypotheses hold, the sequence has a uniform ratio gap, and
`a (n+1) / a n` tends to a real number `L > 1`, then the quotient sequence tends
to the golden ratio.

AI usage disclosure:
The Lean formalization and accompanying writeup were prepared with assistance
from Codex and ChatGPT.  The final mathematical claims and public presentation
remain the author's responsibility.
-/

open scoped BigOperators Topology goldenRatio
open Filter Set

namespace Erdos346

noncomputable section

/-- Finite subset sums using only terms with indices in `I`. -/
def subsetSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {t | ∃ F : Finset ℕ, ↑F ⊆ I ∧ ∑ i ∈ F, a i = t}

/-- Completeness of the subsequence with index set `I`: every sufficiently large
natural number is a finite subset sum of terms indexed by `I`. -/
def IsCompleteOn (a : ℕ → ℕ) (I : Set ℕ) : Prop :=
  ∃ H : ℕ, ∀ n : ℕ, H ≤ n → n ∈ subsetSums a I

/-- The least threshold from which a complete subsequence is complete, once a
proof of completeness is supplied. -/
def leastCompleteThreshold
    (a : ℕ → ℕ) (I : Set ℕ) (hcomplete : IsCompleteOn a I) : ℕ :=
  by
    classical
    exact Nat.find hcomplete

lemma leastCompleteThreshold_spec
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I) :
    ∀ t : ℕ, leastCompleteThreshold a I hcomplete ≤ t →
      t ∈ subsetSums a I := by
  classical
  unfold leastCompleteThreshold
  exact Nat.find_spec hcomplete

lemma leastCompleteThreshold_le_of_complete_from
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I) {H : ℕ}
    (hH : ∀ t : ℕ, H ≤ t → t ∈ subsetSums a I) :
    leastCompleteThreshold a I hcomplete ≤ H := by
  classical
  unfold leastCompleteThreshold
  by_contra hnot
  have hlt : H < Nat.find hcomplete := Nat.lt_of_not_ge hnot
  exact (Nat.find_min hcomplete hlt) hH

lemma exists_hole_of_lt_leastCompleteThreshold
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I) {B : ℕ}
    (hB : B < leastCompleteThreshold a I hcomplete) :
    ∃ t : ℕ, B ≤ t ∧ t ∉ subsetSums a I := by
  classical
  by_contra hno
  have hfromB : ∀ t : ℕ, B ≤ t → t ∈ subsetSums a I := by
    intro t htB
    by_contra htmiss
    exact hno ⟨t, htB, htmiss⟩
  have hle : leastCompleteThreshold a I hcomplete ≤ B :=
    leastCompleteThreshold_le_of_complete_from hcomplete hfromB
  omega

lemma lt_leastCompleteThreshold_of_exists_hole
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I) {B : ℕ}
    (hhole : ∃ t : ℕ, B ≤ t ∧ t ∉ subsetSums a I) :
    B < leastCompleteThreshold a I hcomplete := by
  by_contra hnot
  have hle : leastCompleteThreshold a I hcomplete ≤ B := Nat.le_of_not_gt hnot
  obtain ⟨t, hBt, htmiss⟩ := hhole
  exact htmiss (leastCompleteThreshold_spec hcomplete t (le_trans hle hBt))

theorem lt_leastCompleteThreshold_iff_exists_hole
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I) {B : ℕ} :
    B < leastCompleteThreshold a I hcomplete ↔
      ∃ t : ℕ, B ≤ t ∧ t ∉ subsetSums a I :=
  ⟨exists_hole_of_lt_leastCompleteThreshold hcomplete,
    lt_leastCompleteThreshold_of_exists_hole hcomplete⟩

lemma pred_leastCompleteThreshold_not_mem
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I)
    (hpos : 0 < leastCompleteThreshold a I hcomplete) :
    leastCompleteThreshold a I hcomplete - 1 ∉ subsetSums a I := by
  classical
  let K := leastCompleteThreshold a I hcomplete
  intro hmem
  have hfromPred : ∀ t : ℕ, K - 1 ≤ t → t ∈ subsetSums a I := by
    intro t ht
    by_cases htK : K ≤ t
    · exact leastCompleteThreshold_spec hcomplete t (by simpa [K] using htK)
    · have ht_eq : t = K - 1 := by omega
      simpa [K, ht_eq] using hmem
  have hle : leastCompleteThreshold a I hcomplete ≤ K - 1 := by
    simpa [K] using
      (leastCompleteThreshold_le_of_complete_from
        (a := a) (I := I) hcomplete hfromPred)
  omega

lemma exists_hole_at_pred_leastCompleteThreshold
    {a : ℕ → ℕ} {I : Set ℕ} (hcomplete : IsCompleteOn a I)
    (hpos : 0 < leastCompleteThreshold a I hcomplete) :
    ∃ t : ℕ, t = leastCompleteThreshold a I hcomplete - 1 ∧
      t ∉ subsetSums a I :=
  ⟨leastCompleteThreshold a I hcomplete - 1, rfl,
    pred_leastCompleteThreshold_not_mem hcomplete hpos⟩

/-- Finite subset sums using only terms in `I` up to index `n`. -/
def prefixSubsetSums (a : ℕ → ℕ) (I : Set ℕ) (n : ℕ) : Set ℕ :=
  subsetSums a (I ∩ Set.Iic n)

/-- The finite subset sums up to `n` cover the whole interval `[H, T]`. -/
def CoversInterval (a : ℕ → ℕ) (I : Set ℕ) (n H T : ℕ) : Prop :=
  ∀ t : ℕ, H ≤ t → t ≤ T → t ∈ prefixSubsetSums a I n

lemma exists_prefixCoverThreshold_vacuous
    {a : ℕ → ℕ} {I : Set ℕ} {n T : ℕ} :
    ∃ H : ℕ, CoversInterval a I n H T := by
  refine ⟨T + 1, ?_⟩
  intro t htH htT
  omega

/-- The least lower endpoint `H` from which the prefix through `n` covers
`[H, T]`.  This is always defined: `H = T + 1` gives a vacuous cover. -/
def leastPrefixCoverThreshold (a : ℕ → ℕ) (I : Set ℕ) (n T : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_prefixCoverThreshold_vacuous (a := a) (I := I) (n := n) (T := T))

/-- The least prefix-cover threshold really covers from itself. -/
lemma leastPrefixCoverThreshold_cover
    {a : ℕ → ℕ} {I : Set ℕ} {n T : ℕ} :
    CoversInterval a I n (leastPrefixCoverThreshold a I n T) T := by
  classical
  unfold leastPrefixCoverThreshold
  exact Nat.find_spec (exists_prefixCoverThreshold_vacuous (a := a) (I := I) (n := n) (T := T))

/-- Any prefix-cover threshold bounds the least such threshold. -/
lemma leastPrefixCoverThreshold_le_of_cover
    {a : ℕ → ℕ} {I : Set ℕ} {n T H : ℕ}
    (hcover : CoversInterval a I n H T) :
    leastPrefixCoverThreshold a I n T ≤ H := by
  classical
  unfold leastPrefixCoverThreshold
  by_contra hnot
  have hlt :
      H < Nat.find
        (exists_prefixCoverThreshold_vacuous (a := a) (I := I) (n := n) (T := T)) :=
    Nat.lt_of_not_ge hnot
  exact (Nat.find_min
    (exists_prefixCoverThreshold_vacuous (a := a) (I := I) (n := n) (T := T))
    hlt) hcover

lemma CoversInterval.mono_lower
    {a : ℕ → ℕ} {I : Set ℕ} {n H H' T : ℕ}
    (hcover : CoversInterval a I n H T) (hHH' : H ≤ H') :
    CoversInterval a I n H' T := by
  intro t htH' htT
  exact hcover t (le_trans hHH' htH') htT

lemma not_coversInterval_iff_exists_prefix_hole
    {a : ℕ → ℕ} {I : Set ℕ} {n H T : ℕ} :
    ¬ CoversInterval a I n H T ↔
      ∃ t : ℕ, H ≤ t ∧ t ≤ T ∧ t ∉ prefixSubsetSums a I n := by
  classical
  simp [CoversInterval]

lemma exists_prefix_hole_of_lt_leastPrefixCoverThreshold
    {a : ℕ → ℕ} {I : Set ℕ} {n T B : ℕ}
    (hB : B < leastPrefixCoverThreshold a I n T) :
    ∃ t : ℕ, B ≤ t ∧ t ≤ T ∧ t ∉ prefixSubsetSums a I n := by
  classical
  have hnot : ¬ CoversInterval a I n B T := by
    unfold leastPrefixCoverThreshold at hB
    exact Nat.find_min
      (exists_prefixCoverThreshold_vacuous (a := a) (I := I) (n := n) (T := T))
      hB
  exact not_coversInterval_iff_exists_prefix_hole.mp hnot

lemma lt_leastPrefixCoverThreshold_of_exists_prefix_hole
    {a : ℕ → ℕ} {I : Set ℕ} {n T B : ℕ}
    (hhole : ∃ t : ℕ, B ≤ t ∧ t ≤ T ∧ t ∉ prefixSubsetSums a I n) :
    B < leastPrefixCoverThreshold a I n T := by
  by_contra hnot
  have hleast_le : leastPrefixCoverThreshold a I n T ≤ B := Nat.le_of_not_gt hnot
  obtain ⟨t, hBt, htT, htmiss⟩ := hhole
  have hcoverB : CoversInterval a I n B T :=
    CoversInterval.mono_lower leastPrefixCoverThreshold_cover hleast_le
  exact htmiss (hcoverB t hBt htT)

theorem lt_leastPrefixCoverThreshold_iff_exists_prefix_hole
    {a : ℕ → ℕ} {I : Set ℕ} {n T B : ℕ} :
    B < leastPrefixCoverThreshold a I n T ↔
      ∃ t : ℕ, B ≤ t ∧ t ≤ T ∧ t ∉ prefixSubsetSums a I n :=
  ⟨exists_prefix_hole_of_lt_leastPrefixCoverThreshold,
    lt_leastPrefixCoverThreshold_of_exists_prefix_hole⟩

/-- The first finite margin in the `start = M + 2` seed. -/
def nextSeedMargin (a : ℕ → ℕ) (M : ℕ) : ℕ :=
  a (M + 2) - a (M + 1)

/-- The second finite margin in the `start = M + 2` seed. -/
def pairSeedMargin (a : ℕ → ℕ) (M : ℕ) : ℕ :=
  a (M + 1) + a (M + 2) - a (M + 3)

lemma nextSeedMargin_lt_least_of_not_seed_keep
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2))
    (hnot :
      ¬ leastPrefixCoverThreshold a I M (a (M + 2) - 1) +
          a (M + 1) ≤ a (M + 2)) :
    nextSeedMargin a M <
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) := by
  dsimp [nextSeedMargin]
  omega

lemma pairSeedMargin_lt_least_of_not_seed_margin
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hpair : a (M + 3) ≤ a (M + 1) + a (M + 2))
    (hnot :
      ¬ leastPrefixCoverThreshold a I M (a (M + 2) - 1) +
          a (M + 3) ≤ a (M + 1) + a (M + 2)) :
    pairSeedMargin a M <
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) := by
  dsimp [pairSeedMargin]
  omega

lemma exists_prefix_hole_of_not_seed_keep
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2))
    (hnot :
      ¬ leastPrefixCoverThreshold a I M (a (M + 2) - 1) +
          a (M + 1) ≤ a (M + 2)) :
    ∃ t : ℕ,
      nextSeedMargin a M ≤ t ∧ t ≤ a (M + 2) - 1 ∧
        t ∉ prefixSubsetSums a I M :=
  exists_prefix_hole_of_lt_leastPrefixCoverThreshold
    (nextSeedMargin_lt_least_of_not_seed_keep hnext hnot)

lemma exists_prefix_hole_of_not_seed_margin
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hpair : a (M + 3) ≤ a (M + 1) + a (M + 2))
    (hnot :
      ¬ leastPrefixCoverThreshold a I M (a (M + 2) - 1) +
          a (M + 3) ≤ a (M + 1) + a (M + 2)) :
    ∃ t : ℕ,
      pairSeedMargin a M ≤ t ∧ t ≤ a (M + 2) - 1 ∧
        t ∉ prefixSubsetSums a I M :=
  exists_prefix_hole_of_lt_leastPrefixCoverThreshold
    (pairSeedMargin_lt_least_of_not_seed_margin hpair hnot)

/-- Sum of the non-deleted terms up to index `n`. -/
def keptPrefixSum (a : ℕ → ℕ) (D : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i ∉ D), a i

/-- Sum of all terms up to index `n`. -/
def fullPrefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a i

/-- The fixed numerical slack needed to convert a full-prefix surplus into the
Brown budget inequality for an initial covered interval `[H, T]` at index `M`. -/
def budgetBase (a : ℕ → ℕ) (H M T : ℕ) : ℕ :=
  fullPrefixSum a M + H - (T + 1)

/-- A simple finite upper bound sufficient for all before-budget inequalities
between `M` and the first deleted index `start`.  This is deliberately coarse:
it packages the finite obstruction into one number. -/
def beforeBudgetNeed (a : ℕ → ℕ) (H start : ℕ) : ℕ :=
  (Finset.range start).sup (fun n => H + a (n + 1))

/-- Sum of the deleted terms up to index `n`. -/
def deletedPrefixSum (a : ℕ → ℕ) (D : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i ∈ D), a i

/-- Sum of the first `k` deleted terms in an indexed deletion sequence. -/
def indexedDeletedSum (a b : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, a (b j)

lemma indexedDeletedSum_zero {a b : ℕ → ℕ} :
    indexedDeletedSum a b 0 = 0 := by
  simp [indexedDeletedSum]

lemma indexedDeletedSum_succ {a b : ℕ → ℕ} {k : ℕ} :
    indexedDeletedSum a b (k + 1) = indexedDeletedSum a b k + a (b k) := by
  simp [indexedDeletedSum, Finset.sum_range_succ]

/-- State for the recursive sparse-deletion construction.  The first component
is the current deleted index, and the second component is the sum of all
deleted terms chosen so far. -/
def recursiveBudgetState
    (a : ℕ → ℕ) (threshold : ℕ → ℕ) (C start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, a start)
  | k + 1 =>
      let st := recursiveBudgetState a threshold C start k
      let next := max (st.1 + 2) (threshold (C + st.2))
      (next, st.2 + a next)

/-- The indexed deletion sequence associated to `recursiveBudgetState`. -/
def recursiveBudgetSeq
    (a : ℕ → ℕ) (threshold : ℕ → ℕ) (C start : ℕ) (k : ℕ) : ℕ :=
  (recursiveBudgetState a threshold C start k).1

lemma recursiveBudgetSeq_zero
    {a : ℕ → ℕ} {threshold : ℕ → ℕ} {C start : ℕ} :
    recursiveBudgetSeq a threshold C start 0 = start := by
  simp [recursiveBudgetSeq, recursiveBudgetState]

lemma recursiveBudgetState_sum
    {a : ℕ → ℕ} {threshold : ℕ → ℕ} {C start : ℕ} :
    ∀ k : ℕ,
      (recursiveBudgetState a threshold C start k).2 =
        indexedDeletedSum a (recursiveBudgetSeq a threshold C start) (k + 1)
  | 0 => by
      simp [recursiveBudgetSeq, recursiveBudgetState, indexedDeletedSum]
  | k + 1 => by
      have ih := recursiveBudgetState_sum (a := a) (threshold := threshold)
        (C := C) (start := start) k
      simp [recursiveBudgetSeq, recursiveBudgetState, indexedDeletedSum_succ, ih]

lemma recursiveBudgetSeq_succ
    {a : ℕ → ℕ} {threshold : ℕ → ℕ} {C start k : ℕ} :
    recursiveBudgetSeq a threshold C start (k + 1) =
      max (recursiveBudgetSeq a threshold C start k + 2)
        (threshold
          (C + indexedDeletedSum a (recursiveBudgetSeq a threshold C start) (k + 1))) := by
  simp [recursiveBudgetSeq, recursiveBudgetState, recursiveBudgetState_sum]

lemma recursiveBudgetSeq_gap
    {a : ℕ → ℕ} {threshold : ℕ → ℕ} {C start : ℕ} :
    ∀ k : ℕ,
      recursiveBudgetSeq a threshold C start k + 1 <
        recursiveBudgetSeq a threshold C start (k + 1) := by
  intro k
  rw [recursiveBudgetSeq_succ]
  exact lt_of_lt_of_le (by omega)
    (le_max_left _ _)

lemma recursiveBudgetSeq_threshold_le_succ
    {a : ℕ → ℕ} {threshold : ℕ → ℕ} {C start k : ℕ} :
    threshold
        (C + indexedDeletedSum a (recursiveBudgetSeq a threshold C start) (k + 1)) ≤
      recursiveBudgetSeq a threshold C start (k + 1) := by
  rw [recursiveBudgetSeq_succ]
  exact le_max_right _ _

/-- Deletion set obtained from an indexed family of finite blocks `[b k, e k]`. -/
def blockDeletionSet (b e : ℕ → ℕ) : Set ℕ :=
  {n | ∃ k : ℕ, b k ≤ n ∧ n ≤ e k}

/-- Deletion set obtained by combining a finite initial deletion set with an
indexed sparse tail. -/
def initialTailDeletionSet (F : Set ℕ) (b : ℕ → ℕ) : Set ℕ :=
  F ∪ Set.range b

/-- Arithmetic-progression deletion indices.  In the global-budget route these
are used to delete one term every fixed block. -/
def periodicDeletionSeq (start period : ℕ) (k : ℕ) : ℕ :=
  start + k * period

/-- The set of indices deleted by the periodic deletion scheme with the given
`start` and `period`, i.e. the range of `periodicDeletionSeq start period`. -/
def periodicDeletionSet (start period : ℕ) : Set ℕ :=
  Set.range (periodicDeletionSeq start period)

/-- Sum of the `m` terms immediately preceding index `n`.
For `m ≤ n`, this is `a (n-m) + ... + a (n-1)`. -/
def previousBlockSum (a : ℕ → ℕ) (m n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc (n - m) (n - 1), a i

/-- From index `N` on, every term `a (n + 1)` is strictly dominated by the sum of
the previous `m` terms (`previousBlockSum a m n`). This is the fixed-length block
surplus property used to force completeness. -/
def FixedLengthBlockSurplusFrom (a : ℕ → ℕ) (m N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → m ≤ n → a (n + 1) < previousBlockSum a m n

lemma FixedLengthBlockSurplusFrom.mono
    {a : ℕ → ℕ} {m N N' : ℕ}
    (hsurplus : FixedLengthBlockSurplusFrom a m N)
    (hNN' : N ≤ N') :
    FixedLengthBlockSurplusFrom a m N' := by
  intro n hn hm
  exact hsurplus n (le_trans hNN' hn) hm

/-- The geometric block-surplus condition at ratio `ρ` and block length `m`:
for every `n ≥ m`, the inverse geometric weights of the previous `m` terms sum to
more than one. This drives the surplus needed for the golden-ratio bound. -/
def GeometricBlockSurplus (ρ : ℝ) (m : ℕ) : Prop :=
  ∀ n : ℕ, m ≤ n →
    1 < ∑ i ∈ Finset.Icc (n - m) (n - 1), (ρ ^ (n + 1 - i))⁻¹

lemma periodicDeletionSeq_succ
    {start period k : ℕ} :
    periodicDeletionSeq start period (k + 1) =
      periodicDeletionSeq start period k + period := by
  simp [periodicDeletionSeq, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm]

lemma periodicDeletionSeq_gap_of_two_le_period
    {start period : ℕ} (hperiod : 2 ≤ period) :
    ∀ k : ℕ,
      periodicDeletionSeq start period k + 1 <
        periodicDeletionSeq start period (k + 1) := by
  intro k
  rw [periodicDeletionSeq_succ]
  omega

lemma strictMono_periodicDeletionSeq_of_pos
    {start period : ℕ} (hperiod : 0 < period) :
    StrictMono (periodicDeletionSeq start period) := by
  intro i j hij
  dsimp [periodicDeletionSeq]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hperiod) start

lemma periodicDeletionSet_infinite
    {start period : ℕ} (hperiod : 0 < period) :
    (periodicDeletionSet start period).Infinite := by
  dsimp [periodicDeletionSet]
  exact Set.infinite_range_of_injective
    (strictMono_periodicDeletionSeq_of_pos (start := start) hperiod).injective

lemma periodicDeletionSet_coinfinite_of_two_le_period
    {start period : ℕ} (hperiod : 2 ≤ period) :
    (periodicDeletionSet start period)ᶜ.Infinite := by
  let gapPoints : ℕ → ℕ := fun k => periodicDeletionSeq start period k + 1
  have hperiod_pos : 0 < period := by omega
  have hmono : StrictMono (periodicDeletionSeq start period) :=
    strictMono_periodicDeletionSeq_of_pos (start := start) hperiod_pos
  have hgap :
      ∀ k : ℕ,
        periodicDeletionSeq start period k + 1 <
          periodicDeletionSeq start period (k + 1) :=
    periodicDeletionSeq_gap_of_two_le_period (start := start) hperiod
  have hgapMono : StrictMono gapPoints := by
    intro i j hij
    dsimp [gapPoints]
    exact Nat.succ_lt_succ (hmono hij)
  have hinf : (Set.range gapPoints).Infinite :=
    Set.infinite_range_of_injective hgapMono.injective
  refine hinf.mono ?_
  intro x hx
  rcases hx with ⟨k, rfl⟩
  intro hmem
  rcases hmem with ⟨j, hj⟩
  dsimp [gapPoints] at hj
  by_cases hjk : j ≤ k
  · have hle : periodicDeletionSeq start period j ≤
        periodicDeletionSeq start period k := hmono.monotone hjk
    omega
  · have hkj : k < j := Nat.lt_of_not_ge hjk
    have hsucc_le : periodicDeletionSeq start period (k + 1) ≤
        periodicDeletionSeq start period j :=
      hmono.monotone (Nat.succ_le_of_lt hkj)
    have hgapk := hgap k
    omega

lemma periodicDeletionSet_avoids_initial
    {M start period : ℕ} (hMstart : M < start) :
    Set.Iic M ⊆ (periodicDeletionSet start period)ᶜ := by
  intro i hi hmem
  change i ≤ M at hi
  rcases hmem with ⟨k, hk⟩
  have hstart_le : start ≤ periodicDeletionSeq start period k := by
    dsimp [periodicDeletionSeq]
    omega
  have hMi : M < i := by
    have hMi_seq : M < periodicDeletionSeq start period k :=
      lt_of_lt_of_le hMstart hstart_le
    simpa [hk] using hMi_seq
  omega

lemma periodicDeletionSeq_add_period_le_of_lt
    {start period j k : ℕ} (hperiod : 0 < period) (hjk : j < k) :
    periodicDeletionSeq start period j + period ≤
      periodicDeletionSeq start period k := by
  have hmono : StrictMono (periodicDeletionSeq start period) :=
    strictMono_periodicDeletionSeq_of_pos (start := start) hperiod
  have hsucc_le : j + 1 ≤ k := Nat.succ_le_of_lt hjk
  rw [← periodicDeletionSeq_succ (start := start) (period := period) (k := j)]
  exact hmono.monotone hsucc_le

lemma periodicDeletionSet_not_mem_of_current_window
    {start period k i : ℕ} (hperiod : 0 < period)
    (hleft : periodicDeletionSeq start period k < i + period)
    (hright : i < periodicDeletionSeq start period k) :
    i ∉ periodicDeletionSet start period := by
  intro hmem
  rcases hmem with ⟨j, hj⟩
  have hmono : StrictMono (periodicDeletionSeq start period) :=
    strictMono_periodicDeletionSeq_of_pos (start := start) hperiod
  by_cases hjk : j < k
  · have hle :
        periodicDeletionSeq start period j + period ≤
          periodicDeletionSeq start period k :=
      periodicDeletionSeq_add_period_le_of_lt
        (start := start) (period := period) hperiod hjk
    omega
  · have hkj : k ≤ j := Nat.le_of_not_gt hjk
    have hle :
        periodicDeletionSeq start period k ≤
          periodicDeletionSeq start period j :=
      hmono.monotone hkj
    omega

lemma periodicDeletionSet_not_mem_previousBlock_of_period_m_add_two
    {start m k i : ℕ}
    (hmpos : 0 < m)
    (hmd : m ≤ periodicDeletionSeq start (m + 2) k)
    (hlo : periodicDeletionSeq start (m + 2) k - m ≤ i)
    (hhi : i ≤ periodicDeletionSeq start (m + 2) k - 1) :
    i ∉ periodicDeletionSet start (m + 2) := by
  have hperiod : 0 < m + 2 := by omega
  exact periodicDeletionSet_not_mem_of_current_window
    (start := start) (period := m + 2) (k := k) (i := i)
    hperiod (by omega) (by omega)

lemma periodicDeletionSet_not_mem_previousBlock_of_mem_period_m_add_two
    {start m d i : ℕ}
    (hmpos : 0 < m)
    (hmem : d ∈ periodicDeletionSet start (m + 2))
    (hmd : m ≤ d)
    (hlo : d - m ≤ i)
    (hhi : i ≤ d - 1) :
    i ∉ periodicDeletionSet start (m + 2) := by
  rcases hmem with ⟨k, rfl⟩
  exact periodicDeletionSet_not_mem_previousBlock_of_period_m_add_two
    (start := start) (m := m) (k := k) (i := i)
    hmpos hmd hlo hhi

lemma periodicDeletionSet_start_le_of_mem
    {start period d : ℕ}
    (hmem : d ∈ periodicDeletionSet start period) :
    start ≤ d := by
  rcases hmem with ⟨k, rfl⟩
  dsimp [periodicDeletionSeq]
  omega

lemma periodicDeletionSet_mem_period_m_add_two_bounds
    {M m d : ℕ}
    (hmem : d ∈ periodicDeletionSet (M + m + 1) (m + 2)) :
    M < d - m ∧ m ≤ d ∧ M + m + 1 ≤ d := by
  rcases hmem with ⟨k, rfl⟩
  dsimp [periodicDeletionSeq]
  omega

/-- The quotient `a (n+1) / a n`, viewed in `ℝ`. -/
def quotient (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a (n + 1) : ℝ) / (a n : ℝ)

/-- The original lacunarity lower bound, expressed for index sequences. -/
def HasUniformRatioGap (a : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 + ε ≤ quotient a n

/-- Deleting any finite set of indices leaves a complete subsequence. -/
def FiniteDeletionComplete (a : ℕ → ℕ) : Prop :=
  ∀ D : Set ℕ, D.Finite → IsCompleteOn a Dᶜ

/-- Uniform finite-base singleton completeness.  This is the remaining uniformity
needed by the finite-initial-tail lower-bound route: after deleting one fixed
finite base set `F`, deleting any sufficiently late single extra index still
leaves a complete subsequence with one common threshold. -/
def UniformFinSingletonComplete (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∃ H : ℕ, ∀ᶠ M in atTop,
      ∀ t : ℕ, H ≤ t →
        t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ

/-- The weaker uniform condition actually needed by the `start = M + 2`
finite-initial-tail seed route.  Instead of asking for full completeness after
deleting `F ∪ {M + 1}`, it asks only for the finite prefix cover window used by
the seed constructor. -/
def UniformFinSingletonPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∃ H : ℕ, ∀ᶠ M in atTop,
      F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H (a (M + 2) - 1)

/-- A still weaker seed-window condition: the threshold may depend on `M`, but
for eventually all `M` there is a prefix-cover threshold small enough for the
two finite numeric inequalities used by the `start = M + 2` seed constructor. -/
def EventualFinSingletonSmallPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ᶠ M in atTop, ∃ H : ℕ,
      F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H (a (M + 2) - 1) ∧
        H + a (M + 1) ≤ a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2)

/-- The seed construction only needs one sufficiently late good singleton
window, not a good window at every sufficiently late index.  This formulation
asks for good finite-singleton windows arbitrarily far out. -/
def ArbitrarilyLargeFinSingletonSmallPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ H : ℕ,
      F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H (a (M + 2) - 1) ∧
        H + a (M + 1) ≤ a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2)

/-- The same small-window target phrased using the least possible prefix-cover
threshold.  This turns the remaining finite-deletion problem into bounding one
explicit finite combinatorial quantity. -/
def EventualFinSingletonLeastSmallPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ᶠ M in atTop,
      F ⊆ Set.Iic M ∧
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 1) ≤
          a (M + 2) ∧
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 3) ≤
          a (M + 1) + a (M + 2)

/-- Least-threshold form of
`ArbitrarilyLargeFinSingletonSmallPrefixCover`. -/
def ArbitrarilyLargeFinSingletonLeastSmallPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      F ⊆ Set.Iic M ∧
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 1) ≤
          a (M + 2) ∧
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 3) ≤
          a (M + 1) + a (M + 2)

/-- The weakest current finite-window target for the lower-bound route.  It
only asks, arbitrarily far out, for the first finite seed inequality.  Under the
eventual upper ratio bound `quotient a n < ρ < φ`, finite-deletion completeness
upgrades this to the full least-small target below. -/
def ArbitrarilyLargeFinSingletonFirstSmallPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      F ⊆ Set.Iic M ∧
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 1) ≤
          a (M + 2)

/-- Equivalent cover form of the current first-seed target.  Instead of
speaking about the canonical least threshold, it asks directly that the finite
prefix through `M` cover the whole first seed window
`[nextSeedMargin a M, a (M + 2) - 1]`. -/
def ArbitrarilyLargeFinSingletonFirstPrefixCover (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)

/-- Local closure condition that rules out the first-window shift gap.  Every
prefix sum below the first seed margin remains a prefix sum after adding
`a (M + 1)`, even though index `M + 1` itself is not allowed in the prefix
through `M`. -/
def FirstWindowShiftClosed (a : ℕ → ℕ) (F : Set ℕ) (M : ℕ) : Prop :=
  ∀ s : ℕ, s ∈ prefixSubsetSums a Fᶜ M → s < nextSeedMargin a M →
    a (M + 1) + s ∈ prefixSubsetSums a Fᶜ M

/-- Arbitrarily late occurrences of the local first-window shift closure for
one fixed finite base set. -/
def ArbitrarilyLargeFinSingletonFirstWindowShiftClosed (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
      FirstWindowShiftClosed a F M

/-- The moving singleton-deletion threshold condition sufficient for
`FirstWindowShiftClosed`: after deleting `F ∪ {M + 1}`, completeness has already
started by the previous term `a (M + 1)`. -/
def FinSingletonCompleteBelowPrev (a : ℕ → ℕ) (F : Set ℕ) (M : ℕ) : Prop :=
  ∃ H : ℕ, H ≤ a (M + 1) ∧
    ∀ t : ℕ, H ≤ t →
      t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ

/-- Arbitrarily late occurrences of the moving singleton-deletion threshold
condition for one fixed finite base set. -/
def ArbitrarilyLargeFinSingletonCompleteBelowPrev (a : ℕ → ℕ) : Prop :=
  ∃ F : Set ℕ, F.Finite ∧
    ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
      FinSingletonCompleteBelowPrev a F M

/-- Deleting any infinite set of indices leaves an incomplete subsequence. -/
def InfiniteDeletionIncomplete (a : ℕ → ℕ) : Prop :=
  ∀ D : Set ℕ, D.Infinite → ¬ IsCompleteOn a Dᶜ

/-- Completeness after deleting a set of values rather than a set of indices.
The remaining terms are those indices `i` whose value `a i` is not in `B`. -/
def IsCompleteAfterDeletingValues (a : ℕ → ℕ) (B : Set ℕ) : Prop :=
  IsCompleteOn a {i : ℕ | a i ∉ B}

/-- Deleting any finite set of values leaves a complete subsequence. -/
def ValueFiniteDeletionComplete (a : ℕ → ℕ) : Prop :=
  ∀ B : Set ℕ, B.Finite → IsCompleteAfterDeletingValues a B

/-- Deleting any infinite subset of the sequence values leaves an incomplete
subsequence.  The side condition `B ⊆ Set.range a` says that `B` really consists
of values from the sequence. -/
def ValueInfiniteDeletionIncomplete (a : ℕ → ℕ) : Prop :=
  ∀ B : Set ℕ, B.Infinite → B ⊆ Set.range a →
    ¬ IsCompleteAfterDeletingValues a B

lemma index_compl_eq_value_kept_image {a : ℕ → ℕ}
    (hmono : StrictMono a) (D : Set ℕ) :
    Dᶜ = {i : ℕ | a i ∉ a '' D} := by
  ext i
  constructor
  · intro hi hmem
    rcases hmem with ⟨j, hj, haj⟩
    have hji : j = i := hmono.injective haj
    exact hi (hji ▸ hj)
  · intro hi hD
    exact hi ⟨i, hD, rfl⟩

lemma finiteDeletionComplete_of_valueFiniteDeletionComplete {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hvalue : ValueFiniteDeletionComplete a) :
    FiniteDeletionComplete a := by
  intro D hD
  have hBfinite : (a '' D).Finite := hD.image a
  have hcomplete := hvalue (a '' D) hBfinite
  rw [index_compl_eq_value_kept_image hmono D]
  simpa [IsCompleteAfterDeletingValues] using hcomplete

lemma valueFiniteDeletionComplete_of_finiteDeletionComplete {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hindex : FiniteDeletionComplete a) :
    ValueFiniteDeletionComplete a := by
  intro B hB
  let D : Set ℕ := a ⁻¹' B
  have hD : D.Finite := by
    simpa [D] using hB.preimage hmono.injective.injOn
  have hkept : Dᶜ = {i : ℕ | a i ∉ B} := by
    ext i
    simp [D]
  have hcomplete := hindex D hD
  rw [hkept] at hcomplete
  simpa [IsCompleteAfterDeletingValues] using hcomplete

lemma finiteDeletionComplete_iff_valueFiniteDeletionComplete {a : ℕ → ℕ}
    (hmono : StrictMono a) :
    FiniteDeletionComplete a ↔ ValueFiniteDeletionComplete a :=
  ⟨valueFiniteDeletionComplete_of_finiteDeletionComplete hmono,
    finiteDeletionComplete_of_valueFiniteDeletionComplete hmono⟩

lemma infiniteDeletionIncomplete_of_valueInfiniteDeletionIncomplete {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hvalue : ValueInfiniteDeletionIncomplete a) :
    InfiniteDeletionIncomplete a := by
  intro D hD
  have hBinf : (a '' D).Infinite :=
    Set.Infinite.image hmono.injective.injOn hD
  have hBrange : a '' D ⊆ Set.range a := by
    rintro x ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  exact fun hcomplete =>
    (hvalue (a '' D) hBinf hBrange) (by
      rw [IsCompleteAfterDeletingValues]
      rw [← index_compl_eq_value_kept_image hmono D]
      exact hcomplete)

lemma valueInfiniteDeletionIncomplete_of_infiniteDeletionIncomplete {a : ℕ → ℕ}
    (hindex : InfiniteDeletionIncomplete a) :
    ValueInfiniteDeletionIncomplete a := by
  intro B hB hBrange
  let D : Set ℕ := a ⁻¹' B
  have hD : D.Infinite := by
    simpa [D] using hB.preimage hBrange
  have hkept : Dᶜ = {i : ℕ | a i ∉ B} := by
    ext i
    simp [D]
  have hcomplete := hindex D hD
  rw [hkept] at hcomplete
  simpa [IsCompleteAfterDeletingValues] using hcomplete

lemma infiniteDeletionIncomplete_iff_valueInfiniteDeletionIncomplete {a : ℕ → ℕ}
    (hmono : StrictMono a) :
    InfiniteDeletionIncomplete a ↔ ValueInfiniteDeletionIncomplete a :=
  ⟨valueInfiniteDeletionIncomplete_of_infiniteDeletionIncomplete,
    infiniteDeletionIncomplete_of_valueInfiniteDeletionIncomplete hmono⟩

lemma term_ge_succ_of_strictMono_pos {a : ℕ → ℕ}
    (hmono : StrictMono a) (hpos : ∀ n : ℕ, 0 < a n) :
    ∀ n : ℕ, n + 1 ≤ a n := by
  intro n
  induction n with
  | zero =>
      exact hpos 0
  | succ n ih =>
      have hlt : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
      omega

lemma evt_const_add_self_le_next_of_uniformRatioGap {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a) :
    ∀ C : ℕ, ∀ᶠ n in atTop, C + a n ≤ a (n + 1) := by
  rcases hgap with ⟨ε, hεpos, hε⟩
  intro C
  obtain ⟨N, hN⟩ := exists_nat_gt ((C : ℝ) / ε)
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hN_le_an : N ≤ a n := by
    have hn_le_an : n ≤ a n := by
      have hterm := term_ge_succ_of_strictMono_pos hmono hpos n
      omega
    exact le_trans hn hn_le_an
  have hC_le : (C : ℝ) ≤ ε * (a n : ℝ) := by
    have hC_lt_Nε : (C : ℝ) < (N : ℝ) * ε :=
      (div_lt_iff₀ hεpos).mp hN
    have hN_le_an_real : (N : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hN_le_an
    have hmul_le : (N : ℝ) * ε ≤ (a n : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hN_le_an_real hεpos.le
    nlinarith
  have hanpos : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hnext_ratio : (1 + ε) * (a n : ℝ) ≤ a (n + 1) := by
    have hmul := (le_div_iff₀ hanpos).mp (hε n)
    simpa [quotient, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hreal : (C : ℝ) + a n ≤ a (n + 1) := by
    nlinarith
  exact_mod_cast hreal

lemma evt_const_add_next_le_next_next_of_uniformRatioGap {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a) :
    ∀ C : ℕ, ∀ᶠ M in atTop, C + a (M + 1) ≤ a (M + 2) := by
  intro C
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (evt_const_add_self_le_next_of_uniformRatioGap hmono hpos hgap C)
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro M hM
  exact hN (M + 1) (le_trans hM (Nat.le_succ M))

lemma complete_univ_of_finiteDeletionComplete {a : ℕ → ℕ}
    (hfinite : FiniteDeletionComplete a) :
    IsCompleteOn a Set.univ := by
  have h := hfinite (∅ : Set ℕ) Set.finite_empty
  simpa using h

lemma tail_complete_of_finiteDeletionComplete {a : ℕ → ℕ}
    (hfinite : FiniteDeletionComplete a) (N : ℕ) :
    IsCompleteOn a (Set.Ici N) := by
  have h := hfinite (Set.Iio N) (Set.finite_Iio N)
  simpa [Set.compl_Iio] using h

lemma finite_singleton_complete_of_finiteDeletionComplete
    {a : ℕ → ℕ} {F : Set ℕ} (hfinite : FiniteDeletionComplete a)
    (hF : F.Finite) (M : ℕ) :
    IsCompleteOn a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  exact hfinite (F ∪ ({M + 1} : Set ℕ))
    (hF.union (Set.finite_singleton (M + 1)))

/-- The canonical completeness threshold obtained from finite deletion after
deleting a fixed finite base set `F` and the moving singleton `M + 1`. -/
def finSingletonCompleteThreshold
    (a : ℕ → ℕ) (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) (M : ℕ) : ℕ :=
  leastCompleteThreshold a (F ∪ ({M + 1} : Set ℕ))ᶜ
    (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M)

lemma finSingletonCompleteThreshold_spec
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M t : ℕ}
    (ht : finSingletonCompleteThreshold a hfinite hF M ≤ t) :
    t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ :=
  leastCompleteThreshold_spec
    (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M) t ht

lemma finSingletonCompleteThreshold_le_of_complete_from
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M H : ℕ}
    (hH : ∀ t : ℕ, H ≤ t →
      t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    finSingletonCompleteThreshold a hfinite hF M ≤ H :=
  leastCompleteThreshold_le_of_complete_from
    (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M) hH

lemma finSingletonCompleteBelowPrev_iff_threshold_le
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ} :
    FinSingletonCompleteBelowPrev a F M ↔
      finSingletonCompleteThreshold a hfinite hF M ≤ a (M + 1) := by
  constructor
  · rintro ⟨H, hHprev, hcompleteH⟩
    have hleH :
        finSingletonCompleteThreshold a hfinite hF M ≤ H :=
      finSingletonCompleteThreshold_le_of_complete_from
        hfinite hF hcompleteH
    omega
  · intro hle
    exact ⟨finSingletonCompleteThreshold a hfinite hF M, hle,
      fun t ht =>
        finSingletonCompleteThreshold_spec hfinite hF ht⟩

lemma not_finSingletonCompleteBelowPrev_iff_prev_lt_threshold
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ} :
    ¬ FinSingletonCompleteBelowPrev a F M ↔
      a (M + 1) < finSingletonCompleteThreshold a hfinite hF M := by
  constructor
  · intro hnot
    exact Nat.lt_of_not_ge
      (fun hle =>
        hnot ((finSingletonCompleteBelowPrev_iff_threshold_le
          hfinite hF).mpr hle))
  · intro hlt hbelow
    have hle :
        finSingletonCompleteThreshold a hfinite hF M ≤ a (M + 1) :=
      (finSingletonCompleteBelowPrev_iff_threshold_le hfinite hF).mp hbelow
    omega

lemma exists_finSingletonCompleteThreshold_hole_of_prev_lt
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ}
    (hlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M) :
    ∃ t : ℕ, a (M + 1) ≤ t ∧
      t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ :=
  exists_hole_of_lt_leastCompleteThreshold
    (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M) hlt

lemma pred_finSingletonCompleteThreshold_hole_of_prev_lt
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ}
    (hlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M) :
    finSingletonCompleteThreshold a hfinite hF M - 1 ∉
      subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  have hpos :
      0 <
        leastCompleteThreshold a (F ∪ ({M + 1} : Set ℕ))ᶜ
          (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M) := by
    change 0 < finSingletonCompleteThreshold a hfinite hF M
    have hnonneg : 0 ≤ a (M + 1) := Nat.zero_le _
    omega
  exact
    pred_leastCompleteThreshold_not_mem
      (finite_singleton_complete_of_finiteDeletionComplete hfinite hF M) hpos

lemma pred_finSingletonCompleteThreshold_ge_prev_of_prev_lt
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ}
    (hlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M) :
    a (M + 1) ≤ finSingletonCompleteThreshold a hfinite hF M - 1 := by
  omega

lemma exists_pred_finSingletonCompleteThreshold_hole_of_prev_lt
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {M : ℕ}
    (hlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M) :
    ∃ t : ℕ,
      t = finSingletonCompleteThreshold a hfinite hF M - 1 ∧
        a (M + 1) ≤ t ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ :=
  ⟨finSingletonCompleteThreshold a hfinite hF M - 1, rfl,
    pred_finSingletonCompleteThreshold_ge_prev_of_prev_lt hfinite hF hlt,
    pred_finSingletonCompleteThreshold_hole_of_prev_lt hfinite hF hlt⟩

theorem arbLargeFinSingletonCompleteBelowPrev_iff_threshold_le
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a) :
    ArbitrarilyLargeFinSingletonCompleteBelowPrev a ↔
      ∃ F : Set ℕ, ∃ hF : F.Finite,
        ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
          finSingletonCompleteThreshold a hfinite hF M ≤ a (M + 1) := by
  constructor
  · rintro ⟨F, hFfinite, hlarge⟩
    refine ⟨F, hFfinite, ?_⟩
    intro N
    obtain ⟨M, hNM, hFM, hbelowM⟩ := hlarge N
    exact ⟨M, hNM, hFM,
      (finSingletonCompleteBelowPrev_iff_threshold_le
        hfinite hFfinite).mp hbelowM⟩
  · rintro ⟨F, hFfinite, hlarge⟩
    refine ⟨F, hFfinite, ?_⟩
    intro N
    obtain ⟨M, hNM, hFM, hleM⟩ := hlarge N
    exact ⟨M, hNM, hFM,
      (finSingletonCompleteBelowPrev_iff_threshold_le
        hfinite hFfinite).mpr hleM⟩

lemma uniformFinSingletonComplete_of_eventual_singleton_complete
    {a : ℕ → ℕ}
    (hsingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) :
    UniformFinSingletonComplete a := by
  rcases hsingleton with ⟨H, hH⟩
  refine ⟨∅, Set.finite_empty, H, ?_⟩
  filter_upwards [hH] with M hM t ht
  simpa using hM t ht

lemma one_add_lt_mul_of_goldenRatio_lt {x y : ℝ}
    (hx : Real.goldenRatio < x) (hy : Real.goldenRatio < y) :
    1 + x < x * y := by
  have hφsub : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hxpos : 0 < x := lt_trans Real.goldenRatio_pos hx
  have hdiff :
      1 < x * Real.goldenRatio - x := by
    have hmul :
        Real.goldenRatio * (Real.goldenRatio - 1) <
          x * (Real.goldenRatio - 1) :=
      mul_lt_mul_of_pos_right hx hφsub
    have hφmul : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
      nlinarith [Real.goldenRatio_sq]
    have hxmul : x * (Real.goldenRatio - 1) = x * Real.goldenRatio - x := by
      ring
    simpa [hφmul, hxmul] using hmul
  have hxy : x * Real.goldenRatio < x * y :=
    mul_lt_mul_of_pos_left hy hxpos
  linarith

lemma two_step_gap_of_quotient_gt_goldenRatio {a : ℕ → ℕ} {n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hn : Real.goldenRatio < quotient a n)
    (hn1 : Real.goldenRatio < quotient a (n + 1)) :
    a n + a (n + 1) < a (n + 2) := by
  have hApos : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hBpos : 0 < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hquot :
      1 + quotient a n < quotient a n * quotient a (n + 1) :=
    one_add_lt_mul_of_goldenRatio_lt hn hn1
  have hmul := mul_lt_mul_of_pos_right hquot hApos
  have hreal : (a n : ℝ) + a (n + 1) < a (n + 2) := by
    have hAne : (a n : ℝ) ≠ 0 := ne_of_gt hApos
    have hBne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt hBpos
    have hmul' :
        (a n : ℝ) * (1 + (a (n + 1) : ℝ) / (a n : ℝ)) <
          (a n : ℝ) * ((a (n + 2) : ℝ) / (a n : ℝ)) := by
      simpa [quotient, hAne, hBne, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm]
        using hmul
    have hleft :
        (a n : ℝ) * (1 + (a (n + 1) : ℝ) / (a n : ℝ)) =
          (a n : ℝ) + a (n + 1) := by
      field_simp [hAne]
    have hright :
        (a n : ℝ) * ((a (n + 2) : ℝ) / (a n : ℝ)) =
          a (n + 2) := by
      field_simp [hAne]
    simpa [hleft, hright]
      using hmul'
  exact_mod_cast hreal

lemma goldenRatio_lt_two : Real.goldenRatio < 2 := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

lemma rho_mul_sub_one_lt_one {ρ : ℝ}
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio) :
    ρ * (ρ - 1) < 1 := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

lemma exists_range_geometricBlockWeightSum_gt_one {ρ : ℝ}
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio) :
    ∃ m : ℕ, 0 < m ∧
      1 < ∑ j ∈ Finset.range m, (ρ ^ (j + 2))⁻¹ := by
  let r : ℝ := ρ⁻¹
  have hρpos : 0 < ρ := lt_trans Real.zero_lt_one hρ1
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρsub_ne : ρ - 1 ≠ 0 := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact inv_nonneg.mpr hρpos.le
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ hρ1
  have hterm :
      (fun j : ℕ => r ^ 2 * r ^ j) =
        fun j : ℕ => (ρ ^ (j + 2))⁻¹ := by
    funext j
    calc
      r ^ 2 * r ^ j = r ^ (2 + j) := by
        rw [← pow_add]
      _ = r ^ (j + 2) := by
        congr 1
        omega
      _ = (ρ ^ (j + 2))⁻¹ := by
        simp [r, inv_pow]
  have hsum :
      r ^ 2 * (1 - r)⁻¹ = (ρ * (ρ - 1))⁻¹ := by
    dsimp [r]
    field_simp [hρne, hρsub_ne]
  have hhas :
      HasSum (fun j : ℕ => (ρ ^ (j + 2))⁻¹)
        ((ρ * (ρ - 1))⁻¹) := by
    rw [← hterm, ← hsum]
    exact (hasSum_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left (r ^ 2)
  have hprodpos : 0 < ρ * (ρ - 1) :=
    mul_pos hρpos (sub_pos.mpr hρ1)
  have hsum_gt_one : 1 < (ρ * (ρ - 1))⁻¹ :=
    (one_lt_inv₀ hprodpos).2 (rho_mul_sub_one_lt_one hρ1 hρφ)
  have hlim :
      Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (ρ ^ (j + 2))⁻¹)
        atTop (𝓝 ((ρ * (ρ - 1))⁻¹)) :=
    hhas.tendsto_sum_nat
  have hev :
      ∀ᶠ m in atTop, 1 < ∑ j ∈ Finset.range m, (ρ ^ (j + 2))⁻¹ :=
    hlim.eventually (isOpen_Ioi.mem_nhds hsum_gt_one)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨max 1 M, by omega, ?_⟩
  exact hM (max 1 M) (le_max_right 1 M)

lemma geometricBlockSurplus_of_range_geometricBlockWeightSum_gt_one
    {ρ : ℝ} {m : ℕ}
    (hmpos : 0 < m)
    (hrange : 1 < ∑ j ∈ Finset.range m, (ρ ^ (j + 2))⁻¹) :
    GeometricBlockSurplus ρ m := by
  intro n hmn
  have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
  have hpredsucc : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
  have hIccIco :
      Finset.Icc (n - m) (n - 1) = Finset.Ico (n - m) n := by
    rw [← Finset.Ico_add_one_right_eq_Icc (n - m) (n - 1), hpredsucc]
  have hreflect :
      (∑ i ∈ Finset.Ico (n - m) n, (ρ ^ (n + 1 - i))⁻¹) =
        ∑ j ∈ Finset.Ico 2 (m + 2), (ρ ^ j)⁻¹ := by
    have h :=
      Finset.sum_Ico_reflect (fun e : ℕ => (ρ ^ e)⁻¹) (n - m)
        (m := n) (n := n + 1) (by omega)
    have hleft : n + 1 + 1 - n = 2 := by omega
    have hright : n + 1 + 1 - (n - m) = m + 2 := by omega
    simpa [hleft, hright, Nat.add_assoc] using h
  have hshift :
      (∑ j ∈ Finset.range m, (ρ ^ (j + 2))⁻¹) =
        ∑ j ∈ Finset.Ico 2 (m + 2), (ρ ^ j)⁻¹ := by
    have h :=
      Finset.sum_Ico_add (fun e : ℕ => (ρ ^ e)⁻¹) 0 m 2
    simpa [Nat.Ico_zero_eq_range, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using h
  rw [hIccIco, hreflect]
  simpa [hshift] using hrange

lemma exists_geometricBlockSurplus_of_lt_goldenRatio {ρ : ℝ}
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio) :
    ∃ m : ℕ, 0 < m ∧ GeometricBlockSurplus ρ m := by
  obtain ⟨m, hmpos, hrange⟩ :=
    exists_range_geometricBlockWeightSum_gt_one hρ1 hρφ
  exact ⟨m, hmpos,
    geometricBlockSurplus_of_range_geometricBlockWeightSum_gt_one hmpos hrange⟩

lemma two_mul_of_quotient_succ_lt_two {a : ℕ → ℕ} {n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (h : quotient a (n + 1) < (2 : ℝ)) :
    a (n + 2) < 2 * a (n + 1) := by
  have hden : 0 < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hreal : (a (n + 2) : ℝ) < 2 * a (n + 1) := by
    have h' := (div_lt_iff₀ hden).mp h
    simpa [quotient, Nat.add_assoc, mul_comm, mul_left_comm, mul_assoc] using h'
  exact_mod_cast hreal

lemma evt_two_mul_of_eventual_quotient_lt_of_lt_two
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ2 : ρ < 2)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ n in atTop, a (n + 2) < 2 * a (n + 1) := by
  have hsucc : ∀ᶠ n in atTop, quotient a (n + 1) < ρ := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hupper
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    exact hN (n + 1) (le_trans hn (Nat.le_succ n))
  filter_upwards [hsucc] with n hn
  exact two_mul_of_quotient_succ_lt_two hpos (lt_trans hn hρ2)

lemma two_step_sum_gt_of_quotient_lt_rho {a : ℕ → ℕ} {ρ : ℝ} {n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hn : quotient a n < ρ)
    (hn1 : quotient a (n + 1) < ρ) :
    a (n + 2) < a n + a (n + 1) := by
  have hApos : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hBpos : 0 < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hAne : (a n : ℝ) ≠ 0 := ne_of_gt hApos
  have hBne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt hBpos
  have hBA : (a (n + 1) : ℝ) < ρ * a n := by
    have h := (div_lt_iff₀ hApos).mp hn
    simpa [quotient, hAne] using h
  have hCB : (a (n + 2) : ℝ) < ρ * a (n + 1) := by
    have h := (div_lt_iff₀ hBpos).mp hn1
    simpa [quotient, hBne, Nat.add_assoc] using h
  have hrho : ρ * (ρ - 1) < 1 := rho_mul_sub_one_lt_one hρ1 hρφ
  have hdiff : (ρ - 1) * (a (n + 1) : ℝ) < a n := by
    have hmul := mul_lt_mul_of_pos_left hBA (sub_pos.mpr hρ1)
    nlinarith [hrho, hApos]
  have hCdiff : (a (n + 2) : ℝ) - a (n + 1) < a n := by
    nlinarith
  have hreal : (a (n + 2) : ℝ) < a n + a (n + 1) := by
    nlinarith
  exact_mod_cast hreal

lemma evt_two_step_sum_gt_of_eventual_quotient_lt_rho
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ n in atTop, a (n + 2) < a n + a (n + 1) := by
  have hsucc : ∀ᶠ n in atTop, quotient a (n + 1) < ρ := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hupper
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    exact hN (n + 1) (le_trans hn (Nat.le_succ n))
  filter_upwards [hupper, hsucc] with n hn hn1
  exact two_step_sum_gt_of_quotient_lt_rho hpos hρ1 hρφ hn hn1

lemma evt_two_step_le_of_eventual_quotient_lt_rho
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ n in atTop, a (n + 2) ≤ a n + a (n + 1) := by
  filter_upwards
    [evt_two_step_sum_gt_of_eventual_quotient_lt_rho
      hpos hρ1 hρφ hupper] with n hn
  omega

lemma const_add_two_step_le_of_quotient_lt_rho_of_const_le
    {a : ℕ → ℕ} {ρ : ℝ} {C n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ)
    (hC : (C : ℝ) ≤ (1 - ρ * (ρ - 1)) * (a n : ℝ))
    (hn : quotient a n < ρ)
    (hn1 : quotient a (n + 1) < ρ) :
    C + a (n + 2) ≤ a n + a (n + 1) := by
  have hApos : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hBpos : 0 < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hAne : (a n : ℝ) ≠ 0 := ne_of_gt hApos
  have hBne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt hBpos
  have hBA : (a (n + 1) : ℝ) < ρ * a n := by
    have h := (div_lt_iff₀ hApos).mp hn
    simpa [quotient, hAne] using h
  have hCB : (a (n + 2) : ℝ) < ρ * a (n + 1) := by
    have h := (div_lt_iff₀ hBpos).mp hn1
    simpa [quotient, hBne, Nat.add_assoc] using h
  have hdiffB :
      (ρ - 1) * (a (n + 1) : ℝ) <
        ρ * (ρ - 1) * (a n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hBA (sub_pos.mpr hρ1)
    nlinarith
  have hCdiff :
      (a (n + 2) : ℝ) - a (n + 1) <
        (ρ - 1) * (a (n + 1) : ℝ) := by
    nlinarith
  have hmargin :
      (1 - ρ * (ρ - 1)) * (a n : ℝ) <
        (a n : ℝ) + a (n + 1) - a (n + 2) := by
    nlinarith
  have hreal : (C : ℝ) + a (n + 2) < a n + a (n + 1) := by
    nlinarith
  have hnat : C + a (n + 2) < a n + a (n + 1) := by
    exact_mod_cast hreal
  exact hnat.le

lemma evt_const_add_two_step_le_of_eventual_quotient_lt_rho
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ C : ℕ, ∀ᶠ n in atTop, C + a (n + 2) ≤ a n + a (n + 1) := by
  intro C
  let δ : ℝ := 1 - ρ * (ρ - 1)
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [rho_mul_sub_one_lt_one hρ1 hρφ]
  obtain ⟨N, hN⟩ := exists_nat_gt ((C : ℝ) / δ)
  have hlarge : ∀ᶠ n in atTop, (C : ℝ) ≤ δ * (a n : ℝ) := by
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hN_le_an : N ≤ a n := by
      have hn_le_an : n ≤ a n := by
        have hterm := term_ge_succ_of_strictMono_pos hmono hpos n
        omega
      exact le_trans hn hn_le_an
    have hC_lt_Nδ : (C : ℝ) < (N : ℝ) * δ :=
      (div_lt_iff₀ hδpos).mp hN
    have hN_le_an_real : (N : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hN_le_an
    have hmul_le : (N : ℝ) * δ ≤ (a n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hN_le_an_real hδpos.le
    nlinarith
  have hsucc : ∀ᶠ n in atTop, quotient a (n + 1) < ρ := by
    obtain ⟨Nq, hNq⟩ := eventually_atTop.1 hupper
    refine eventually_atTop.2 ⟨Nq, ?_⟩
    intro n hn
    exact hNq (n + 1) (le_trans hn (Nat.le_succ n))
  filter_upwards [hlarge, hupper, hsucc] with n hC hn hn1
  exact const_add_two_step_le_of_quotient_lt_rho_of_const_le
    hpos hρ1 (by simpa [δ] using hC) hn hn1

lemma term_le_pow_mul_of_quotient_lt_on_range
    {a : ℕ → ℕ} {ρ : ℝ} {s k : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρpos : 0 < ρ)
    (hquot : ∀ j : ℕ, j < k → quotient a (s + j) < ρ) :
    (a (s + k) : ℝ) ≤ ρ ^ k * a s := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hq : quotient a (s + k) < ρ := hquot k (Nat.lt_succ_self k)
      have ih' :
          (a (s + k) : ℝ) ≤ ρ ^ k * a s := by
        exact ih (fun j hj => hquot j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hden : 0 < (a (s + k) : ℝ) := by exact_mod_cast hpos (s + k)
      have hstep :
          (a (s + (k + 1)) : ℝ) ≤ ρ * a (s + k) := by
        have hlt : (a (s + k + 1) : ℝ) < ρ * a (s + k) := by
          have h := (div_lt_iff₀ hden).mp hq
          simpa [quotient, Nat.add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
        simpa [Nat.add_assoc] using hlt.le
      calc
        (a (s + (k + 1)) : ℝ) ≤ ρ * a (s + k) := hstep
        _ ≤ ρ * (ρ ^ k * a s) :=
            mul_le_mul_of_nonneg_left ih' hρpos.le
        _ = ρ ^ (k + 1) * a s := by
            ring

lemma term_div_pow_le_of_quotient_lt_between
    {a : ℕ → ℕ} {ρ : ℝ} {i n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρpos : 0 < ρ)
    (hin : i ≤ n + 1)
    (hquot : ∀ t : ℕ, i ≤ t → t < n + 1 → quotient a t < ρ) :
    (a (n + 1) : ℝ) / ρ ^ (n + 1 - i) ≤ a i := by
  let k := n + 1 - i
  have hik : i + k = n + 1 := by
    dsimp [k]
    omega
  have hchain :
      (a (i + k) : ℝ) ≤ ρ ^ k * a i :=
    term_le_pow_mul_of_quotient_lt_on_range
      (a := a) (ρ := ρ) (s := i) (k := k) hpos hρpos
      (fun j hj => by
        have hleft : i ≤ i + j := by omega
        have hright : i + j < n + 1 := by
          dsimp [k] at hj
          omega
        exact hquot (i + j) hleft hright)
  have hpowpos : 0 < ρ ^ k := pow_pos hρpos k
  have htarget :
      (a (n + 1) : ℝ) ≤ ρ ^ k * a i := by
    simpa [hik] using hchain
  have hdiv :
      (a (n + 1) : ℝ) / ρ ^ k ≤ a i := by
    rw [div_le_iff₀ hpowpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htarget
  simpa [k] using hdiv

lemma fixedLengthBlockSurplusFrom_of_geometricBlockSurplus_of_eventual_quotient_lt
    {a : ℕ → ℕ} {ρ : ℝ} {m : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρpos : 0 < ρ)
    (hgeom : GeometricBlockSurplus ρ m)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∃ N : ℕ, FixedLengthBlockSurplusFrom a m N := by
  obtain ⟨Nq, hNq⟩ := eventually_atTop.1 hupper
  refine ⟨Nq + m, ?_⟩
  intro n hnN hmn
  let s := Finset.Icc (n - m) (n - 1)
  have hblock_start : Nq ≤ n - m := by omega
  have hgeomn : 1 < ∑ i ∈ s, (ρ ^ (n + 1 - i))⁻¹ := by
    simpa [s] using hgeom n hmn
  have hterm_le :
      (∑ i ∈ s, (a (n + 1) : ℝ) / ρ ^ (n + 1 - i)) ≤
        ∑ i ∈ s, (a i : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_bounds := Finset.mem_Icc.mp hi
    exact term_div_pow_le_of_quotient_lt_between
      (a := a) (ρ := ρ) (i := i) (n := n)
      hpos hρpos (by omega)
      (fun t hit htn => hNq t (by omega))
  have hsum_div :
      (∑ i ∈ s, (a (n + 1) : ℝ) / ρ ^ (n + 1 - i)) =
        (a (n + 1) : ℝ) * ∑ i ∈ s, (ρ ^ (n + 1 - i))⁻¹ := by
    simp [div_eq_mul_inv, Finset.mul_sum]
  have hxpos : 0 < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hleft_gt :
      (a (n + 1) : ℝ) <
        ∑ i ∈ s, (a (n + 1) : ℝ) / ρ ^ (n + 1 - i) := by
    have hmul :=
      mul_lt_mul_of_pos_left hgeomn hxpos
    rw [hsum_div]
    simpa using hmul
  have hsum_cast :
      ((previousBlockSum a m n : ℕ) : ℝ) =
        ∑ i ∈ s, (a i : ℝ) := by
    simp [previousBlockSum, s]
  have hreal :
      (a (n + 1) : ℝ) < (previousBlockSum a m n : ℝ) := by
    rw [hsum_cast]
    exact lt_of_lt_of_le hleft_gt hterm_le
  exact_mod_cast hreal

/-- A moving hole in a tail.  Starting from `a N - 1`, it is propagated two
steps at a time by adding the intervening odd-indexed tail term. -/
def propagatedGap (a : ℕ → ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => a N - 1
  | k + 1 => propagatedGap a N k + a (N + 2 * k + 1)

lemma finset_sum_le_Icc_sum_of_subset_Ici_of_forall_le
    {a : ℕ → ℕ} {F : Finset ℕ} {N m : ℕ}
    (hFN : ↑F ⊆ Set.Ici N)
    (hm : ∀ i ∈ F, i ≤ m) :
    ∑ i ∈ F, a i ≤ ∑ i ∈ Finset.Icc N m, a i := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨hFN hi, hm i hi⟩
  · intro i hi _
    exact Nat.zero_le (a i)

lemma propagatedGap_ge_self {a : ℕ → ℕ} {N : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n) :
    ∀ k : ℕ, k ≤ propagatedGap a N k := by
  intro k
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      have hstep : 1 ≤ a (N + 2 * k + 1) := hpos _
      simp [propagatedGap]
      omega

lemma prefixSubsetSums_mono_index {a : ℕ → ℕ} {I : Set ℕ} {m n : ℕ}
    (hmn : m ≤ n) :
    prefixSubsetSums a I m ⊆ prefixSubsetSums a I n := by
  intro t ht
  rcases ht with ⟨F, hFI, hsum⟩
  refine ⟨F, ?_, hsum⟩
  intro i hi
  exact ⟨hFI hi |>.1, le_trans (hFI hi |>.2) hmn⟩

lemma prefixSubsetSums_subset {a : ℕ → ℕ} {I : Set ℕ} {n : ℕ} :
    prefixSubsetSums a I n ⊆ subsetSums a I := by
  intro t ht
  rcases ht with ⟨F, hFI, hsum⟩
  exact ⟨F, fun i hi => (hFI hi).1, hsum⟩

lemma prefixSubsetSums_succ_iff
    {a : ℕ → ℕ} {I : Set ℕ} {M t : ℕ} :
    t ∈ prefixSubsetSums a I (M + 1) ↔
      t ∈ prefixSubsetSums a I M ∨
        ((M + 1) ∈ I ∧ a (M + 1) ≤ t ∧
          t - a (M + 1) ∈ prefixSubsetSums a I M) := by
  constructor
  · intro ht
    rcases ht with ⟨G, hG, hsum⟩
    by_cases hmem : M + 1 ∈ G
    · have hI : M + 1 ∈ I := (hG hmem).1
      have hterm_le : a (M + 1) ≤ t := by
        have hsplit := Finset.sum_erase_add (s := G) (f := a) hmem
        omega
      have hEraseSubset : ↑(G.erase (M + 1)) ⊆ I ∩ Set.Iic M := by
        intro i hi
        have hiG : i ∈ G := Finset.mem_of_mem_erase hi
        constructor
        · exact (hG hiG).1
        · have hi_le_succ : i ≤ M + 1 := (hG hiG).2
          have hi_ne : i ≠ M + 1 := (Finset.mem_erase.mp hi).1
          exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hi_le_succ hi_ne)
      have hEraseSum :
          ∑ i ∈ G.erase (M + 1), a i = t - a (M + 1) := by
        have hsplit := Finset.sum_erase_add (s := G) (f := a) hmem
        omega
      exact Or.inr ⟨hI, hterm_le, ⟨G.erase (M + 1), hEraseSubset, hEraseSum⟩⟩
    · have hSubset : ↑G ⊆ I ∩ Set.Iic M := by
        intro i hi
        constructor
        · exact (hG hi).1
        · have hi_le_succ : i ≤ M + 1 := (hG hi).2
          have hi_ne : i ≠ M + 1 := by
            intro hi_eq
            exact hmem (hi_eq ▸ hi)
          exact Nat.lt_succ_iff.mp (lt_of_le_of_ne hi_le_succ hi_ne)
      exact Or.inl ⟨G, hSubset, hsum⟩
  · intro ht
    rcases ht with ht | ht
    · exact prefixSubsetSums_mono_index (Nat.le_succ M) ht
    · rcases ht with ⟨hI, hterm_le, G, hG, hsum⟩
      have hnotmem : M + 1 ∉ G := by
        intro hmem
        have hleM : M + 1 ≤ M := (hG hmem).2
        omega
      refine ⟨insert (M + 1) G, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with hi_eq | hiG
        · subst i
          exact ⟨hI, by simp⟩
        · exact ⟨(hG hiG).1, le_trans (hG hiG).2 (Nat.le_succ M)⟩
      · have hsum_insert :
            ∑ i ∈ insert (M + 1) G, a i =
              a (M + 1) + ∑ i ∈ G, a i := by
          simp [Finset.sum_insert, hnotmem]
        rw [hsum_insert, hsum]
        omega

lemma CoversInterval.mono_index {a : ℕ → ℕ} {I : Set ℕ} {m n H T : ℕ}
    (hcover : CoversInterval a I m H T) (hmn : m ≤ n) :
    CoversInterval a I n H T := by
  intro t htH htT
  exact prefixSubsetSums_mono_index hmn (hcover t htH htT)

lemma CoversInterval.mono_set {a : ℕ → ℕ} {I J : Set ℕ} {n H T : ℕ}
    (hcover : CoversInterval a I n H T) (hIJ : I ∩ Set.Iic n ⊆ J ∩ Set.Iic n) :
    CoversInterval a J n H T := by
  intro t htH htT
  rcases hcover t htH htT with ⟨F, hFI, hsum⟩
  exact ⟨F, fun i hi => hIJ (hFI hi), hsum⟩

lemma cover_compl_of_cover_univ_of_avoid {a : ℕ → ℕ} {D : Set ℕ} {n H T : ℕ}
    (hcover : CoversInterval a Set.univ n H T)
    (havoid : Set.Iic n ⊆ Dᶜ) :
    CoversInterval a Dᶜ n H T := by
  refine CoversInterval.mono_set hcover ?_
  intro i hi
  exact ⟨havoid hi.2, hi.2⟩

lemma prefixSubsetSum_le_fullPrefixSum
    {a : ℕ → ℕ} {I : Set ℕ} {n t : ℕ}
    (ht : t ∈ prefixSubsetSums a I n) :
    t ≤ fullPrefixSum a n := by
  classical
  rcases ht with ⟨F, hFI, hsum⟩
  have hsum_le :
      ∑ i ∈ F, a i ≤ ∑ i ∈ Finset.range (n + 1), a i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hFI hi).2))
      (by
        intro i hi_range hiF
        exact Nat.zero_le (a i))
  have hsum_le_full : ∑ i ∈ F, a i ≤ fullPrefixSum a n := by
    simpa [fullPrefixSum] using hsum_le
  omega

lemma wide_prefix_cover_forces_zero_left
    {a : ℕ → ℕ} {M H T : ℕ}
    (hcover : CoversInterval a Set.univ M H T)
    (hHT : H ≤ T)
    (hwide : fullPrefixSum a M + H ≤ T) :
    H = 0 := by
  have hTmem : T ∈ prefixSubsetSums a Set.univ M := hcover T hHT le_rfl
  have hT_le : T ≤ fullPrefixSum a M :=
    prefixSubsetSum_le_fullPrefixSum hTmem
  omega

lemma exists_prefix_cover_univ_of_complete
    {a : ℕ → ℕ}
    (hcomplete : IsCompleteOn a Set.univ) :
    ∃ H : ℕ, ∀ T : ℕ, H ≤ T → ∃ M : ℕ, CoversInterval a Set.univ M H T := by
  classical
  rcases hcomplete with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  intro T hHT
  let rep : ℕ → Finset ℕ :=
    fun t => if ht : H ≤ t then Classical.choose (hH t ht) else ∅
  let U : Finset ℕ := (Finset.Icc H T).biUnion rep
  let M : ℕ := U.sup id
  refine ⟨M, ?_⟩
  intro t htH htT
  have htmem : t ∈ Finset.Icc H T := Finset.mem_Icc.mpr ⟨htH, htT⟩
  refine ⟨rep t, ?_, ?_⟩
  · intro i hi
    have hiU : i ∈ U := by
      simp only [U, Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨t, ⟨htH, htT⟩, hi⟩
    exact ⟨by simp, Finset.le_sup (f := id) hiU⟩
  · have hsum := (Classical.choose_spec (hH t htH)).2
    simpa [rep, htH] using hsum

lemma exists_prefix_cover_of_complete
    {a : ℕ → ℕ} {I : Set ℕ}
    (hcomplete : IsCompleteOn a I) :
    ∃ H : ℕ, ∀ T : ℕ, H ≤ T → ∃ M : ℕ, CoversInterval a I M H T := by
  classical
  rcases hcomplete with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  intro T hHT
  let rep : ℕ → Finset ℕ :=
    fun t => if ht : H ≤ t then Classical.choose (hH t ht) else ∅
  let U : Finset ℕ := (Finset.Icc H T).biUnion rep
  let M : ℕ := U.sup id
  refine ⟨M, ?_⟩
  intro t htH htT
  have htmem : t ∈ Finset.Icc H T := Finset.mem_Icc.mpr ⟨htH, htT⟩
  refine ⟨rep t, ?_, ?_⟩
  · intro i hi
    have hiU : i ∈ U := by
      simp only [U, Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨t, ⟨htH, htT⟩, hi⟩
    have hrep_subset : ↑(rep t) ⊆ I := by
      have hsub := (Classical.choose_spec (hH t htH)).1
      simpa [rep, htH] using hsub
    exact ⟨hrep_subset hi, Finset.le_sup (f := id) hiU⟩
  · have hsum := (Classical.choose_spec (hH t htH)).2
    simpa [rep, htH] using hsum

lemma finite_subset_iic {F : Set ℕ} (hF : F.Finite) :
    ∃ M : ℕ, F ⊆ Set.Iic M := by
  exact hF.bddAbove

lemma exists_prefix_cover_compl_of_finiteDeletionComplete
    {a : ℕ → ℕ} {F : Set ℕ}
    (hfinite : FiniteDeletionComplete a)
    (hF : F.Finite) :
    ∃ H : ℕ, ∀ T : ℕ, H ≤ T →
      ∃ M : ℕ, F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H T := by
  obtain ⟨H, hcoverH⟩ :=
    exists_prefix_cover_of_complete (hfinite F hF)
  obtain ⟨B, hB⟩ := finite_subset_iic hF
  refine ⟨H, ?_⟩
  intro T hHT
  obtain ⟨M0, hcover0⟩ := hcoverH T hHT
  refine ⟨max B M0, ?_, ?_⟩
  · intro i hi
    exact le_trans (hB hi) (le_max_left B M0)
  · exact hcover0.mono_index (le_max_right B M0)

lemma finset_term_le_sum_of_mem {a : ℕ → ℕ} {F : Finset ℕ} {i : ℕ}
    (hi : i ∈ F) :
    a i ≤ ∑ j ∈ F, a j := by
  have hsum := Finset.sum_erase_add (s := F) (f := a) hi
  omega

lemma subset_sum_eq_lt_next_uses_only_prefix
    {a : ℕ → ℕ} {F : Finset ℕ} {n t : ℕ}
    (hmono : StrictMono a)
    (hsum : ∑ i ∈ F, a i = t)
    (hlt : t < a (n + 1)) :
    ↑F ⊆ Set.Iic n := by
  intro i hi
  by_contra hnot
  have hni : n + 1 ≤ i := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have hainext : a (n + 1) ≤ a i := hmono.monotone hni
  have haisum : a i ≤ ∑ j ∈ F, a j := finset_term_le_sum_of_mem hi
  omega

lemma subsetSums_lt_next_subset_prefixSubsetSums
    {a : ℕ → ℕ} {I : Set ℕ} {n t : ℕ}
    (hmono : StrictMono a)
    (ht : t ∈ subsetSums a I)
    (hlt : t < a (n + 1)) :
    t ∈ prefixSubsetSums a I n := by
  rcases ht with ⟨F, hFI, hsum⟩
  have hprefix : ↑F ⊆ Set.Iic n :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum hlt
  exact ⟨F, fun i hi => ⟨hFI hi, hprefix hi⟩, hsum⟩

lemma complete_prefix_cover_two_mul_sub_one
    {a : ℕ → ℕ} {H q : ℕ}
    (hmono : StrictMono a)
    (hprev_pos : 0 < a (q + 1))
    (hcompleteH : ∀ t : ℕ, H ≤ t → t ∈ subsetSums a Set.univ)
    (hnext : a (q + 1) + H ≤ a (q + 2)) :
    CoversInterval a Set.univ (q + 1) H (2 * a (q + 1) - 1) := by
  classical
  intro t htH htT
  by_cases ht_lt_prev : t < a (q + 1)
  · exact prefixSubsetSums_mono_index (Nat.le_succ q)
      (subsetSums_lt_next_subset_prefixSubsetSums
        (a := a) (I := Set.univ) (n := q) hmono
        (hcompleteH t htH) ht_lt_prev)
  · by_cases ht_lt_middle : t < a (q + 1) + H
    · have ht_lt_next : t < a (q + 2) := lt_of_lt_of_le ht_lt_middle hnext
      exact subsetSums_lt_next_subset_prefixSubsetSums
        (a := a) (I := Set.univ) (n := q + 1) hmono
        (hcompleteH t htH) (by simpa [Nat.add_assoc] using ht_lt_next)
    · have hprev_le_t : a (q + 1) ≤ t := Nat.le_of_not_gt ht_lt_prev
      have hmiddle_le_t : a (q + 1) + H ≤ t := Nat.le_of_not_gt ht_lt_middle
      let y := t - a (q + 1)
      have hyH : H ≤ y := by
        dsimp [y]
        omega
      have hylt : y < a (q + 1) := by
        dsimp [y]
        omega
      have hyPrefix :
          y ∈ prefixSubsetSums a Set.univ q :=
        subsetSums_lt_next_subset_prefixSubsetSums
          (a := a) (I := Set.univ) (n := q) hmono
          (hcompleteH y hyH) hylt
      have ht_eq : t = a (q + 1) + y := by
        dsimp [y]
        omega
      have hsucc :
          t ∈ prefixSubsetSums a Set.univ (q + 1) := by
        rw [prefixSubsetSums_succ_iff]
        exact Or.inr ⟨by simp, by omega, by simpa [ht_eq] using hyPrefix⟩
      exact hsucc

lemma exists_initial_global_budget_seed_of_complete_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hcomplete : IsCompleteOn a Set.univ)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∃ H q : ℕ,
      H ≤ 2 * a (q + 1) - 1 ∧
        CoversInterval a Set.univ (q + 1) H (2 * a (q + 1) - 1) ∧
          a (q + 2) ≤ 2 * a (q + 1) - H := by
  rcases hcomplete with ⟨H, hcompleteH⟩
  have hnext :
      ∀ᶠ q in atTop, H + a (q + 1) ≤ a (q + 2) :=
    evt_const_add_next_le_next_next_of_uniformRatioGap
      hmono hpos hgap H
  have htwo :
      ∀ᶠ q in atTop, H + a (q + 2) ≤ a q + a (q + 1) :=
    evt_const_add_two_step_le_of_eventual_quotient_lt_rho
      hmono hpos hρ1 hρφ hupper H
  have hev :
      ∀ᶠ q in atTop,
        H + a (q + 1) ≤ a (q + 2) ∧
          H + a (q + 2) ≤ a q + a (q + 1) := by
    filter_upwards [hnext, htwo] with q hnextq htwoq
    exact ⟨hnextq, htwoq⟩
  obtain ⟨q, hq⟩ := eventually_atTop.1 hev
  have hqdata := hq q le_rfl
  have hprev_le : a q ≤ a (q + 1) :=
    (hmono (Nat.lt_succ_self q)).le
  have hbudget : a (q + 2) ≤ 2 * a (q + 1) - H := by
    omega
  have hnonempty : H ≤ 2 * a (q + 1) - 1 := by
    have hnext_pos : 0 < a (q + 2) := hpos (q + 2)
    omega
  refine ⟨H, q, hnonempty, ?_, hbudget⟩
  exact complete_prefix_cover_two_mul_sub_one
    hmono (hpos (q + 1)) hcompleteH
    (by simpa [Nat.add_comm] using hqdata.1)

lemma exists_initial_global_budget_seed_after_of_complete_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hcomplete : IsCompleteOn a Set.univ)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (B : ℕ) :
    ∃ H q : ℕ,
      B ≤ q ∧
        H ≤ 2 * a (q + 1) - 1 ∧
          CoversInterval a Set.univ (q + 1) H (2 * a (q + 1) - 1) ∧
            a (q + 2) ≤ 2 * a (q + 1) - H := by
  rcases hcomplete with ⟨H, hcompleteH⟩
  have hnext :
      ∀ᶠ q in atTop, H + a (q + 1) ≤ a (q + 2) :=
    evt_const_add_next_le_next_next_of_uniformRatioGap
      hmono hpos hgap H
  have htwo :
      ∀ᶠ q in atTop, H + a (q + 2) ≤ a q + a (q + 1) :=
    evt_const_add_two_step_le_of_eventual_quotient_lt_rho
      hmono hpos hρ1 hρφ hupper H
  have hev :
      ∀ᶠ q in atTop,
        H + a (q + 1) ≤ a (q + 2) ∧
          H + a (q + 2) ≤ a q + a (q + 1) := by
    filter_upwards [hnext, htwo] with q hnextq htwoq
    exact ⟨hnextq, htwoq⟩
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hev
  let q := max Q B
  have hqdata := hQ q (le_max_left Q B)
  have hBq : B ≤ q := le_max_right Q B
  have hprev_le : a q ≤ a (q + 1) :=
    (hmono (Nat.lt_succ_self q)).le
  have hbudget : a (q + 2) ≤ 2 * a (q + 1) - H := by
    omega
  have hnonempty : H ≤ 2 * a (q + 1) - 1 := by
    have hnext_pos : 0 < a (q + 2) := hpos (q + 2)
    omega
  refine ⟨H, q, hBq, hnonempty, ?_, hbudget⟩
  exact complete_prefix_cover_two_mul_sub_one
    hmono (hpos (q + 1)) hcompleteH
    (by simpa [Nat.add_comm] using hqdata.1)

lemma not_subsetSums_of_not_prefixSubsetSums_of_lt_next
    {a : ℕ → ℕ} {I : Set ℕ} {n t : ℕ}
    (hmono : StrictMono a)
    (hmiss : t ∉ prefixSubsetSums a I n)
    (hlt : t < a (n + 1)) :
    t ∉ subsetSums a I := by
  intro ht
  exact hmiss (subsetSums_lt_next_subset_prefixSubsetSums hmono ht hlt)

lemma subsetSums_avoiding_finite_singleton_lt_next_next_subset_prefix
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (hmono : StrictMono a)
    (ht : t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hlt : t < a (M + 2)) :
    t ∈ prefixSubsetSums a Fᶜ M := by
  rcases ht with ⟨G, hG, hsum⟩
  have hprefixM1 : ↑G ⊆ Set.Iic (M + 1) :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum (by simpa [Nat.add_assoc] using hlt)
  refine ⟨G, ?_, hsum⟩
  intro i hi
  have havoid := hG hi
  constructor
  · exact fun hiF => havoid (Or.inl hiF)
  · have hi_le_M1 : i ≤ M + 1 := hprefixM1 hi
    change i ≤ M + 1 at hi_le_M1
    have hi_ne_M1 : i ≠ M + 1 := by
      intro hi_eq
      exact havoid (by simp [hi_eq])
    change i ≤ M
    omega

lemma prefixSubsetSums_subset_subsetSums_avoiding_finite_singleton
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (ht : t ∈ prefixSubsetSums a Fᶜ M) :
    t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  rcases ht with ⟨G, hG, hsum⟩
  refine ⟨G, ?_, hsum⟩
  intro i hi
  rcases hG hi with ⟨hiF, hiM⟩
  intro hiDel
  rcases hiDel with hiF' | hiSing
  · exact hiF hiF'
  · have hi_eq : i = M + 1 := by simpa using hiSing
    change i ≤ M at hiM
    omega

theorem subsetSums_avoiding_finite_singleton_lt_next_next_iff_prefix
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (hmono : StrictMono a)
    (hlt : t < a (M + 2)) :
    t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ↔
      t ∈ prefixSubsetSums a Fᶜ M :=
  ⟨fun ht => subsetSums_avoiding_finite_singleton_lt_next_next_subset_prefix
      hmono ht hlt,
    prefixSubsetSums_subset_subsetSums_avoiding_finite_singleton⟩

lemma not_prefixSubsetSums_of_not_subsetSums_avoiding_finite_singleton
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (hmiss : t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    t ∉ prefixSubsetSums a Fᶜ M := by
  intro ht
  exact hmiss (prefixSubsetSums_subset_subsetSums_avoiding_finite_singleton ht)

lemma not_subsetSums_avoiding_finite_singleton_of_prefix_hole
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (hmono : StrictMono a)
    (hmiss : t ∉ prefixSubsetSums a Fᶜ M)
    (hlt : t < a (M + 2)) :
    t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  intro ht
  exact hmiss
    (subsetSums_avoiding_finite_singleton_lt_next_next_subset_prefix hmono ht hlt)

lemma exists_finite_singleton_hole_of_not_seed_margins
    {a : ℕ → ℕ} {F : Set ℕ} {M : ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hnext : a (M + 1) ≤ a (M + 2))
    (hpair : a (M + 3) ≤ a (M + 1) + a (M + 2))
    (hnot :
      ¬ (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) := by
  classical
  by_cases hkeep :
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
        a (M + 1) ≤ a (M + 2)
  · have hnot_margin :
        ¬ leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2) := by
      intro hmargin
      exact hnot ⟨hkeep, hmargin⟩
    obtain ⟨t, hlow, htT, hmiss⟩ :=
      exists_prefix_hole_of_not_seed_margin
        (a := a) (I := Fᶜ) (M := M) hpair hnot_margin
    have hlt : t < a (M + 2) := by
      have hA2pos : 0 < a (M + 2) := hpos (M + 2)
      omega
    exact ⟨t, htT, hlt,
      not_subsetSums_avoiding_finite_singleton_of_prefix_hole hmono hmiss hlt,
      Or.inr hlow⟩
  · obtain ⟨t, hlow, htT, hmiss⟩ :=
      exists_prefix_hole_of_not_seed_keep
        (a := a) (I := Fᶜ) (M := M) hnext hkeep
    have hlt : t < a (M + 2) := by
      have hA2pos : 0 < a (M + 2) := hpos (M + 2)
      omega
    exact ⟨t, htT, hlt,
      not_subsetSums_avoiding_finite_singleton_of_prefix_hole hmono hmiss hlt,
      Or.inl hlow⟩

lemma finite_singleton_hole_mem_base_compl_forces_shifted_prefix
    {a : ℕ → ℕ} {F : Set ℕ} {H M t : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hHt : H ≤ t)
    (hmiss : t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hlt : t < a (M + 2)) :
    a (M + 1) ≤ t ∧ t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M := by
  classical
  rcases hcompleteF t hHt with ⟨G, hG, hsum⟩
  have hprefixM1 : ↑G ⊆ Set.Iic (M + 1) :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum
      (by simpa [Nat.add_assoc] using hlt)
  have hM1G : M + 1 ∈ G := by
    by_contra hnotM1
    have havoid : ↑G ⊆ (F ∪ ({M + 1} : Set ℕ))ᶜ := by
      intro i hi
      have hiF : i ∉ F := hG hi
      have hi_ne : i ≠ M + 1 := by
        intro hi_eq
        exact hnotM1 (hi_eq ▸ hi)
      intro hiDel
      rcases hiDel with hiF' | hiSing
      · exact hiF hiF'
      · exact hi_ne (by simpa using hiSing)
    exact hmiss ⟨G, havoid, hsum⟩
  have ha_le_t : a (M + 1) ≤ t := by
    have hterm : a (M + 1) ≤ ∑ i ∈ G, a i :=
      finset_term_le_sum_of_mem hM1G
    omega
  have hEraseSubset : ↑(G.erase (M + 1)) ⊆ Fᶜ ∩ Set.Iic M := by
    intro i hi
    have hiG : i ∈ G := Finset.mem_of_mem_erase hi
    constructor
    · exact hG hiG
    · have hi_le_M1 : i ≤ M + 1 := hprefixM1 hiG
      have hi_ne_M1 : i ≠ M + 1 := (Finset.mem_erase.mp hi).1
      change i ≤ M
      omega
  have hEraseSum : ∑ i ∈ G.erase (M + 1), a i = t - a (M + 1) := by
    have hsplit := Finset.sum_erase_add (s := G) (f := a) hM1G
    omega
  exact ⟨ha_le_t, ⟨G.erase (M + 1), hEraseSubset, hEraseSum⟩⟩

lemma finite_singleton_hole_lt_next_forces_shifted_prefix
    {a : ℕ → ℕ} {F : Set ℕ} {H M R t : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hHt : H ≤ t)
    (hmiss : t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hlt : t < a (R + 1)) :
    a (M + 1) ≤ t ∧
      t - a (M + 1) ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ R := by
  classical
  rcases hcompleteF t hHt with ⟨G, hG, hsum⟩
  have hprefixR : ↑G ⊆ Set.Iic R :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum hlt
  have hM1G : M + 1 ∈ G := by
    by_contra hnotM1
    have havoid : ↑G ⊆ (F ∪ ({M + 1} : Set ℕ))ᶜ := by
      intro i hi
      have hiF : i ∉ F := hG hi
      have hi_ne : i ≠ M + 1 := by
        intro hi_eq
        exact hnotM1 (hi_eq ▸ hi)
      intro hiDel
      rcases hiDel with hiF' | hiSing
      · exact hiF hiF'
      · exact hi_ne (by simpa using hiSing)
    exact hmiss ⟨G, havoid, hsum⟩
  have ha_le_t : a (M + 1) ≤ t := by
    have hterm : a (M + 1) ≤ ∑ i ∈ G, a i :=
      finset_term_le_sum_of_mem hM1G
    omega
  have hEraseSubset :
      ↑(G.erase (M + 1)) ⊆
        (F ∪ ({M + 1} : Set ℕ))ᶜ ∩ Set.Iic R := by
    intro i hi
    have hiG : i ∈ G := Finset.mem_of_mem_erase hi
    constructor
    · intro hiDel
      rcases hiDel with hiF | hiSing
      · exact hG hiG hiF
      · have hi_ne_M1 : i ≠ M + 1 := (Finset.mem_erase.mp hi).1
        exact hi_ne_M1 (by simpa using hiSing)
    · exact hprefixR hiG
  have hEraseSum : ∑ i ∈ G.erase (M + 1), a i = t - a (M + 1) := by
    have hsplit := Finset.sum_erase_add (s := G) (f := a) hM1G
    omega
  exact ⟨ha_le_t, ⟨G.erase (M + 1), hEraseSubset, hEraseSum⟩⟩

lemma finite_singleton_hole_lt_next3_forces_shifted_prefix
    {a : ℕ → ℕ} {F : Set ℕ} {H M t : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hHt : H ≤ t)
    (hmiss : t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hlt : t < a (M + 3)) :
    a (M + 1) ≤ t ∧
      t - a (M + 1) ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ (M + 2) := by
  classical
  rcases hcompleteF t hHt with ⟨G, hG, hsum⟩
  have hprefixM2 : ↑G ⊆ Set.Iic (M + 2) :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum
      (by simpa [Nat.add_assoc] using hlt)
  have hM1G : M + 1 ∈ G := by
    by_contra hnotM1
    have havoid : ↑G ⊆ (F ∪ ({M + 1} : Set ℕ))ᶜ := by
      intro i hi
      have hiF : i ∉ F := hG hi
      have hi_ne : i ≠ M + 1 := by
        intro hi_eq
        exact hnotM1 (hi_eq ▸ hi)
      intro hiDel
      rcases hiDel with hiF' | hiSing
      · exact hiF hiF'
      · exact hi_ne (by simpa using hiSing)
    exact hmiss ⟨G, havoid, hsum⟩
  have ha_le_t : a (M + 1) ≤ t := by
    have hterm : a (M + 1) ≤ ∑ i ∈ G, a i :=
      finset_term_le_sum_of_mem hM1G
    omega
  have hEraseSubset :
      ↑(G.erase (M + 1)) ⊆
        (F ∪ ({M + 1} : Set ℕ))ᶜ ∩ Set.Iic (M + 2) := by
    intro i hi
    have hiG : i ∈ G := Finset.mem_of_mem_erase hi
    constructor
    · intro hiDel
      rcases hiDel with hiF | hiSing
      · exact hG hiG hiF
      · have hi_ne_M1 : i ≠ M + 1 := (Finset.mem_erase.mp hi).1
        exact hi_ne_M1 (by simpa using hiSing)
    · exact hprefixM2 hiG
  have hEraseSum : ∑ i ∈ G.erase (M + 1), a i = t - a (M + 1) := by
    have hsplit := Finset.sum_erase_add (s := G) (f := a) hM1G
    omega
  exact ⟨ha_le_t, ⟨G.erase (M + 1), hEraseSubset, hEraseSum⟩⟩

lemma finite_singleton_hole_ge_base_threshold_forces_shifted_prefix_of_finiteDeletionComplete
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite) :
    ∃ H : ℕ, ∀ M t : ℕ, H ≤ t →
      t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ →
        t < a (M + 2) →
          a (M + 1) ≤ t ∧
            t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M := by
  rcases hfinite F hFfinite with ⟨H, hH⟩
  exact ⟨H, fun M t hHt hmiss hlt =>
    finite_singleton_hole_mem_base_compl_forces_shifted_prefix
      hmono hH hHt hmiss hlt⟩

lemma shifted_prefix_source_lt_nextSeedMargin
    {a : ℕ → ℕ} {M t : ℕ}
    (ha : a (M + 1) ≤ t)
    (hlt : t < a (M + 2)) :
    t - a (M + 1) < nextSeedMargin a M := by
  dsimp [nextSeedMargin]
  omega

lemma shifted_prefix_hole_gives_prefix_shift_gap
    {a : ℕ → ℕ} {F : Set ℕ} {M t : ℕ}
    (ha : a (M + 1) ≤ t)
    (hsource : t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M)
    (hmiss : t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hlt : t < a (M + 2)) :
    ∃ s : ℕ,
      s ∈ prefixSubsetSums a Fᶜ M ∧
        s < nextSeedMargin a M ∧
          a (M + 1) + s < a (M + 2) ∧
            a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  let s := t - a (M + 1)
  have hadd : a (M + 1) + s = t := by
    dsimp [s]
    omega
  have hnotPrefix : t ∉ prefixSubsetSums a Fᶜ M :=
    not_prefixSubsetSums_of_not_subsetSums_avoiding_finite_singleton hmiss
  refine ⟨s, hsource, shifted_prefix_source_lt_nextSeedMargin ha hlt, ?_, ?_⟩
  · simpa [hadd] using hlt
  · intro hs
    exact hnotPrefix (by simpa [hadd] using hs)

lemma pred_finSingletonCompleteThreshold_small_forces_prefix_shift_gap
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {H M : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hHprev : H ≤ a (M + 1))
    (hprevlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M)
    (hthreshold_le : finSingletonCompleteThreshold a hfinite hF M ≤ a (M + 2)) :
    ∃ s : ℕ,
      s ∈ prefixSubsetSums a Fᶜ M ∧
        s < nextSeedMargin a M ∧
          a (M + 1) + s < a (M + 2) ∧
            a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  let t := finSingletonCompleteThreshold a hfinite hF M - 1
  have hmiss :
      t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
    dsimp [t]
    exact pred_finSingletonCompleteThreshold_hole_of_prev_lt
      hfinite hF hprevlt
  have hprev_le_t : a (M + 1) ≤ t := by
    dsimp [t]
    exact pred_finSingletonCompleteThreshold_ge_prev_of_prev_lt
      hfinite hF hprevlt
  have htlt : t < a (M + 2) := by
    dsimp [t]
    omega
  have hHt : H ≤ t := le_trans hHprev hprev_le_t
  have hshifted :
      a (M + 1) ≤ t ∧ t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M :=
    finite_singleton_hole_mem_base_compl_forces_shifted_prefix
      hmono hcompleteF hHt hmiss htlt
  exact shifted_prefix_hole_gives_prefix_shift_gap
    hshifted.1 hshifted.2 hmiss htlt

lemma pred_finSingletonCompleteThreshold_next_forces_shifted_prefix
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {H M R : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hM1R : M + 1 < R)
    (hHR : H ≤ a R)
    (hRlt : a R < finSingletonCompleteThreshold a hfinite hF M)
    (hthreshold_le : finSingletonCompleteThreshold a hfinite hF M ≤ a (R + 1)) :
    ∃ t s : ℕ,
      t = finSingletonCompleteThreshold a hfinite hF M - 1 ∧
        a R ≤ t ∧ t < a (R + 1) ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
            s = t - a (M + 1) ∧
              s ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ R := by
  let t := finSingletonCompleteThreshold a hfinite hF M - 1
  have hprevlt : a (M + 1) < finSingletonCompleteThreshold a hfinite hF M := by
    have hmonoM1R : a (M + 1) < a R := hmono hM1R
    omega
  have hmiss :
      t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
    dsimp [t]
    exact pred_finSingletonCompleteThreshold_hole_of_prev_lt
      hfinite hF hprevlt
  have hR_le_t : a R ≤ t := by
    dsimp [t]
    omega
  have htlt : t < a (R + 1) := by
    dsimp [t]
    omega
  have hHt : H ≤ t := le_trans hHR hR_le_t
  have hshifted :
      a (M + 1) ≤ t ∧
        t - a (M + 1) ∈
          prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ R :=
    finite_singleton_hole_lt_next_forces_shifted_prefix
      hmono hcompleteF hHt hmiss htlt
  exact ⟨t, t - a (M + 1), rfl, hR_le_t, htlt, hmiss, rfl, hshifted.2⟩

lemma pred_finSingletonCompleteThreshold_next3_forces_shifted_prefix
    {a : ℕ → ℕ} (hfinite : FiniteDeletionComplete a)
    {F : Set ℕ} (hF : F.Finite) {H M : ℕ}
    (hmono : StrictMono a)
    (hcompleteF : ∀ u : ℕ, H ≤ u → u ∈ subsetSums a Fᶜ)
    (hHnext : H ≤ a (M + 2))
    (hnextlt : a (M + 2) < finSingletonCompleteThreshold a hfinite hF M)
    (hthreshold_le : finSingletonCompleteThreshold a hfinite hF M ≤ a (M + 3)) :
    ∃ t s : ℕ,
      t = finSingletonCompleteThreshold a hfinite hF M - 1 ∧
        a (M + 2) ≤ t ∧ t < a (M + 3) ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
            s = t - a (M + 1) ∧
              s ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ (M + 2) := by
  simpa [Nat.add_assoc] using
    (pred_finSingletonCompleteThreshold_next_forces_shifted_prefix
      (R := M + 2) hfinite hF hmono hcompleteF
      (by omega) hHnext hnextlt
      (by simpa [Nat.add_assoc] using hthreshold_le))

lemma first_prefix_cover_of_succ_cover_and_shiftClosed
    {a : ℕ → ℕ} {F : Set ℕ} {M : ℕ}
    (hpos : 0 < a (M + 2))
    (hcoverSucc :
      CoversInterval a Fᶜ (M + 1) (nextSeedMargin a M) (a (M + 2) - 1))
    (hclosed : FirstWindowShiftClosed a F M) :
    CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1) := by
  intro t hlow htT
  have htSucc : t ∈ prefixSubsetSums a Fᶜ (M + 1) :=
    hcoverSucc t hlow htT
  rcases (prefixSubsetSums_succ_iff (a := a) (I := Fᶜ) (M := M) (t := t)).mp
      htSucc with htPrefix | htShift
  · exact htPrefix
  · rcases htShift with ⟨_hI, ha, hsource⟩
    have hlt : t < a (M + 2) := by omega
    have hs_lt : t - a (M + 1) < nextSeedMargin a M :=
      shifted_prefix_source_lt_nextSeedMargin ha hlt
    have hshift := hclosed (t - a (M + 1)) hsource hs_lt
    have hadd : a (M + 1) + (t - a (M + 1)) = t := by omega
    simpa [hadd] using hshift

lemma firstWindowShiftClosed_of_first_prefix_cover_of_nextSeedMargin_le_prev
    {a : ℕ → ℕ} {F : Set ℕ} {M : ℕ}
    (hnext_le : nextSeedMargin a M ≤ a (M + 1))
    (hcover :
      CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    FirstWindowShiftClosed a F M := by
  intro s hs hslt
  have hlow : nextSeedMargin a M ≤ a (M + 1) + s :=
    le_trans hnext_le (Nat.le_add_right _ _)
  have hlt : a (M + 1) + s < a (M + 2) := by
    dsimp [nextSeedMargin] at hslt
    omega
  have hupper : a (M + 1) + s ≤ a (M + 2) - 1 := by
    omega
  exact hcover (a (M + 1) + s) hlow hupper

lemma firstWindowShiftClosed_of_finSingletonCompleteBelowPrev
    {a : ℕ → ℕ} {F : Set ℕ} {M : ℕ}
    (hmono : StrictMono a)
    (hbelow : FinSingletonCompleteBelowPrev a F M) :
    FirstWindowShiftClosed a F M := by
  rcases hbelow with ⟨H, hHprev, hcomplete⟩
  intro s hs hslt
  have hnext : a (M + 1) ≤ a (M + 2) :=
    (hmono (by omega : M + 1 < M + 2)).le
  have hlt : a (M + 1) + s < a (M + 2) := by
    dsimp [nextSeedMargin] at hslt
    omega
  have hH : H ≤ a (M + 1) + s :=
    le_trans hHprev (Nat.le_add_right _ _)
  have hsum :
      a (M + 1) + s ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ :=
    hcomplete (a (M + 1) + s) hH
  exact
    (subsetSums_avoiding_finite_singleton_lt_next_next_iff_prefix
      (a := a) (F := F) (M := M) (t := a (M + 1) + s)
      hmono hlt).mp hsum

lemma prefix_shift_gap_forces_nextSeedMargin_lt_least
    {a : ℕ → ℕ} {F : Set ℕ} {M s : ℕ}
    (hnext_le : nextSeedMargin a M ≤ a (M + 1))
    (hgap :
      s ∈ prefixSubsetSums a Fᶜ M ∧
        s < nextSeedMargin a M ∧
          a (M + 1) + s < a (M + 2) ∧
            a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M) :
    nextSeedMargin a M <
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) := by
  refine lt_leastPrefixCoverThreshold_of_exists_prefix_hole ?_
  refine ⟨a (M + 1) + s, ?_, ?_, hgap.2.2.2⟩
  · exact le_trans hnext_le (Nat.le_add_right _ _)
  · omega

lemma complete_forces_next_le_fullPrefixSum_add_one
    {a : ℕ → ℕ} {H n : ℕ}
    (hmono : StrictMono a)
    (hcomplete : ∀ t : ℕ, H ≤ t → t ∈ subsetSums a Set.univ)
    (hH : H ≤ fullPrefixSum a n + 1) :
    a (n + 1) ≤ fullPrefixSum a n + 1 := by
  by_contra hnot
  have hlt : fullPrefixSum a n + 1 < a (n + 1) := Nat.lt_of_not_ge hnot
  rcases hcomplete (fullPrefixSum a n + 1) hH with ⟨F, hF, hsum⟩
  have hprefix : ↑F ⊆ Set.Iic n :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum hlt
  have hsum_le :
      ∑ i ∈ F, a i ≤ ∑ i ∈ Finset.range (n + 1), a i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hprefix hi)))
      (by
        intro i hi_range hiF
        exact Nat.zero_le (a i))
  have hsum_le_full : ∑ i ∈ F, a i ≤ fullPrefixSum a n := by
    simpa [fullPrefixSum] using hsum_le
  omega

lemma complete_prefix_cover_of_lt_next
    {a : ℕ → ℕ} {H n T : ℕ}
    (hmono : StrictMono a)
    (hcomplete : ∀ t : ℕ, H ≤ t → t ∈ subsetSums a Set.univ)
    (hTlt : T < a (n + 1)) :
    CoversInterval a Set.univ n H T := by
  intro t htH htT
  rcases hcomplete t htH with ⟨F, hF, hsum⟩
  have htlt : t < a (n + 1) := lt_of_le_of_lt htT hTlt
  have hprefix : ↑F ⊆ Set.Iic n :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum htlt
  exact ⟨F, fun i hi => ⟨by simp, hprefix hi⟩, hsum⟩

lemma complete_prefix_cover_of_lt_next_on
    {a : ℕ → ℕ} {I : Set ℕ} {H n T : ℕ}
    (hmono : StrictMono a)
    (hcomplete : ∀ t : ℕ, H ≤ t → t ∈ subsetSums a I)
    (hTlt : T < a (n + 1)) :
    CoversInterval a I n H T := by
  intro t htH htT
  rcases hcomplete t htH with ⟨F, hF, hsum⟩
  have htlt : t < a (n + 1) := lt_of_le_of_lt htT hTlt
  have hprefix : ↑F ⊆ Set.Iic n :=
    subset_sum_eq_lt_next_uses_only_prefix hmono hsum htlt
  exact ⟨F, fun i hi => ⟨hF hi, hprefix hi⟩, hsum⟩

lemma exists_prefix_cover_compl_lt_next_of_finiteDeletionComplete
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hfinite : FiniteDeletionComplete a)
    (hF : F.Finite) :
    ∃ H : ℕ, ∀ n T : ℕ, T < a (n + 1) →
      CoversInterval a Fᶜ n H T := by
  obtain ⟨H, hH⟩ := hfinite F hF
  exact ⟨H, fun n T hTlt =>
    complete_prefix_cover_of_lt_next_on hmono hH hTlt⟩

lemma keptPrefixSum_add_deletedPrefixSum
    {a : ℕ → ℕ} {D : Set ℕ} {n : ℕ} :
    keptPrefixSum a D n + deletedPrefixSum a D n = fullPrefixSum a n := by
  classical
  simpa [keptPrefixSum, deletedPrefixSum, fullPrefixSum, add_comm] using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.range (n + 1))
      (p := fun i => i ∈ D) (f := a))

lemma keptPrefixSum_eq_fullPrefixSum_sub_deletedPrefixSum
    {a : ℕ → ℕ} {D : Set ℕ} {n : ℕ} :
    keptPrefixSum a D n = fullPrefixSum a n - deletedPrefixSum a D n := by
  have hsum := keptPrefixSum_add_deletedPrefixSum (a := a) (D := D) (n := n)
  omega

lemma deletedPrefixSum_eq_zero_of_avoid
    {a : ℕ → ℕ} {D : Set ℕ} {n : ℕ}
    (havoid : Set.Iic n ⊆ Dᶜ) :
    deletedPrefixSum a D n = 0 := by
  classical
  unfold deletedPrefixSum
  apply Finset.sum_eq_zero
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hirange, hiD⟩
  have hinitial : i ∈ Set.Iic n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
  exact False.elim ((havoid hinitial) hiD)

lemma deletedPrefixSum_mono_set
    {a : ℕ → ℕ} {D E : Set ℕ} {n : ℕ}
    (hDE : D ∩ Set.Iic n ⊆ E ∩ Set.Iic n) :
    deletedPrefixSum a D n ≤ deletedPrefixSum a E n := by
  classical
  unfold deletedPrefixSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hirange, hiD⟩
    have hiIic : i ∈ Set.Iic n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
    have hiE : i ∈ E := (hDE ⟨hiD, hiIic⟩).1
    exact Finset.mem_filter.mpr ⟨hirange, hiE⟩
  · intro i hiE hiD
    exact Nat.zero_le (a i)

lemma finset_sum_union_le_add
    {a : ℕ → ℕ} {s t : Finset ℕ} :
    ∑ i ∈ s ∪ t, a i ≤ (∑ i ∈ s, a i) + ∑ i ∈ t, a i := by
  classical
  let u := t \ s
  have hunion : s ∪ u = s ∪ t := by
    ext i
    simp [u]
  have hdisj : Disjoint s u := by
    rw [Finset.disjoint_left]
    intro i his hiu
    exact (Finset.mem_sdiff.mp hiu).2 his
  have hsum_union :
      (∑ i ∈ s ∪ u, a i) = (∑ i ∈ s, a i) + ∑ i ∈ u, a i := by
    rw [Finset.sum_union hdisj]
  have hu_le_t : (∑ i ∈ u, a i) ≤ ∑ i ∈ t, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro i hi
        exact (Finset.mem_sdiff.mp hi).1)
      (by
        intro i hit hiu
        exact Nat.zero_le (a i))
  rw [← hunion, hsum_union]
  omega

lemma fullPrefixSum_succ {a : ℕ → ℕ} {n : ℕ} :
    fullPrefixSum a (n + 1) = fullPrefixSum a n + a (n + 1) := by
  simp [fullPrefixSum, Finset.sum_range_succ, Nat.add_assoc]

lemma fullPrefixSum_mono {a : ℕ → ℕ} :
    Monotone (fullPrefixSum a) := by
  intro m n hmn
  induction hmn with
  | refl =>
      rfl
  | @step n hmn ih =>
      rw [fullPrefixSum_succ]
      exact le_trans ih (Nat.le_add_right _ _)

lemma succ_le_fullPrefixSum_of_pos {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a n) :
    ∀ n : ℕ, n + 1 ≤ fullPrefixSum a n := by
  intro n
  induction n with
  | zero =>
      simp only [fullPrefixSum, zero_add, Finset.sum_range_one]
      exact hpos 0
  | succ n ih =>
      rw [fullPrefixSum_succ]
      have hterm : 1 ≤ a (n + 1) := hpos (n + 1)
      omega

theorem evt_next_le_fullPrefixSum_add_one_of_complete
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcomplete : IsCompleteOn a Set.univ) :
    ∀ᶠ n in atTop, a (n + 1) ≤ fullPrefixSum a n + 1 := by
  rcases hcomplete with ⟨H, hH⟩
  refine eventually_atTop.2 ⟨H, ?_⟩
  intro n hn
  have htarget : H ≤ fullPrefixSum a n + 1 := by
    have hs := succ_le_fullPrefixSum_of_pos hpos n
    omega
  exact complete_forces_next_le_fullPrefixSum_add_one hmono hH htarget

lemma next_add_fullPrefixSum_ge_add_next_of_evt_two_mul_aux
    {a : ℕ → ℕ} {N : ℕ}
    (hsmall : ∀ n : ℕ, N ≤ n → a (n + 2) < 2 * a (n + 1)) :
    ∀ k : ℕ,
      a (N + 1) + fullPrefixSum a (N + k) ≥ k + a (N + k + 1) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hgap : a (N + k + 2) < 2 * a (N + k + 1) := by
        simpa [Nat.add_assoc] using hsmall (N + k) (Nat.le_add_right N k)
      rw [show N + (k + 1) = (N + k) + 1 by omega, fullPrefixSum_succ]
      change k + 1 + a (N + k + 2) ≤
        a (N + 1) + (fullPrefixSum a (N + k) + a (N + k + 1))
      omega

lemma evt_const_add_next_le_fullPrefixSum_of_evt_two_mul
    {a : ℕ → ℕ}
    (hsmall : ∀ᶠ n in atTop, a (n + 2) < 2 * a (n + 1)) :
    ∀ C : ℕ, ∀ᶠ n in atTop, C + a (n + 1) ≤ fullPrefixSum a n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  intro C
  refine eventually_atTop.2 ⟨N + (C + a (N + 1)), ?_⟩
  intro n hn
  have hNn : N ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNn
  subst n
  have hklarge : C + a (N + 1) ≤ k := by omega
  have haux := next_add_fullPrefixSum_ge_add_next_of_evt_two_mul_aux
    (a := a) (N := N) hN k
  omega

lemma two_initial_add_fullPrefixSum_ge_add_pair_aux
    {a : ℕ → ℕ} {N : ℕ}
    (hsmall : ∀ n : ℕ, N ≤ n → a (n + 2) < a n + a (n + 1)) :
    ∀ k : ℕ,
      a N + a (N + 1) + fullPrefixSum a (N + k) ≥
        k + (a (N + k) + a (N + k + 1)) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hgap : a (N + k + 2) < a (N + k) + a (N + k + 1) := by
        simpa [Nat.add_assoc] using hsmall (N + k) (Nat.le_add_right N k)
      rw [show N + (k + 1) = (N + k) + 1 by omega, fullPrefixSum_succ]
      change k + 1 + (a (N + k + 1) + a (N + k + 2)) ≤
        a N + a (N + 1) + (fullPrefixSum a (N + k) + a (N + k + 1))
      omega

lemma evt_const_add_pair_le_fullPrefixSum_of_evt_pair_gap
    {a : ℕ → ℕ}
    (hsmall : ∀ᶠ n in atTop, a (n + 2) < a n + a (n + 1)) :
    ∀ C : ℕ, ∀ᶠ n in atTop, C + a n + a (n + 1) ≤ fullPrefixSum a n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  intro C
  refine eventually_atTop.2 ⟨N + (C + a N + a (N + 1)), ?_⟩
  intro n hn
  have hNn : N ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNn
  subst n
  have hklarge : C + a N + a (N + 1) ≤ k := by omega
  have haux := two_initial_add_fullPrefixSum_ge_add_pair_aux
    (a := a) (N := N) hN k
  omega

lemma evt_pair_prefix_surplus_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ C : ℕ, ∀ᶠ n in atTop, C + a n + a (n + 1) ≤ fullPrefixSum a n := by
  exact evt_const_add_pair_le_fullPrefixSum_of_evt_pair_gap
    (evt_two_step_sum_gt_of_eventual_quotient_lt_rho hpos hρ1 hρφ hupper)

lemma evt_next_next_seed_tail_conditions_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ M in atTop,
      a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
        ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) := by
  obtain ⟨Npair, hNpair⟩ := eventually_atTop.1
    (evt_pair_prefix_surplus_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper 0)
  obtain ⟨Nstep, hNstep⟩ := eventually_atTop.1
    (evt_two_step_le_of_eventual_quotient_lt_rho hpos hρ1 hρφ hupper)
  refine eventually_atTop.2 ⟨max Npair Nstep, ?_⟩
  intro M hM
  constructor
  · have hp := hNpair (M + 2) (by omega)
    simpa [Nat.add_assoc] using hp
  · intro n hn
    exact hNstep n (by omega)

lemma evt_next_next_seed_numeric_conditions
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ H : ℕ, ∀ᶠ M in atTop,
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) := by
  intro H
  filter_upwards
    [evt_const_add_next_le_next_next_of_uniformRatioGap
      hmono hpos hratioGap H,
     evt_next_next_seed_tail_conditions_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper] with M hkeep htail
  exact ⟨hkeep, htail.1, htail.2⟩

lemma evt_next_next_seed_numeric_conditions_with_margin
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ H : ℕ, ∀ᶠ M in atTop,
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) := by
  intro H
  obtain ⟨Nmargin, hNmargin⟩ := eventually_atTop.1
    (evt_const_add_two_step_le_of_eventual_quotient_lt_rho
      hmono hpos hρ1 hρφ hupper H)
  have hmarginEv :
      ∀ᶠ M in atTop, H + a (M + 3) ≤ a (M + 1) + a (M + 2) := by
    refine eventually_atTop.2 ⟨Nmargin, ?_⟩
    intro M hM
    have hm := hNmargin (M + 1) (le_trans hM (Nat.le_succ M))
    simpa [Nat.add_assoc] using hm
  filter_upwards
    [evt_next_next_seed_numeric_conditions
      hmono hpos hratioGap hρ1 hρφ hupper H,
     hmarginEv] with M hnum hmargin
  exact ⟨hnum.1, hnum.2.1, hmargin, hnum.2.2⟩

lemma range_infinite_of_strictMono_nat {b : ℕ → ℕ} (hb : StrictMono b) :
    (Set.range b).Infinite := by
  exact Set.infinite_range_of_injective hb.injective

lemma strictMono_nat_add_le {b : ℕ → ℕ} (hb : StrictMono b) :
    ∀ k : ℕ, b 0 + k ≤ b k := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep : b k < b (k + 1) := hb (Nat.lt_succ_self k)
      omega

lemma strictMono_of_gap_one {b : ℕ → ℕ}
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1)) :
    StrictMono b := by
  exact strictMono_nat_of_lt_succ
    (fun k => lt_trans (Nat.lt_succ_self (b k)) (hgap k))

lemma deletedPrefixSum_range_le_indexedDeletedSum_of_lt
    {a b : ℕ → ℕ} {n k : ℕ}
    (hb : StrictMono b) (hnk : n < b k) :
    deletedPrefixSum a (Set.range b) n ≤ indexedDeletedSum a b k := by
  classical
  unfold deletedPrefixSum indexedDeletedSum
  let s := (Finset.range (n + 1)).filter (fun i => i ∈ Set.range b)
  let t := (Finset.range k).image b
  have hsubset : s ⊆ t := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hirange, himem⟩
    rcases himem with ⟨j, rfl⟩
    have hbj_le_n : b j ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
    have hjk : j < k := by
      by_contra hnot
      have hkj : k ≤ j := Nat.le_of_not_gt hnot
      have hbk_le_bj : b k ≤ b j := hb.monotone hkj
      omega
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjk, rfl⟩
  have hsum_le :
      (∑ i ∈ s, a i) ≤ ∑ i ∈ t, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx_t hx_s
      exact Nat.zero_le (a x))
  have hsum_image : (∑ i ∈ t, a i) = ∑ j ∈ Finset.range k, a (b j) := by
    dsimp [t]
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hb.injective hxy
  exact le_trans hsum_le (le_of_eq hsum_image)

lemma deletedPrefixSum_range_le_indexedDeletedSum_between
    {a b : ℕ → ℕ} {n k : ℕ}
    (hb : StrictMono b) (_hleft : b k ≤ n) (hright : n < b (k + 1)) :
    deletedPrefixSum a (Set.range b) n ≤ indexedDeletedSum a b (k + 1) := by
  exact deletedPrefixSum_range_le_indexedDeletedSum_of_lt hb hright

lemma deletedPrefixSum_initialTail_le_initial_add_range
    {a b : ℕ → ℕ} {F : Set ℕ} {M n : ℕ}
    (hF : F ⊆ Set.Iic M) :
    deletedPrefixSum a (initialTailDeletionSet F b) n ≤
      deletedPrefixSum a (initialTailDeletionSet F b) M +
        deletedPrefixSum a (Set.range b) n := by
  classical
  unfold deletedPrefixSum
  let s := (Finset.range (n + 1)).filter
    (fun i => i ∈ initialTailDeletionSet F b)
  let s0 := (Finset.range (M + 1)).filter
    (fun i => i ∈ initialTailDeletionSet F b)
  let sr := (Finset.range (n + 1)).filter (fun i => i ∈ Set.range b)
  have hsub : s ⊆ s0 ∪ sr := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hirange, hiD⟩
    rcases hiD with hiF | hirangeb
    · have hiM : i ≤ M := hF hiF
      exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiM), Or.inl hiF⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hirange, hirangeb⟩
  have hsum_le :
      (∑ i ∈ s, a i) ≤ ∑ i ∈ s0 ∪ sr, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi_union hi_s
      exact Nat.zero_le (a i))
  have hunion_le :
      (∑ i ∈ s0 ∪ sr, a i) ≤ (∑ i ∈ s0, a i) + ∑ i ∈ sr, a i :=
    finset_sum_union_le_add
  exact le_trans hsum_le hunion_le

lemma deletedPrefixSum_initialTail_le_initial_add_indexedDeletedSum_of_lt
    {a b : ℕ → ℕ} {F : Set ℕ} {M n k : ℕ}
    (hF : F ⊆ Set.Iic M) (hb : StrictMono b) (hnk : n < b k) :
    deletedPrefixSum a (initialTailDeletionSet F b) n ≤
      deletedPrefixSum a (initialTailDeletionSet F b) M +
        indexedDeletedSum a b k := by
  have hsplit :=
    deletedPrefixSum_initialTail_le_initial_add_range
      (a := a) (b := b) (F := F) (M := M) (n := n) hF
  have hrange :=
    deletedPrefixSum_range_le_indexedDeletedSum_of_lt
      (a := a) (b := b) (n := n) (k := k) hb hnk
  omega

lemma deletedPrefixSum_initialTail_le_initial_of_lt_first
    {a b : ℕ → ℕ} {F : Set ℕ} {M n : ℕ}
    (hF : F ⊆ Set.Iic M) (hb : StrictMono b) (hn : n < b 0) :
    deletedPrefixSum a (initialTailDeletionSet F b) n ≤
      deletedPrefixSum a (initialTailDeletionSet F b) M := by
  classical
  unfold deletedPrefixSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hirange, hiD⟩
    have hiM : i ≤ M := by
      rcases hiD with hiF | hitail
      · exact hF hiF
      · rcases hitail with ⟨j, rfl⟩
        have hb0_le : b 0 ≤ b j := hb.monotone (Nat.zero_le j)
        have hbj_le_n : b j ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hirange)
        omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiM), hiD⟩
  · intro i hiM hiN
    exact Nat.zero_le (a i)

lemma succ_range_subset_compl_of_gap {b : ℕ → ℕ}
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1)) :
    Set.range (fun k => b k + 1) ⊆ (Set.range b)ᶜ := by
  have hbmono : StrictMono b := strictMono_of_gap_one hgap
  rintro x ⟨k, rfl⟩ ⟨j, hj⟩
  change b j = b k + 1 at hj
  by_cases hjk : j ≤ k
  · have hbj_le : b j ≤ b k := hbmono.monotone hjk
    omega
  · have hkj : k + 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_not_ge hjk)
    have hble : b (k + 1) ≤ b j := hbmono.monotone hkj
    have hgapk := hgap k
    omega

lemma range_succ_infinite_of_gap {b : ℕ → ℕ}
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1)) :
    (Set.range (fun k => b k + 1)).Infinite := by
  have hbmono : StrictMono b := strictMono_of_gap_one hgap
  refine Set.infinite_range_of_injective ?_
  intro i j hij
  exact hbmono.injective (Nat.succ.inj hij)

lemma coinfinite_range_of_gap {b : ℕ → ℕ}
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1)) :
    (Set.range b)ᶜ.Infinite := by
  exact (range_succ_infinite_of_gap hgap).mono (succ_range_subset_compl_of_gap hgap)

lemma initialTailDeletionSet_infinite
    {F : Set ℕ} {b : ℕ → ℕ}
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1)) :
    (initialTailDeletionSet F b).Infinite := by
  have hbmono : StrictMono b := strictMono_of_gap_one hgap
  exact (range_infinite_of_strictMono_nat hbmono).mono (by
    rintro x ⟨k, rfl⟩
    exact Or.inr ⟨k, rfl⟩)

lemma gap_points_subset_compl_initialTailDeletionSet
    {F : Set ℕ} {b : ℕ → ℕ} {M : ℕ}
    (hF : F ⊆ Set.Iic M)
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1))
    (havoid : ∀ k : ℕ, M < b k) :
    Set.range (fun k => b k + 1) ⊆ (initialTailDeletionSet F b)ᶜ := by
  have hnot_tail := succ_range_subset_compl_of_gap hgap
  rintro x ⟨k, rfl⟩ hx
  rcases hx with hxF | hxTail
  · have hxM : b k + 1 ≤ M := hF hxF
    have hMb : M < b k := havoid k
    omega
  · exact hnot_tail ⟨k, rfl⟩ hxTail

lemma initialTailDeletionSet_coinfinite
    {F : Set ℕ} {b : ℕ → ℕ} {M : ℕ}
    (hF : F ⊆ Set.Iic M)
    (hgap : ∀ k : ℕ, b k + 1 < b (k + 1))
    (havoid : ∀ k : ℕ, M < b k) :
    (initialTailDeletionSet F b)ᶜ.Infinite := by
  exact (range_succ_infinite_of_gap hgap).mono
    (gap_points_subset_compl_initialTailDeletionSet hF hgap havoid)

lemma cover_initialTailDeletionSet_of_cover_initial
    {a : ℕ → ℕ} {F : Set ℕ} {b : ℕ → ℕ} {H M T : ℕ}
    (hcover : CoversInterval a Fᶜ M H T)
    (havoid : ∀ k : ℕ, M < b k) :
    CoversInterval a (initialTailDeletionSet F b)ᶜ M H T := by
  refine CoversInterval.mono_set hcover ?_
  intro i hi
  rcases hi with ⟨hiF, hiM⟩
  constructor
  · intro hdel
    rcases hdel with hF | htail
    · exact hiF hF
    · rcases htail with ⟨k, hk⟩
      have hMi : M < i := by
        simpa [hk] using havoid k
      exact (not_le_of_gt hMi) hiM
  · exact hiM

lemma strictMono_block_left
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    StrictMono b := by
  exact strictMono_nat_of_lt_succ (fun k => by
    have hb := hnonempty k
    have hg := hgap k
    omega)

lemma strictMono_block_right
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    StrictMono e := by
  exact strictMono_nat_of_lt_succ (fun k => by
    have hb := hnonempty (k + 1)
    have hg := hgap k
    omega)

lemma blockDeletionSet_infinite
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    (blockDeletionSet b e).Infinite := by
  have hbmono : StrictMono b := strictMono_block_left hnonempty hgap
  exact (range_infinite_of_strictMono_nat hbmono).mono (by
    rintro x ⟨k, rfl⟩
    exact ⟨k, le_rfl, hnonempty k⟩)

lemma block_gap_points_subset_compl
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    Set.range (fun k => e k + 1) ⊆ (blockDeletionSet b e)ᶜ := by
  have hbmono : StrictMono b := strictMono_block_left hnonempty hgap
  have hemono : StrictMono e := strictMono_block_right hnonempty hgap
  rintro x ⟨k, rfl⟩ ⟨j, hbj, hje⟩
  change b j ≤ e k + 1 at hbj
  change e k + 1 ≤ e j at hje
  by_cases hjk : j ≤ k
  · have hej_le : e j ≤ e k := hemono.monotone hjk
    omega
  · have hkj : k + 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_not_ge hjk)
    have hbk_le : b (k + 1) ≤ b j := hbmono.monotone hkj
    have hg := hgap k
    omega

lemma block_gap_points_infinite
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    (Set.range (fun k => e k + 1)).Infinite := by
  have hemono : StrictMono e := strictMono_block_right hnonempty hgap
  refine Set.infinite_range_of_injective ?_
  intro i j hij
  exact hemono.injective (Nat.succ.inj hij)

lemma blockDeletionSet_coinfinite
    {b e : ℕ → ℕ}
    (hnonempty : ∀ k : ℕ, b k ≤ e k)
    (hgap : ∀ k : ℕ, e k + 1 < b (k + 1)) :
    (blockDeletionSet b e)ᶜ.Infinite := by
  exact (block_gap_points_infinite hnonempty hgap).mono
    (block_gap_points_subset_compl hnonempty hgap)

lemma keptPrefixSum_succ_of_mem {a : ℕ → ℕ} {D : Set ℕ} {n : ℕ}
    (hmem : n + 1 ∈ D) :
    keptPrefixSum a D (n + 1) = keptPrefixSum a D n := by
  classical
  unfold keptPrefixSum
  conv_lhs => rw [Finset.range_add_one, Finset.filter_insert]
  simp [hmem]

lemma keptPrefixSum_succ_of_not_mem {a : ℕ → ℕ} {D : Set ℕ} {n : ℕ}
    (hmem : n + 1 ∉ D) :
    keptPrefixSum a D (n + 1) = keptPrefixSum a D n + a (n + 1) := by
  classical
  unfold keptPrefixSum
  conv_lhs => rw [Finset.range_add_one, Finset.filter_insert]
  simp [hmem, add_comm]

lemma keptPrefixSum_mono {a : ℕ → ℕ} {D : Set ℕ} :
    Monotone (keptPrefixSum a D) := by
  intro m n hmn
  induction hmn with
  | refl =>
      rfl
  | @step n hmn ih =>
      by_cases hdel : n + 1 ∈ D
      · simpa [keptPrefixSum_succ_of_mem hdel] using ih
      · rw [keptPrefixSum_succ_of_not_mem hdel]
        exact le_trans ih (Nat.le_add_right _ _)

lemma keptPrefixSum_add_term_le_of_lt_of_not_mem
    {a : ℕ → ℕ} {D : Set ℕ} {n m : ℕ}
    (hnm : n < m) (hm : m ∉ D) :
    keptPrefixSum a D n + a m ≤ keptPrefixSum a D m := by
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hnp : n ≤ p := Nat.lt_succ_iff.mp hnm
  have hmono := keptPrefixSum_mono (a := a) (D := D) hnp
  rw [keptPrefixSum_succ_of_not_mem hm]
  exact Nat.add_le_add_right hmono _

lemma brown_tail_budget_nonempty_of_initial
    {a : ℕ → ℕ} {D : Set ℕ} {H M T n : ℕ}
    (hMn : M ≤ n)
    (hnonempty : H ≤ T) :
    H ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) := by
  have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
    keptPrefixSum_mono hMn
  omega

lemma brown_tail_budget_propagates_of_two_mul
    {a : ℕ → ℕ} {D : Set ℕ} {H M T n : ℕ}
    (hMn : M ≤ n)
    (hnonempty : H ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M))
    (hkeep : n + 1 ∉ D)
    (hcurrent :
      a (n + 1) ≤
        T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1)
    (htwo : a (n + 2) ≤ 2 * a (n + 1)) :
    a (n + 2) ≤
      T + (keptPrefixSum a D (n + 1) - keptPrefixSum a D M) - H + 1 := by
  have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
    keptPrefixSum_mono hMn
  have htop :
      T + (keptPrefixSum a D n + a (n + 1) - keptPrefixSum a D M) - H + 1 =
        (T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1) +
          a (n + 1) := by
    omega
  rw [keptPrefixSum_succ_of_not_mem hkeep]
  rw [htop]
  calc
    a (n + 2) ≤ 2 * a (n + 1) := htwo
    _ ≤ (T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1) +
          a (n + 1) := by
        omega

lemma brown_tail_budget_unchanged_of_deleted
    {a : ℕ → ℕ} {D : Set ℕ} {H M T n : ℕ}
    (hdel : n + 1 ∈ D) :
    T + (keptPrefixSum a D (n + 1) - keptPrefixSum a D M) - H + 1 =
      T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1 := by
  rw [keptPrefixSum_succ_of_mem hdel]

lemma keptPrefixSum_add_sum_Icc_le_of_not_mem
    {a : ℕ → ℕ} {D : Set ℕ} {M lo hi : ℕ}
    (hMlo : M < lo)
    (hlohi : lo ≤ hi)
    (hkeep : ∀ i : ℕ, lo ≤ i → i ≤ hi → i ∉ D) :
    keptPrefixSum a D M + (∑ i ∈ Finset.Icc lo hi, a i) ≤
      keptPrefixSum a D hi := by
  induction hlohi with
  | refl =>
      have hlo_keep : lo ∉ D := hkeep lo le_rfl le_rfl
      simpa using
        (keptPrefixSum_add_term_le_of_lt_of_not_mem
          (a := a) (D := D) (n := M) (m := lo) hMlo hlo_keep)
  | @step hi hlohi ih =>
      have ih' :
          keptPrefixSum a D M + (∑ i ∈ Finset.Icc lo hi, a i) ≤
            keptPrefixSum a D hi :=
        ih (fun i hli hih => hkeep i hli (le_trans hih (Nat.le_succ hi)))
      have hsucc_keep : hi + 1 ∉ D :=
        hkeep (hi + 1) (Nat.le_succ_of_le hlohi) le_rfl
      have hkept_succ :
          keptPrefixSum a D hi + a (hi + 1) ≤
            keptPrefixSum a D (hi + 1) := by
        rw [keptPrefixSum_succ_of_not_mem hsucc_keep]
      have hsum_succ :
          (∑ i ∈ Finset.Icc lo (hi + 1), a i) =
            (∑ i ∈ Finset.Icc lo hi, a i) + a (hi + 1) :=
        Finset.sum_Icc_succ_top (a := lo) (b := hi)
          (Nat.le_succ_of_le hlohi) a
      rw [hsum_succ]
      calc
        keptPrefixSum a D M +
            ((∑ i ∈ Finset.Icc lo hi, a i) + a (hi + 1))
            = (keptPrefixSum a D M +
                (∑ i ∈ Finset.Icc lo hi, a i)) + a (hi + 1) := by
                omega
        _ ≤ keptPrefixSum a D hi + a (hi + 1) :=
            Nat.add_le_add_right ih' _
        _ ≤ keptPrefixSum a D (hi + 1) := hkept_succ

lemma previousBlockSum_le_brown_tail_budget_of_not_mem
    {a : ℕ → ℕ} {D : Set ℕ} {H M T m n : ℕ}
    (hnonempty : H ≤ T)
    (hmpos : 0 < m)
    (hmn : m ≤ n)
    (hMlo : M < n - m)
    (hkeep : ∀ i : ℕ, n - m ≤ i → i ≤ n - 1 → i ∉ D) :
    previousBlockSum a m n ≤
      T + (keptPrefixSum a D (n - 1) - keptPrefixSum a D M) - H + 1 := by
  have hlohi : n - m ≤ n - 1 := by omega
  have hsumle :
      keptPrefixSum a D M + previousBlockSum a m n ≤
        keptPrefixSum a D (n - 1) := by
    simpa [previousBlockSum] using
      (keptPrefixSum_add_sum_Icc_le_of_not_mem
        (a := a) (D := D) (M := M) (lo := n - m) (hi := n - 1)
        hMlo hlohi hkeep)
  omega

lemma brown_tail_budget_after_deleted_of_previousBlockSurplus
    {a : ℕ → ℕ} {D : Set ℕ} {H M T m d : ℕ}
    (hnonempty : H ≤ T)
    (hmpos : 0 < m)
    (hmd : m ≤ d)
    (hMlo : M < d - m)
    (hkeep : ∀ i : ℕ, d - m ≤ i → i ≤ d - 1 → i ∉ D)
    (hdel : d ∈ D)
    (hsurplus : a (d + 1) < previousBlockSum a m d) :
    a (d + 1) ≤
      T + (keptPrefixSum a D d - keptPrefixSum a D M) - H + 1 := by
  have hdpos : 0 < d := by omega
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  subst d
  have hprev :
      previousBlockSum a m (p + 1) ≤
        T + (keptPrefixSum a D p - keptPrefixSum a D M) - H + 1 :=
    previousBlockSum_le_brown_tail_budget_of_not_mem
      (a := a) (D := D) (H := H) (M := M) (T := T)
      (m := m) (n := p + 1)
      hnonempty hmpos hmd hMlo hkeep
  have hbudget_eq :
      T + (keptPrefixSum a D (p + 1) - keptPrefixSum a D M) - H + 1 =
        T + (keptPrefixSum a D p - keptPrefixSum a D M) - H + 1 :=
    brown_tail_budget_unchanged_of_deleted
      (a := a) (D := D) (H := H) (M := M) (T := T)
      (n := p) hdel
  rw [hbudget_eq]
  exact le_trans (Nat.le_of_lt hsurplus) hprev

lemma periodicDeletion_step_of_fixedBlockSurplus
    {a : ℕ → ℕ} {H M T m : ℕ}
    (hmpos : 0 < m)
    (hnonempty : H ≤ T)
    (hbase : a (M + 1) ≤ T - H + 1)
    (htwo : ∀ n : ℕ, M ≤ n → a (n + 2) ≤ 2 * a (n + 1))
    (hsurplus : FixedLengthBlockSurplusFrom a m (M + m + 1)) :
    ∀ n : ℕ, M ≤ n →
      n + 1 ∉ periodicDeletionSet (M + m + 1) (m + 2) →
        a (n + 1) ≤
          T + (keptPrefixSum a (periodicDeletionSet (M + m + 1) (m + 2)) n -
            keptPrefixSum a (periodicDeletionSet (M + m + 1) (m + 2)) M) - H + 1 := by
  intro n hn
  let D := periodicDeletionSet (M + m + 1) (m + 2)
  change n + 1 ∉ D →
    a (n + 1) ≤
      T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1
  induction hn with
  | refl =>
      intro _hkeep
      simpa using hbase
  | @step n hn ih =>
      intro _hkeepNext
      by_cases hdel : n + 1 ∈ D
      · have hbounds :
            M < (n + 1) - m ∧ m ≤ n + 1 ∧ M + m + 1 ≤ n + 1 :=
          periodicDeletionSet_mem_period_m_add_two_bounds
            (M := M) (m := m) (d := n + 1) hdel
        have hkeepBlock :
            ∀ i : ℕ, (n + 1) - m ≤ i → i ≤ (n + 1) - 1 → i ∉ D := by
          intro i hlo hhi
          exact periodicDeletionSet_not_mem_previousBlock_of_mem_period_m_add_two
            (start := M + m + 1) (m := m) (d := n + 1) (i := i)
            hmpos hdel hbounds.2.1 hlo hhi
        have hsur :
            a ((n + 1) + 1) < previousBlockSum a m (n + 1) :=
          hsurplus (n + 1) hbounds.2.2 hbounds.2.1
        exact brown_tail_budget_after_deleted_of_previousBlockSurplus
          (a := a) (D := D) (H := H) (M := M) (T := T)
          (m := m) (d := n + 1)
          hnonempty hmpos hbounds.2.1 hbounds.1 hkeepBlock hdel hsur
      · have hcurrent :
            a (n + 1) ≤
              T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1 :=
          ih hdel
        have htop_nonempty :
            H ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) :=
          brown_tail_budget_nonempty_of_initial
            (a := a) (D := D) (H := H) (M := M) (T := T)
            hn hnonempty
        exact brown_tail_budget_propagates_of_two_mul
          (a := a) (D := D) (H := H) (M := M) (T := T) (n := n)
          hn htop_nonempty hdel hcurrent (htwo n hn)

lemma exists_keptPrefixSum_ge_of_infinite_compl
    {a : ℕ → ℕ} {D : Set ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hinf : Dᶜ.Infinite) :
    ∀ k start : ℕ, ∃ n : ℕ, start ≤ n ∧ k ≤ keptPrefixSum a D n := by
  intro k
  induction k with
  | zero =>
      intro start
      exact ⟨start, le_rfl, Nat.zero_le _⟩
  | succ k ih =>
      intro start
      rcases ih start with ⟨n, hstartn, hkn⟩
      have hfinite : (Set.Iic n : Set ℕ).Finite := Set.finite_Iic n
      obtain ⟨m, hmkeep, hmnotle⟩ := hinf.exists_notMem_finite hfinite
      have hnm : n < m := Nat.lt_of_not_ge hmnotle
      have hmD : m ∉ D := hmkeep
      have hterm : 1 ≤ a m := hpos m
      have hsum_le :
          keptPrefixSum a D n + a m ≤ keptPrefixSum a D m :=
        keptPrefixSum_add_term_le_of_lt_of_not_mem hnm hmD
      refine ⟨m, le_trans hstartn hnm.le, ?_⟩
      omega

lemma coversInterval_step_of_kept {a : ℕ → ℕ} {D : Set ℕ} {n H T : ℕ}
    (hcover : CoversInterval a Dᶜ n H T)
    (hHT : H ≤ T)
    (hkeep : n + 1 ∉ D)
    (hnext : a (n + 1) ≤ T - H + 1) :
    CoversInterval a Dᶜ (n + 1) H (T + a (n + 1)) := by
  classical
  intro t htH htT
  by_cases ht_old : t ≤ T
  · exact CoversInterval.mono_index hcover (Nat.le_succ n) t htH ht_old
  · have hTlt : T < t := lt_of_not_ge ht_old
    have ha_le_t : a (n + 1) ≤ t := by
      omega
    have hsubH : H ≤ t - a (n + 1) := by
      omega
    have hsubT : t - a (n + 1) ≤ T := by
      omega
    rcases hcover (t - a (n + 1)) hsubH hsubT with ⟨F, hFI, hsum⟩
    have hn1_notin_F : n + 1 ∉ F := by
      intro hn1F
      have hn1_le_n : n + 1 ≤ n := (hFI hn1F).2
      omega
    refine ⟨insert (n + 1) F, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiF
      · exact ⟨hkeep, by simp⟩
      · exact ⟨(hFI hiF).1, le_trans (hFI hiF).2 (Nat.le_succ n)⟩
    · rw [Finset.sum_insert hn1_notin_F]
      omega

/-- Brown-style data guaranteeing that deleting `D` preserves eventual
completeness.  The initial interval `[H, keptPrefixSum M]` is covered, every
kept next term is small enough to extend the covered interval, and the kept
prefix sums are unbounded. -/
structure BrownDeletionData (a : ℕ → ℕ) (D : Set ℕ) (H M : ℕ) : Prop where
  infinite : D.Infinite
  initial_nonempty : H ≤ keptPrefixSum a D M
  initial_cover : CoversInterval a Dᶜ M H (keptPrefixSum a D M)
  step :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      a (n + 1) ≤ keptPrefixSum a D n - H + 1
  unbounded :
    ∀ t : ℕ, H ≤ t → ∃ n : ℕ, M ≤ n ∧ t ≤ keptPrefixSum a D n

/-- Brown-style data before proving unboundedness of the kept prefix sums.
Coinfiniteness of the kept set plus positivity implies the `unbounded` field of
`BrownDeletionData`. -/
structure BrownStepData (a : ℕ → ℕ) (D : Set ℕ) (H M : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  initial_nonempty : H ≤ keptPrefixSum a D M
  initial_cover : CoversInterval a Dᶜ M H (keptPrefixSum a D M)
  step :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      a (n + 1) ≤ keptPrefixSum a D n - H + 1

/-- Brown-style seed data with a fixed initial slack `C`.  This is weaker than
`BrownStepData`: the propagated covered interval is allowed to be
`[H, C + keptPrefixSum n]` rather than `[H, keptPrefixSum n]`. -/
structure BrownSeedData (a : ℕ → ℕ) (D : Set ℕ) (H M C : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  initial_nonempty : H ≤ C + keptPrefixSum a D M
  initial_cover : CoversInterval a Dᶜ M H (C + keptPrefixSum a D M)
  step :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      a (n + 1) ≤ C + keptPrefixSum a D n - H + 1

/-- Brown-style tail data with an explicit initial covered interval `[H, T]`.
The construction only has to avoid deleting the initial prefix.  Lean then
transfers the `Set.univ` prefix cover to `Dᶜ` and propagates the covered upper
endpoint by the kept-prefix growth after `M`. -/
structure BrownTailData (a : ℕ → ℕ) (D : Set ℕ) (H M T : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  avoids_initial : Set.Iic M ⊆ Dᶜ
  initial_nonempty : H ≤ T
  step :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      a (n + 1) ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1

/-- Brown-style tail data when the initial cover has already been proved in
the kept set.  This removes the `avoids_initial` requirement and is useful for
starting after a finite batch of deletions. -/
structure BrownTailCoverData (a : ℕ → ℕ) (D : Set ℕ) (H M T : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  initial_nonempty : H ≤ T
  initial_cover : CoversInterval a Dᶜ M H T
  step :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      a (n + 1) ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) - H + 1

/-- A purely numerical sufficient condition for `BrownTailData`.  It controls
the total deleted mass up to `n`, rather than mentioning the kept prefix sum in
the step inequality. -/
structure BrownBudgetData (a : ℕ → ℕ) (D : Set ℕ) (H M T : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  avoids_initial : Set.Iic M ⊆ Dᶜ
  initial_nonempty : H ≤ T
  budget :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      deletedPrefixSum a D n + a (n + 1) ≤
        T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1

/-- Numerical sufficient condition for `BrownTailCoverData`.  Unlike
`BrownBudgetData`, this permits a finite batch of deletions at or before `M`,
provided the initial cover is already in the kept set. -/
structure BrownBudgetCoverData (a : ℕ → ℕ) (D : Set ℕ) (H M T : ℕ) : Prop where
  infinite : D.Infinite
  coinfinite : Dᶜ.Infinite
  initial_nonempty : H ≤ T
  initial_cover : CoversInterval a Dᶜ M H T
  budget :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ D →
      deletedPrefixSum a D n + a (n + 1) + fullPrefixSum a M + H ≤
        T + fullPrefixSum a n + deletedPrefixSum a D M + 1

/-- Indexed sparse-tail data after a finite initial deletion set `F`.  The
initial interval is covered in `Fᶜ`; the indexed tail starts after `M`, so the
initial cover also lives in the full kept set `(F ∪ range b)ᶜ`. -/
structure IndexedBudgetInitialTailData
    (a : ℕ → ℕ) (F : Set ℕ) (b : ℕ → ℕ) (H M T : ℕ) : Prop where
  initial_subset : F ⊆ Set.Iic M
  gap : ∀ k : ℕ, b k + 1 < b (k + 1)
  avoids_initial : ∀ k : ℕ, M < b k
  initial_nonempty : H ≤ T
  initial_cover : CoversInterval a Fᶜ M H T
  budget :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ initialTailDeletionSet F b →
      deletedPrefixSum a (initialTailDeletionSet F b) n + a (n + 1) +
          fullPrefixSum a M + H ≤
        T + fullPrefixSum a n +
          deletedPrefixSum a (initialTailDeletionSet F b) M + 1

/-- Constructive version of `IndexedBudgetInitialTailData`.  It only asks for
the budget inequality before the first tail deletion and between consecutive
tail deletions. -/
structure IndexedPartialBudgetInitialTailData
    (a : ℕ → ℕ) (F : Set ℕ) (b : ℕ → ℕ) (H M T : ℕ) : Prop where
  initial_subset : F ⊆ Set.Iic M
  gap : ∀ k : ℕ, b k + 1 < b (k + 1)
  avoids_initial : ∀ k : ℕ, M < b k
  initial_nonempty : H ≤ T
  initial_cover : CoversInterval a Fᶜ M H T
  budget_before :
    ∀ n : ℕ, M ≤ n → n < b 0 → n + 1 ∉ initialTailDeletionSet F b →
      deletedPrefixSum a (initialTailDeletionSet F b) n + a (n + 1) +
          fullPrefixSum a M + H ≤
        T + fullPrefixSum a n +
          deletedPrefixSum a (initialTailDeletionSet F b) M + 1
  budget_between :
    ∀ k n : ℕ, b k ≤ n → n < b (k + 1) →
      n + 1 ∉ initialTailDeletionSet F b →
        indexedDeletedSum a b (k + 1) + a (n + 1) + fullPrefixSum a M + H ≤
          T + fullPrefixSum a n + 1

/-- Indexed sparse-deletion budget data.  Unlike the discarded block-control
condition below, this asks for the Brown budget inequality itself at the kept
extension steps. -/
structure IndexedBudgetData (a : ℕ → ℕ) (b : ℕ → ℕ) (H M T : ℕ) : Prop where
  gap : ∀ k : ℕ, b k + 1 < b (k + 1)
  avoids_initial : ∀ k : ℕ, M < b k
  initial_nonempty : H ≤ T
  budget :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ Set.range b →
      deletedPrefixSum a (Set.range b) n + a (n + 1) ≤
        T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1

/-- A more constructive form of indexed sparse-deletion budget data.  It only
mentions the finite sum of the first `k` chosen deleted terms on the interval
before the next deletion. -/
structure IndexedPartialBudgetData (a : ℕ → ℕ) (b : ℕ → ℕ) (H M T : ℕ) : Prop where
  gap : ∀ k : ℕ, b k + 1 < b (k + 1)
  avoids_initial : ∀ k : ℕ, M < b k
  initial_nonempty : H ≤ T
  budget_before :
    ∀ n : ℕ, M ≤ n → n < b 0 → n + 1 ∉ Set.range b →
      a (n + 1) ≤ T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1
  budget_between :
    ∀ k n : ℕ, b k ≤ n → n < b (k + 1) → n + 1 ∉ Set.range b →
      indexedDeletedSum a b (k + 1) + a (n + 1) ≤
        T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1

/-- Finite seed data for the remaining recursive sparse-deletion construction.
After `start`, the global pair-prefix surplus handles all later intervals; the
finite interval before `start` is recorded explicitly. -/
structure IndexedPartialBudgetSeed
    (a : ℕ → ℕ) (H M T start : ℕ) : Prop where
  initial_cover : CoversInterval a Set.univ M H T
  initial_nonempty : H ≤ T
  avoids_initial : M < start
  surplus_from :
    ∀ n : ℕ, start ≤ n →
      budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n
  budget_before :
    ∀ n : ℕ, M ≤ n → n < start → n + 1 ≠ start →
      a (n + 1) ≤ T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1

/-- Seed data for the finite-initial-deletion route.  The initial covered
interval is already proved after deleting a finite set `F ⊆ Iic M`; after
`start`, the usual pair-prefix surplus controls the recursive sparse tail. -/
structure IndexedInitialTailSeed
    (a : ℕ → ℕ) (F : Set ℕ) (H M T start : ℕ) : Prop where
  initial_subset : F ⊆ Set.Iic M
  initial_cover : CoversInterval a Fᶜ M H T
  initial_nonempty : H ≤ T
  avoids_initial : M < start
  surplus_from :
    ∀ n : ℕ, start ≤ n →
      budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n
  budget_before :
    ∀ n : ℕ, M ≤ n → n < start → n + 1 ≠ start →
      a (n + 1) + fullPrefixSum a M + H ≤ T + fullPrefixSum a n + 1

theorem indexedPartialBudgetSeed_of_wide_prefix_cover
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hcover : CoversInterval a Set.univ M H T)
    (hHT : H ≤ T)
    (hwide : fullPrefixSum a M + H ≤ T)
    (hMstart : M < start)
    (hnext : ∀ n : ℕ, M ≤ n → a (n + 1) ≤ fullPrefixSum a n + 1)
    (hsurplus0 : ∀ n : ℕ, start ≤ n → a n + a (n + 1) ≤ fullPrefixSum a n) :
    IndexedPartialBudgetSeed a H M T start where
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := hMstart
  surplus_from := by
    intro n hn
    have hbase : budgetBase a H M T = 0 := by
      dsimp [budgetBase]
      omega
    have hsur := hsurplus0 n hn
    omega
  budget_before := by
    intro n hn _hnstart _hne
    have hfullM_le : fullPrefixSum a M ≤ fullPrefixSum a n :=
      fullPrefixSum_mono hn
    have hnextn := hnext n hn
    omega

theorem indexedPartialBudgetSeed_of_prefix_cover_and_tail_surplus
    {a : ℕ → ℕ} {H M T : ℕ}
    (hcover : CoversInterval a Set.univ M H T)
    (hHT : H ≤ T)
    (hsurplus_from :
      ∀ n : ℕ, M + 1 ≤ n →
        budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n) :
    IndexedPartialBudgetSeed a H M T (M + 1) where
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := by omega
  surplus_from := hsurplus_from
  budget_before := by
    intro n hn hnlt hne
    omega

lemma before_budget_of_large_T
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hmono : StrictMono a)
    (hTlarge : H + a start ≤ T) :
    ∀ n : ℕ, M ≤ n → n < start → n + 1 ≠ start →
      a (n + 1) ≤ T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1 := by
  intro n _hn hnstart hne
  have hsucc_le : n + 1 ≤ start := Nat.succ_le_of_lt hnstart
  have hsucc_lt : n + 1 < start := lt_of_le_of_ne hsucc_le hne
  have ha_le : a (n + 1) ≤ a start :=
    hmono.monotone (Nat.le_of_lt hsucc_lt)
  omega

lemma beforeBudgetNeed_ge
    {a : ℕ → ℕ} {H start n : ℕ}
    (hnstart : n < start) :
    H + a (n + 1) ≤ beforeBudgetNeed a H start := by
  unfold beforeBudgetNeed
  exact Finset.le_sup (f := fun n => H + a (n + 1))
    (Finset.mem_range.mpr hnstart)

lemma before_budget_of_T_ge_beforeBudgetNeed
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hT : beforeBudgetNeed a H start ≤ T) :
    ∀ n : ℕ, M ≤ n → n < start → n + 1 ≠ start →
      a (n + 1) ≤ T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1 := by
  intro n hn hnstart _hne
  have hneed : H + a (n + 1) ≤ T :=
    le_trans (beforeBudgetNeed_ge (a := a) (H := H) hnstart) hT
  have hfullM_le : fullPrefixSum a M ≤ fullPrefixSum a n :=
    fullPrefixSum_mono hn
  omega

theorem indexedInitialTailSeed_of_cover_ge_beforeBudgetNeed_and_tail_surplus
    {a : ℕ → ℕ} {F : Set ℕ} {H M T start : ℕ}
    (hF : F ⊆ Set.Iic M)
    (hcover : CoversInterval a Fᶜ M H T)
    (hHT : H ≤ T)
    (hMstart : M < start)
    (hT : beforeBudgetNeed a H start ≤ T)
    (hsurplus_from :
      ∀ n : ℕ, start ≤ n →
        budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n) :
    IndexedInitialTailSeed a F H M T start where
  initial_subset := hF
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := hMstart
  surplus_from := hsurplus_from
  budget_before := by
    intro n hn hnstart _hne
    have hneed : H + a (n + 1) ≤ T :=
      le_trans (beforeBudgetNeed_ge (a := a) (H := H) hnstart) hT
    have hfullM_le : fullPrefixSum a M ≤ fullPrefixSum a n :=
      fullPrefixSum_mono hn
    omega

theorem indexedPartialBudgetSeed_of_large_cover_and_tail_surplus
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hmono : StrictMono a)
    (hcover : CoversInterval a Set.univ M H T)
    (hHT : H ≤ T)
    (hMstart : M < start)
    (hTlarge : H + a start ≤ T)
    (hsurplus_from :
      ∀ n : ℕ, start ≤ n →
        budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n) :
    IndexedPartialBudgetSeed a H M T start where
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := hMstart
  surplus_from := hsurplus_from
  budget_before := before_budget_of_large_T hmono hTlarge

theorem indexedPartialBudgetSeed_of_cover_ge_beforeBudgetNeed_and_tail_surplus
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hcover : CoversInterval a Set.univ M H T)
    (hHT : H ≤ T)
    (hMstart : M < start)
    (hT : beforeBudgetNeed a H start ≤ T)
    (hsurplus_from :
      ∀ n : ℕ, start ≤ n →
        budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n) :
    IndexedPartialBudgetSeed a H M T start where
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := hMstart
  surplus_from := hsurplus_from
  budget_before := before_budget_of_T_ge_beforeBudgetNeed hT

lemma prefix_cover_of_complete_avoiding_singleton_of_lt_next_next
    {a : ℕ → ℕ} {H M T : ℕ}
    (hmono : StrictMono a)
    (hcomplete :
      ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ)
    (hTlt : T < a (M + 2)) :
    CoversInterval a Set.univ M H T := by
  intro t htH htT
  rcases hcomplete t htH with ⟨F, hF, hsum⟩
  refine ⟨F, ?_, hsum⟩
  intro i hi
  constructor
  · simp
  · by_contra hnot
    have hMi : M < i := Nat.lt_of_not_ge hnot
    have hi_ne : i ≠ M + 1 := by
      intro hi_eq
      have havoid := hF hi
      exact havoid (by simp [hi_eq])
    have hM2i : M + 2 ≤ i := by omega
    have haM2_le : a (M + 2) ≤ a i := hmono.monotone hM2i
    have hai_sum : a i ≤ ∑ j ∈ F, a j := finset_term_le_sum_of_mem hi
    omega

lemma exists_prefix_cover_of_finiteDeletionComplete_avoiding_singleton
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hfinite : FiniteDeletionComplete a)
    (M : ℕ) :
    ∃ H : ℕ, ∀ T : ℕ, H ≤ T → T < a (M + 2) →
      CoversInterval a Set.univ M H T := by
  have hcomplete := hfinite ({M + 1} : Set ℕ) (Set.finite_singleton (M + 1))
  rcases hcomplete with ⟨H, hH⟩
  exact ⟨H, fun T _hHT hTlt =>
    prefix_cover_of_complete_avoiding_singleton_of_lt_next_next
      hmono hH hTlt⟩

lemma tail_pair_surplus_of_initial_and_two_step_le
    {a : ℕ → ℕ} {C start : ℕ}
    (hinit : C + a start + a (start + 1) ≤ fullPrefixSum a start)
    (hstep : ∀ n : ℕ, start ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    ∀ n : ℕ, start ≤ n →
      C + a n + a (n + 1) ≤ fullPrefixSum a n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      simpa using hinit
  | succ k ih =>
      have hstepk : a (start + k + 2) ≤ a (start + k) + a (start + k + 1) :=
        hstep (start + k) (Nat.le_add_right start k)
      rw [show start + (k + 1) = (start + k) + 1 by omega, fullPrefixSum_succ]
      simpa [Nat.add_assoc] using (by omega : C + a (start + k + 1) +
        a (start + k + 2) ≤ fullPrefixSum a (start + k) + a (start + k + 1))

theorem indexedPartialBudgetSeed_of_next_next_cover
    {a : ℕ → ℕ} {H M : ℕ}
    (hcover : CoversInterval a Set.univ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hsurplus_from :
      ∀ n : ℕ, M + 2 ≤ n →
        budgetBase a H M (a (M + 2) - 1) + a n + a (n + 1) ≤
          fullPrefixSum a n) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) where
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := by omega
  surplus_from := hsurplus_from
  budget_before := by
    intro n hnM hnstart hne
    have hnM_eq : n = M := by omega
    subst n
    simp only [fullPrefixSum]
    have hdiff : (∑ i ∈ Finset.range (M + 1), a i) -
        (∑ i ∈ Finset.range (M + 1), a i) = 0 := by omega
    rw [hdiff]
    omega

theorem indexedPartialBudgetSeed_of_next_next_cover_and_two_step_tail
    {a : ℕ → ℕ} {H M : ℕ}
    (hcover : CoversInterval a Set.univ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hinit :
      budgetBase a H M (a (M + 2) - 1) + a (M + 2) + a (M + 3) ≤
        fullPrefixSum a (M + 2))
    (hstep : ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) :=
  indexedPartialBudgetSeed_of_next_next_cover hcover hHT hkeep
    (tail_pair_surplus_of_initial_and_two_step_le hinit hstep)

lemma budgetBase_next_next_initial_surplus_of_pair_and_margin
    {a : ℕ → ℕ} {H M : ℕ}
    (hA2pos : 0 < a (M + 2))
    (hpair : a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2))
    (hmargin : H + a (M + 3) ≤ a (M + 1) + a (M + 2)) :
    budgetBase a H M (a (M + 2) - 1) + a (M + 2) + a (M + 3) ≤
      fullPrefixSum a (M + 2) := by
  rw [show M + 2 = (M + 1) + 1 by omega, fullPrefixSum_succ,
    show M + 1 = M + 1 by rfl, fullPrefixSum_succ] at hpair ⊢
  dsimp [budgetBase]
  have hA2pos' : 0 < a (M + 1 + 1) := by
    simpa [Nat.add_assoc] using hA2pos
  have hpred : a (M + 1 + 1) - 1 + 1 = a (M + 1 + 1) := by
    omega
  have hmargin' : H + a (M + 3) ≤ a (M + 1) + a (M + 1 + 1) := by
    simpa [Nat.add_assoc] using hmargin
  rw [hpred]
  by_cases hle : a (M + 1 + 1) ≤ fullPrefixSum a M + H
  · have hsub :
        fullPrefixSum a M + H - a (M + 1 + 1) + a (M + 1 + 1) =
          fullPrefixSum a M + H :=
      Nat.sub_add_cancel hle
    rw [hsub]
    omega
  · have hlt : fullPrefixSum a M + H < a (M + 1 + 1) := Nat.lt_of_not_ge hle
    have hsub : fullPrefixSum a M + H - a (M + 1 + 1) = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    rw [hsub]
    omega

theorem indexedPartialBudgetSeed_of_next_next_cover_and_margin_tail
    {a : ℕ → ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcover : CoversInterval a Set.univ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hpair : a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2))
    (hmargin : H + a (M + 3) ≤ a (M + 1) + a (M + 2))
    (hstep : ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) :=
  indexedPartialBudgetSeed_of_next_next_cover_and_two_step_tail
    hcover hHT hkeep
    (budgetBase_next_next_initial_surplus_of_pair_and_margin
      (hpos (M + 2)) hpair hmargin)
    hstep

theorem indexedPartialBudgetSeed_of_next_next_cover_and_numeric_conditions
    {a : ℕ → ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcover : CoversInterval a Set.univ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hnum :
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) :=
  indexedPartialBudgetSeed_of_next_next_cover_and_margin_tail
    hpos hcover hHT hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2

theorem indexedInitialTailSeed_of_next_next_cover
    {a : ℕ → ℕ} {F : Set ℕ} {H M : ℕ}
    (hF : F ⊆ Set.Iic M)
    (hcover : CoversInterval a Fᶜ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hsurplus_from :
      ∀ n : ℕ, M + 2 ≤ n →
        budgetBase a H M (a (M + 2) - 1) + a n + a (n + 1) ≤
          fullPrefixSum a n) :
    IndexedInitialTailSeed a F H M (a (M + 2) - 1) (M + 2) where
  initial_subset := hF
  initial_cover := hcover
  initial_nonempty := hHT
  avoids_initial := by omega
  surplus_from := hsurplus_from
  budget_before := by
    intro n hnM hnstart hne
    have hnM_eq : n = M := by omega
    subst n
    omega

theorem indexedInitialTailSeed_of_next_next_cover_and_two_step_tail
    {a : ℕ → ℕ} {F : Set ℕ} {H M : ℕ}
    (hF : F ⊆ Set.Iic M)
    (hcover : CoversInterval a Fᶜ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hinit :
      budgetBase a H M (a (M + 2) - 1) + a (M + 2) + a (M + 3) ≤
        fullPrefixSum a (M + 2))
    (hstep : ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedInitialTailSeed a F H M (a (M + 2) - 1) (M + 2) :=
  indexedInitialTailSeed_of_next_next_cover hF hcover hHT hkeep
    (tail_pair_surplus_of_initial_and_two_step_le hinit hstep)

theorem indexedInitialTailSeed_of_next_next_cover_and_margin_tail
    {a : ℕ → ℕ} {F : Set ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hF : F ⊆ Set.Iic M)
    (hcover : CoversInterval a Fᶜ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hpair : a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2))
    (hmargin : H + a (M + 3) ≤ a (M + 1) + a (M + 2))
    (hstep : ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedInitialTailSeed a F H M (a (M + 2) - 1) (M + 2) :=
  indexedInitialTailSeed_of_next_next_cover_and_two_step_tail
    hF hcover hHT hkeep
    (budgetBase_next_next_initial_surplus_of_pair_and_margin
      (hpos (M + 2)) hpair hmargin)
    hstep

theorem indexedInitialTailSeed_of_next_next_cover_and_numeric_conditions
    {a : ℕ → ℕ} {F : Set ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hF : F ⊆ Set.Iic M)
    (hcover : CoversInterval a Fᶜ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hnum :
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedInitialTailSeed a F H M (a (M + 2) - 1) (M + 2) :=
  indexedInitialTailSeed_of_next_next_cover_and_margin_tail
    hpos hF hcover hHT hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2

lemma prefix_cover_of_complete_avoiding_finite_singleton_of_lt_next_next
    {a : ℕ → ℕ} {F : Set ℕ} {H M T : ℕ}
    (hmono : StrictMono a)
    (hcomplete :
      ∀ t : ℕ, H ≤ t →
        t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hTlt : T < a (M + 2)) :
    CoversInterval a Fᶜ M H T := by
  intro t htH htT
  rcases hcomplete t htH with ⟨G, hG, hsum⟩
  refine ⟨G, ?_, hsum⟩
  intro i hi
  constructor
  · have havoid := hG hi
    exact fun hiF => havoid (Or.inl hiF)
  · by_contra hnot
    have hMi : M < i := Nat.lt_of_not_ge hnot
    have hi_ne : i ≠ M + 1 := by
      intro hi_eq
      have havoid := hG hi
      exact havoid (by simp [hi_eq])
    have hM2i : M + 2 ≤ i := by omega
    have haM2_le : a (M + 2) ≤ a i := hmono.monotone hM2i
    have hai_sum : a i ≤ ∑ j ∈ G, a j := finset_term_le_sum_of_mem hi
    omega

theorem indexedInitialTailSeed_of_finite_singleton_complete_and_numeric_conditions
    {a : ℕ → ℕ} {F : Set ℕ} {H M : ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hF : F ⊆ Set.Iic M)
    (hcomplete :
      ∀ t : ℕ, H ≤ t →
        t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ)
    (hnum :
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedInitialTailSeed a F H M (a (M + 2) - 1) (M + 2) := by
  have hTlt : a (M + 2) - 1 < a (M + 2) := by
    have hA2pos : 0 < a (M + 2) := hpos (M + 2)
    omega
  have hHT : H ≤ a (M + 2) - 1 := by
    have hA1pos : 0 < a (M + 1) := hpos (M + 1)
    have hkeep := hnum.1
    omega
  have hcover :
      CoversInterval a Fᶜ M H (a (M + 2) - 1) :=
    prefix_cover_of_complete_avoiding_finite_singleton_of_lt_next_next
      hmono hcomplete hTlt
  exact indexedInitialTailSeed_of_next_next_cover_and_numeric_conditions
    hpos hF hcover hHT hnum

lemma uniformFinSingletonPrefixCover_of_uniformFinSingletonComplete
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (huniform : UniformFinSingletonComplete a) :
    UniformFinSingletonPrefixCover a := by
  rcases huniform with ⟨F, hFfinite, H, hH⟩
  obtain ⟨B, hB⟩ := finite_subset_iic hFfinite
  have hFevent : ∀ᶠ M in atTop, F ⊆ Set.Iic M := by
    refine eventually_atTop.2 ⟨B, ?_⟩
    intro M hBM i hi
    exact le_trans (hB hi) hBM
  refine ⟨F, hFfinite, H, ?_⟩
  filter_upwards [hFevent, hH] with M hFM hcompleteM
  have hTlt : a (M + 2) - 1 < a (M + 2) := by
    have hA2pos : 0 < a (M + 2) := hpos (M + 2)
    omega
  exact ⟨hFM,
    prefix_cover_of_complete_avoiding_finite_singleton_of_lt_next_next
      hmono hcompleteM hTlt⟩

lemma exists_prefix_cover_avoiding_finite_singleton_of_finiteDeletionComplete
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite) :
    ∀ M : ℕ, ∃ H : ℕ, CoversInterval a Fᶜ M H (a (M + 2) - 1) := by
  intro M
  obtain ⟨H, hH⟩ :=
    finite_singleton_complete_of_finiteDeletionComplete hfinite hFfinite M
  refine ⟨H, ?_⟩
  have hTlt : a (M + 2) - 1 < a (M + 2) := by
    have hA2pos : 0 < a (M + 2) := hpos (M + 2)
    omega
  exact prefix_cover_of_complete_avoiding_finite_singleton_of_lt_next_next
    hmono hH hTlt

lemma eventualFinSingletonSmallPrefixCover_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hprefix : UniformFinSingletonPrefixCover a) :
    EventualFinSingletonSmallPrefixCover a := by
  rcases hprefix with ⟨F, hFfinite, H, hcoverH⟩
  have hnum :
      ∀ᶠ M in atTop,
        H + a (M + 1) ≤ a (M + 2) ∧
          a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
            H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
              ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_numeric_conditions_with_margin
      hmono hpos hratioGap hρ1 hρφ hupper H
  refine ⟨F, hFfinite, ?_⟩
  filter_upwards [hcoverH, hnum] with M hcoverM hnumM
  exact ⟨H, hcoverM.1, hcoverM.2, hnumM.1, hnumM.2.2.1⟩

lemma eventualFinSingletonSmallPrefixCover_of_leastSmall
    {a : ℕ → ℕ}
    (hleast : EventualFinSingletonLeastSmallPrefixCover a) :
    EventualFinSingletonSmallPrefixCover a := by
  rcases hleast with ⟨F, hFfinite, hleastM⟩
  refine ⟨F, hFfinite, ?_⟩
  filter_upwards [hleastM] with M hM
  let H := leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1)
  exact ⟨H, hM.1, leastPrefixCoverThreshold_cover, hM.2.1, hM.2.2⟩

lemma leastSmall_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ}
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    EventualFinSingletonLeastSmallPrefixCover a := by
  rcases hsmall with ⟨F, hFfinite, hsmallM⟩
  refine ⟨F, hFfinite, ?_⟩
  filter_upwards [hsmallM] with M hM
  rcases hM with ⟨H, hFM, hcover, hkeep, hmargin⟩
  have hleast_le :
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) ≤ H :=
    leastPrefixCoverThreshold_le_of_cover hcover
  exact ⟨hFM, by omega, by omega⟩

theorem eventualFinSingletonSmallPrefixCover_iff_leastSmall
    {a : ℕ → ℕ} :
    EventualFinSingletonSmallPrefixCover a ↔
      EventualFinSingletonLeastSmallPrefixCover a :=
  ⟨leastSmall_of_eventualFinSingletonSmallPrefixCover,
    eventualFinSingletonSmallPrefixCover_of_leastSmall⟩

lemma arbLargeFinSingletonSmallPrefixCover_of_eventual
    {a : ℕ → ℕ}
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonSmallPrefixCover a := by
  rcases hsmall with ⟨F, hFfinite, hsmallM⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨B, hB⟩ := eventually_atTop.1 hsmallM
  refine ⟨max N B, le_max_left N B, ?_⟩
  exact hB (max N B) (le_max_right N B)

lemma arbLargeFinSingletonSmallPrefixCover_of_leastLarge
    {a : ℕ → ℕ}
    (hleast : ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonSmallPrefixCover a := by
  rcases hleast with ⟨F, hFfinite, hlarge⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, hM⟩ := hlarge N
  let H := leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1)
  exact ⟨M, hNM, H, hM.1, leastPrefixCoverThreshold_cover, hM.2.1, hM.2.2⟩

lemma leastLarge_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ}
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a := by
  rcases hsmall with ⟨F, hFfinite, hlarge⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, H, hFM, hcover, hkeep, hmargin⟩ := hlarge N
  have hleast_le :
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) ≤ H :=
    leastPrefixCoverThreshold_le_of_cover hcover
  exact ⟨M, hNM, hFM, by omega, by omega⟩

theorem arbLargeFinSingletonSmallPrefixCover_iff_leastLarge
    {a : ℕ → ℕ} :
    ArbitrarilyLargeFinSingletonSmallPrefixCover a ↔
      ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a :=
  ⟨leastLarge_of_arbLargeFinSingletonSmallPrefixCover,
    arbLargeFinSingletonSmallPrefixCover_of_leastLarge⟩

lemma first_seed_keep_iff_leastPrefixCoverThreshold_le_nextSeedMargin
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2)) :
    leastPrefixCoverThreshold a I M (a (M + 2) - 1) + a (M + 1) ≤
        a (M + 2) ↔
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) ≤
        nextSeedMargin a M := by
  dsimp [nextSeedMargin]
  omega

lemma first_prefix_cover_of_first_seed_keep
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2))
    (hkeep :
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) + a (M + 1) ≤
        a (M + 2)) :
    CoversInterval a I M (nextSeedMargin a M) (a (M + 2) - 1) := by
  have hleast_le :
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) ≤
        nextSeedMargin a M :=
    (first_seed_keep_iff_leastPrefixCoverThreshold_le_nextSeedMargin hnext).mp
      hkeep
  exact CoversInterval.mono_lower
    (leastPrefixCoverThreshold_cover (a := a) (I := I) (n := M)
      (T := a (M + 2) - 1))
    hleast_le

lemma first_seed_keep_of_first_prefix_cover
    {a : ℕ → ℕ} {I : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2))
    (hcover : CoversInterval a I M (nextSeedMargin a M) (a (M + 2) - 1)) :
    leastPrefixCoverThreshold a I M (a (M + 2) - 1) + a (M + 1) ≤
      a (M + 2) := by
  have hleast_le :
      leastPrefixCoverThreshold a I M (a (M + 2) - 1) ≤
        nextSeedMargin a M :=
    leastPrefixCoverThreshold_le_of_cover hcover
  exact
    (first_seed_keep_iff_leastPrefixCoverThreshold_le_nextSeedMargin hnext).mpr
      hleast_le

lemma arbLargeFinSingletonFirstPrefixCover_of_firstSmall
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a := by
  rcases hfirst with ⟨F, hFfinite, hfirstF⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, hFM, hkeep⟩ := hfirstF N
  refine ⟨M, hNM, hFM, ?_⟩
  exact first_prefix_cover_of_first_seed_keep
    ((hmono (by omega : M + 1 < M + 2)).le) hkeep

lemma arbLargeFinSingletonFirstSmallPrefixCover_of_firstPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a) :
    ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a := by
  rcases hcover with ⟨F, hFfinite, hcoverF⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, hFM, hcoverM⟩ := hcoverF N
  refine ⟨M, hNM, hFM, ?_⟩
  exact first_seed_keep_of_first_prefix_cover
    ((hmono (by omega : M + 1 < M + 2)).le) hcoverM

theorem arbLargeFinSingletonFirstPrefixCover_iff_firstSmall
    {a : ℕ → ℕ}
    (hmono : StrictMono a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a ↔
      ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a :=
  ⟨arbLargeFinSingletonFirstSmallPrefixCover_of_firstPrefixCover hmono,
    arbLargeFinSingletonFirstPrefixCover_of_firstSmall hmono⟩

lemma eventual_first_prefix_cover_failure_of_not_arbLarge_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
      ∃ N : ℕ, ∀ M : ℕ, N ≤ M → F ⊆ Set.Iic M →
        ¬ CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1) := by
  classical
  by_contra hno
  push Not at hno
  exact hnot hno

lemma evt_prefix_holes_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      nextSeedMargin a M ≤ t ∧ t ≤ a (M + 2) - 1 ∧
        t ∉ prefixSubsetSums a Fᶜ M := by
  obtain ⟨Nbad, hbad⟩ :=
    eventual_first_prefix_cover_failure_of_not_arbLarge_fixedBase
      hnot
  obtain ⟨B, hB⟩ := finite_subset_iic hFfinite
  refine eventually_atTop.2 ⟨max Nbad B, ?_⟩
  intro M hM
  have hNbadM : Nbad ≤ M := by omega
  have hBM : B ≤ M := by omega
  have hFM : F ⊆ Set.Iic M := by
    intro i hi
    exact le_trans (hB hi) hBM
  exact not_coversInterval_iff_exists_prefix_hole.mp
    (hbad M hNbadM hFM)

lemma evt_finite_singleton_holes_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          nextSeedMargin a M ≤ t := by
  have hholes :
      ∀ᶠ M in atTop, ∃ t : ℕ,
        nextSeedMargin a M ≤ t ∧ t ≤ a (M + 2) - 1 ∧
          t ∉ prefixSubsetSums a Fᶜ M :=
    evt_prefix_holes_of_not_arbLargeFirstPrefixCover_fixedBase
      hFfinite hnot
  filter_upwards [hholes] with M hM
  rcases hM with ⟨t, hlow, htT, hmiss⟩
  have hlt : t < a (M + 2) := by
    have hA2pos : 0 < a (M + 2) := hpos (M + 2)
    omega
  exact ⟨t, htT, hlt,
    not_subsetSums_avoiding_finite_singleton_of_prefix_hole hmono hmiss hlt,
    hlow⟩

lemma arbLargeFinSingletonFirstPrefixCover_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a := by
  rcases hsmall with ⟨F, hFfinite, hlarge⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, H, hFM, hcover, hkeep, _hmargin⟩ := hlarge N
  refine ⟨M, hNM, hFM, ?_⟩
  have hleast_le :
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) ≤ H :=
    leastPrefixCoverThreshold_le_of_cover hcover
  have hfirst :
      leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) + a (M + 1) ≤
        a (M + 2) := by
    omega
  exact first_prefix_cover_of_first_seed_keep
    ((hmono (by omega : M + 1 < M + 2)).le) hfirst

lemma arbLargeFinSingletonFirstPrefixCover_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hprefix : UniformFinSingletonPrefixCover a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a := by
  rcases hprefix with ⟨F, hFfinite, H, hcoverH⟩
  have hnextLarge : ∀ᶠ M in atTop, H ≤ nextSeedMargin a M :=
    by
      filter_upwards
        [evt_const_add_next_le_next_next_of_uniformRatioGap
          hmono hpos hgap H] with M hM
      dsimp [nextSeedMargin]
      omega
  have hgood :
      ∀ᶠ M in atTop,
        F ⊆ Set.Iic M ∧
          CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1) := by
    filter_upwards [hcoverH, hnextLarge] with M hcoverM hHM
    exact ⟨hcoverM.1, CoversInterval.mono_lower hcoverM.2 hHM⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨B, hB⟩ := eventually_atTop.1 hgood
  refine ⟨max N B, le_max_left N B, ?_⟩
  exact hB (max N B) (le_max_right N B)

lemma arbLargeFinSingletonFirstPrefixCover_of_firstWindowShiftClosed
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hclosed : ArbitrarilyLargeFinSingletonFirstWindowShiftClosed a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a := by
  rcases hclosed with ⟨F, hFfinite, hlarge⟩
  rcases hfinite F hFfinite with ⟨H, hcompleteF⟩
  have hnextLarge : ∀ᶠ M in atTop, H ≤ nextSeedMargin a M := by
    filter_upwards
      [evt_const_add_next_le_next_next_of_uniformRatioGap
        hmono hpos hgap H] with M hM
    dsimp [nextSeedMargin]
    omega
  obtain ⟨B, hB⟩ := eventually_atTop.1 hnextLarge
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNBM, hFM, hclosedM⟩ := hlarge (max N B)
  have hNM : N ≤ M := by omega
  have hBM : B ≤ M := by omega
  have hHle : H ≤ nextSeedMargin a M := hB M hBM
  have hTlt : a (M + 2) - 1 < a ((M + 1) + 1) := by
    have hposM : 0 < a (M + 2) := hpos (M + 2)
    have hlt0 : a (M + 2) - 1 < a (M + 2) := by omega
    simpa [Nat.add_assoc] using hlt0
  have hcoverH :
      CoversInterval a Fᶜ (M + 1) H (a (M + 2) - 1) :=
    complete_prefix_cover_of_lt_next_on
      (a := a) (I := Fᶜ) (H := H) (n := M + 1)
      (T := a (M + 2) - 1) hmono hcompleteF hTlt
  have hcoverSucc :
      CoversInterval a Fᶜ (M + 1) (nextSeedMargin a M) (a (M + 2) - 1) :=
    CoversInterval.mono_lower hcoverH hHle
  exact ⟨M, hNM, hFM,
    first_prefix_cover_of_succ_cover_and_shiftClosed
      (hpos (M + 2)) hcoverSucc hclosedM⟩

lemma evt_pair_seed_margin_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ M in atTop, a (M + 3) ≤ a (M + 1) + a (M + 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (evt_two_step_le_of_eventual_quotient_lt_rho hpos hρ1 hρφ hupper)
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro M hM
  simpa [Nat.add_assoc] using hN (M + 1) (le_trans hM (Nat.le_succ M))

lemma evt_nextSeedMargin_ge_of_uniformRatioGap
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a) :
    ∀ C : ℕ, ∀ᶠ M in atTop, C ≤ nextSeedMargin a M := by
  intro C
  filter_upwards
    [evt_const_add_next_le_next_next_of_uniformRatioGap
      hmono hpos hgap C] with M hM
  dsimp [nextSeedMargin]
  omega

lemma evt_pairSeedMargin_ge_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ C : ℕ, ∀ᶠ M in atTop, C ≤ pairSeedMargin a M := by
  intro C
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (evt_const_add_two_step_le_of_eventual_quotient_lt_rho
      hmono hpos hρ1 hρφ hupper C)
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro M hM
  have hCM : C + a (M + 3) ≤ a (M + 1) + a (M + 2) := by
    simpa [Nat.add_assoc] using hN (M + 1) (le_trans hM (Nat.le_succ M))
  dsimp [pairSeedMargin]
  omega

lemma evt_prefix_shift_gaps_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ∃ s : ℕ,
      s ∈ prefixSubsetSums a Fᶜ M ∧
        s < nextSeedMargin a M ∧
          a (M + 1) + s < a (M + 2) ∧
            a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  obtain ⟨H, hcompleteF⟩ := hfinite F hFfinite
  have hholes :
      ∀ᶠ M in atTop, ∃ t : ℕ,
        t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
            nextSeedMargin a M ≤ t :=
    evt_finite_singleton_holes_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hFfinite hnot
  have hnextLarge : ∀ᶠ M in atTop, H ≤ nextSeedMargin a M :=
    evt_nextSeedMargin_ge_of_uniformRatioGap hmono hpos hgap H
  filter_upwards [hholes, hnextLarge] with M hhole hnextM
  rcases hhole with ⟨t, _htT, hlt, hmiss, hlow⟩
  have hHt : H ≤ t := le_trans hnextM hlow
  have hshifted :
      a (M + 1) ≤ t ∧ t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M :=
    finite_singleton_hole_mem_base_compl_forces_shifted_prefix
      hmono hcompleteF hHt hmiss hlt
  exact shifted_prefix_hole_gives_prefix_shift_gap
    hshifted.1 hshifted.2 hmiss hlt

lemma evt_not_firstWindowShiftClosed_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ¬ FirstWindowShiftClosed a F M := by
  have hshift :
      ∀ᶠ M in atTop, ∃ s : ℕ,
        s ∈ prefixSubsetSums a Fᶜ M ∧
          s < nextSeedMargin a M ∧
            a (M + 1) + s < a (M + 2) ∧
              a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M :=
    evt_prefix_shift_gaps_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hshift] with M hM hclosed
  rcases hM with ⟨s, hs, hslt, _hshift_lt, hshift_miss⟩
  exact hshift_miss (hclosed s hs hslt)

lemma evt_not_finSingletonCompleteBelowPrev_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ¬ FinSingletonCompleteBelowPrev a F M := by
  have hclosedNot :
      ∀ᶠ M in atTop, ¬ FirstWindowShiftClosed a F M :=
    evt_not_firstWindowShiftClosed_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hclosedNot] with M hnotClosed hbelow
  exact hnotClosed
    (firstWindowShiftClosed_of_finSingletonCompleteBelowPrev hmono hbelow)

lemma evt_prev_lt_finSingletonCompleteThreshold_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop,
      a (M + 1) < finSingletonCompleteThreshold a hfinite hFfinite M := by
  have hnotBelow :
      ∀ᶠ M in atTop, ¬ FinSingletonCompleteBelowPrev a F M :=
    evt_not_finSingletonCompleteBelowPrev_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hnotBelow] with M hnotM
  exact
    (not_finSingletonCompleteBelowPrev_iff_prev_lt_threshold
      hfinite hFfinite).mp hnotM

lemma evt_finSingletonCompleteThreshold_holes_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ∃ t : ℕ, a (M + 1) ≤ t ∧
      t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  have hthreshold :
      ∀ᶠ M in atTop,
        a (M + 1) < finSingletonCompleteThreshold a hfinite hFfinite M :=
    evt_prev_lt_finSingletonCompleteThreshold_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hthreshold] with M hlt
  exact exists_finSingletonCompleteThreshold_hole_of_prev_lt
    hfinite hFfinite hlt

lemma evt_pred_finSingletonCompleteThreshold_holes_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t = finSingletonCompleteThreshold a hfinite hFfinite M - 1 ∧
        a (M + 1) ≤ t ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ := by
  have hthreshold :
      ∀ᶠ M in atTop,
        a (M + 1) < finSingletonCompleteThreshold a hfinite hFfinite M :=
    evt_prev_lt_finSingletonCompleteThreshold_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hthreshold] with M hlt
  exact exists_pred_finSingletonCompleteThreshold_hole_of_prev_lt
    hfinite hFfinite hlt

lemma evt_predThreshold_small_forces_prefix_shift_gap_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop,
      finSingletonCompleteThreshold a hfinite hFfinite M ≤ a (M + 2) →
        ∃ s : ℕ,
          s ∈ prefixSubsetSums a Fᶜ M ∧
            s < nextSeedMargin a M ∧
              a (M + 1) + s < a (M + 2) ∧
                a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  rcases hfinite F hFfinite with ⟨H, hcompleteF⟩
  have hthreshold :
      ∀ᶠ M in atTop,
        a (M + 1) < finSingletonCompleteThreshold a hfinite hFfinite M :=
    evt_prev_lt_finSingletonCompleteThreshold_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  have hHprev : ∀ᶠ M in atTop, H ≤ a (M + 1) := by
    refine eventually_atTop.2 ⟨H, ?_⟩
    intro M hHM
    have hterm := term_ge_succ_of_strictMono_pos hmono hpos (M + 1)
    omega
  filter_upwards [hthreshold, hHprev] with M hprevlt hHM hthreshold_le
  exact
    pred_finSingletonCompleteThreshold_small_forces_prefix_shift_gap
      hfinite hFfinite hmono hcompleteF hHM hprevlt hthreshold_le

lemma evt_threshold_large_or_prefix_shift_gap_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ∀ᶠ M in atTop,
      a (M + 2) < finSingletonCompleteThreshold a hfinite hFfinite M ∨
        ∃ s : ℕ,
          s ∈ prefixSubsetSums a Fᶜ M ∧
            s < nextSeedMargin a M ∧
              a (M + 1) + s < a (M + 2) ∧
                a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  have hcond :
      ∀ᶠ M in atTop,
        finSingletonCompleteThreshold a hfinite hFfinite M ≤ a (M + 2) →
          ∃ s : ℕ,
            s ∈ prefixSubsetSums a Fᶜ M ∧
              s < nextSeedMargin a M ∧
                a (M + 1) + s < a (M + 2) ∧
                  a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M :=
    evt_predThreshold_small_forces_prefix_shift_gap_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot
  filter_upwards [hcond] with M hcondM
  by_cases hle :
      finSingletonCompleteThreshold a hfinite hFfinite M ≤ a (M + 2)
  · exact Or.inr (hcondM hle)
  · exact Or.inl (Nat.lt_of_not_ge hle)

lemma evt_offset_threshold_or_shifted_prefix_of_threshold_escape
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (k : ℕ) (hk : 2 ≤ k)
    (hescape :
      ∀ᶠ M in atTop,
        a (M + k) < finSingletonCompleteThreshold a hfinite hFfinite M) :
    ∀ᶠ M in atTop,
      a (M + k + 1) < finSingletonCompleteThreshold a hfinite hFfinite M ∨
        ∃ t s : ℕ,
          t = finSingletonCompleteThreshold a hfinite hFfinite M - 1 ∧
            a (M + k) ≤ t ∧ t < a (M + k + 1) ∧
              t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
                s = t - a (M + 1) ∧
                  s ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ (M + k) := by
  rcases hfinite F hFfinite with ⟨H, hcompleteF⟩
  have hHoffset : ∀ᶠ M in atTop, H ≤ a (M + k) := by
    refine eventually_atTop.2 ⟨H, ?_⟩
    intro M hHM
    have hterm := term_ge_succ_of_strictMono_pos hmono hpos (M + k)
    omega
  filter_upwards [hescape, hHoffset] with M hoffsetlt hHM
  by_cases hle :
      finSingletonCompleteThreshold a hfinite hFfinite M ≤ a (M + k + 1)
  · exact Or.inr
      (pred_finSingletonCompleteThreshold_next_forces_shifted_prefix
        (R := M + k) hfinite hFfinite hmono hcompleteF
        (by omega) hHM hoffsetlt (by simpa [Nat.add_assoc] using hle))
  · exact Or.inl (Nat.lt_of_not_ge hle)

lemma evt_next3_threshold_or_shifted_prefix_of_threshold_escape
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hescape :
      ∀ᶠ M in atTop,
        a (M + 2) < finSingletonCompleteThreshold a hfinite hFfinite M) :
    ∀ᶠ M in atTop,
      a (M + 3) < finSingletonCompleteThreshold a hfinite hFfinite M ∨
        ∃ t s : ℕ,
          t = finSingletonCompleteThreshold a hfinite hFfinite M - 1 ∧
            a (M + 2) ≤ t ∧ t < a (M + 3) ∧
              t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
                s = t - a (M + 1) ∧
                  s ∈ prefixSubsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ (M + 2) := by
  rcases hfinite F hFfinite with ⟨H, hcompleteF⟩
  have hHnext : ∀ᶠ M in atTop, H ≤ a (M + 2) := by
    refine eventually_atTop.2 ⟨H, ?_⟩
    intro M hHM
    have hterm := term_ge_succ_of_strictMono_pos hmono hpos (M + 2)
    omega
  filter_upwards [hescape, hHnext] with M hnextlt hHM
  by_cases hle :
      finSingletonCompleteThreshold a hfinite hFfinite M ≤ a (M + 3)
  · exact Or.inr
      (pred_finSingletonCompleteThreshold_next3_forces_shifted_prefix
        hfinite hFfinite hmono hcompleteF hHM hnextlt hle)
  · exact Or.inl (Nat.lt_of_not_ge hle)

lemma not_arbLargeFinSingletonCompleteBelowPrev_fixedBase_of_not_arbLargeFirstPrefixCover_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        CoversInterval a Fᶜ M (nextSeedMargin a M) (a (M + 2) - 1)) :
    ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
      FinSingletonCompleteBelowPrev a F M := by
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (evt_not_finSingletonCompleteBelowPrev_of_not_arbLargeFirstPrefixCover_fixedBase
      hmono hpos hgap hfinite hFfinite hnot)
  intro hlargeBelow
  obtain ⟨M, hBM, _hFM, hbelowM⟩ := hlargeBelow B
  exact hB M hBM hbelowM

lemma nextSeedMargin_le_prev_of_two_step_le
    {a : ℕ → ℕ} {M : ℕ}
    (hmono : StrictMono a)
    (htwo : a (M + 2) ≤ a M + a (M + 1)) :
    nextSeedMargin a M ≤ a (M + 1) := by
  have hprev : a M ≤ a (M + 1) := (hmono (Nat.lt_succ_self M)).le
  dsimp [nextSeedMargin]
  omega

lemma evt_nextSeedMargin_le_prev_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∀ᶠ M in atTop, nextSeedMargin a M ≤ a (M + 1) := by
  filter_upwards
    [evt_two_step_le_of_eventual_quotient_lt_rho
      hpos hρ1 hρφ hupper] with M htwo
  exact nextSeedMargin_le_prev_of_two_step_le hmono htwo

lemma arbLargeFinSingletonFirstWindowShiftClosed_of_firstPrefixCover_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a) :
    ArbitrarilyLargeFinSingletonFirstWindowShiftClosed a := by
  rcases hcover with ⟨F, hFfinite, hcoverF⟩
  have hnext :
      ∀ᶠ M in atTop, nextSeedMargin a M ≤ a (M + 1) :=
    evt_nextSeedMargin_le_prev_of_evtQuotientLtGold
      hmono hpos hρ1 hρφ hupper
  obtain ⟨B, hB⟩ := eventually_atTop.1 hnext
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNBM, hFM, hcoverM⟩ := hcoverF (max N B)
  have hNM : N ≤ M := by omega
  have hBM : B ≤ M := by omega
  exact ⟨M, hNM, hFM,
    firstWindowShiftClosed_of_first_prefix_cover_of_nextSeedMargin_le_prev
      (hB M hBM) hcoverM⟩

theorem arbLargeFinSingletonFirstPrefixCover_iff_firstWindowShiftClosed_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a ↔
      ArbitrarilyLargeFinSingletonFirstWindowShiftClosed a :=
  ⟨arbLargeFinSingletonFirstWindowShiftClosed_of_firstPrefixCover_of_evtQuotientLtGold
      hmono hpos hρ1 hρφ hupper,
    arbLargeFinSingletonFirstPrefixCover_of_firstWindowShiftClosed
      hmono hpos hgap hfinite⟩

lemma arbLargeFinSingletonFirstWindowShiftClosed_of_completeBelowPrev
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hbelow : ArbitrarilyLargeFinSingletonCompleteBelowPrev a) :
    ArbitrarilyLargeFinSingletonFirstWindowShiftClosed a := by
  rcases hbelow with ⟨F, hFfinite, hlarge⟩
  refine ⟨F, hFfinite, ?_⟩
  intro N
  obtain ⟨M, hNM, hFM, hbelowM⟩ := hlarge N
  exact ⟨M, hNM, hFM,
    firstWindowShiftClosed_of_finSingletonCompleteBelowPrev hmono hbelowM⟩

lemma arbLargeFinSingletonFirstPrefixCover_of_completeBelowPrev
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hbelow : ArbitrarilyLargeFinSingletonCompleteBelowPrev a) :
    ArbitrarilyLargeFinSingletonFirstPrefixCover a :=
  arbLargeFinSingletonFirstPrefixCover_of_firstWindowShiftClosed
    hmono hpos hgap hfinite
    (arbLargeFinSingletonFirstWindowShiftClosed_of_completeBelowPrev
      hmono hbelow)

lemma not_seed_keep_of_nextSeedMargin_lt_least
    {a : ℕ → ℕ} {F : Set ℕ} {M : ℕ}
    (hnext : a (M + 1) ≤ a (M + 2))
    (hlt :
      nextSeedMargin a M <
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1)) :
    ¬ leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
        a (M + 1) ≤ a (M + 2) := by
  dsimp [nextSeedMargin] at hlt
  omega

lemma evt_finite_singleton_holes_of_eventual_seed_margin_failure
    {a : ℕ → ℕ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hFfinite : F.Finite)
    (hbad :
      ∃ N : ℕ, ∀ M : ℕ, N ≤ M → F ⊆ Set.Iic M →
        ¬ (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 1) ≤ a (M + 2) ∧
            leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 3) ≤ a (M + 1) + a (M + 2)))
    (hnext : ∀ᶠ M in atTop, a (M + 1) ≤ a (M + 2))
    (hpair : ∀ᶠ M in atTop, a (M + 3) ≤ a (M + 1) + a (M + 2)) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) := by
  rcases hbad with ⟨Nbad, hbadM⟩
  obtain ⟨B, hB⟩ := finite_subset_iic hFfinite
  obtain ⟨Nnext, hNnext⟩ := eventually_atTop.1 hnext
  obtain ⟨Npair, hNpair⟩ := eventually_atTop.1 hpair
  refine eventually_atTop.2 ⟨max (max Nbad B) (max Nnext Npair), ?_⟩
  intro M hM
  have hNbadM : Nbad ≤ M := by omega
  have hBM : B ≤ M := by omega
  have hFM : F ⊆ Set.Iic M := by
    intro i hi
    exact le_trans (hB hi) hBM
  have hnot := hbadM M hNbadM hFM
  exact exists_finite_singleton_hole_of_not_seed_margins
    hmono hpos (hNnext M (by omega)) (hNpair M (by omega)) hnot

lemma evt_finite_singleton_holes_of_eventual_seed_margin_failure_of_evtQuotientLtGold
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hbad :
      ∃ N : ℕ, ∀ M : ℕ, N ≤ M → F ⊆ Set.Iic M →
        ¬ (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 1) ≤ a (M + 2) ∧
            leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) :=
  evt_finite_singleton_holes_of_eventual_seed_margin_failure
    hmono hpos hFfinite hbad
    (Filter.Eventually.of_forall fun M =>
      (hmono (by omega : M + 1 < M + 2)).le)
    (evt_pair_seed_margin_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper)

lemma eventual_seed_margin_failure_of_not_arbLargeLeastSmall_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ}
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
      ∃ N : ℕ, ∀ M : ℕ, N ≤ M → F ⊆ Set.Iic M →
        ¬ (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 1) ≤ a (M + 2) ∧
            leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
              a (M + 3) ≤ a (M + 1) + a (M + 2)) := by
  classical
  push Not at hnot
  rcases hnot with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro M hNM hFM hboth
  exact (not_le_of_gt (hN M hNM hFM hboth.1)) hboth.2

lemma evt_finite_singleton_holes_of_not_arbLargeLeastSmall_fixedBase_of_evtQuotientLtGold
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) :=
  evt_finite_singleton_holes_of_eventual_seed_margin_failure_of_evtQuotientLtGold
    hmono hpos hFfinite hρ1 hρφ hupper
    (eventual_seed_margin_failure_of_not_arbLargeLeastSmall_fixedBase hnot)

lemma evt_shifted_prefix_holes_of_not_arbLargeLeastSmall_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop, ∃ t : ℕ,
      t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
        t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
          a (M + 1) ≤ t ∧
            t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M ∧
              (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) := by
  obtain ⟨H, hshift⟩ :=
    finite_singleton_hole_ge_base_threshold_forces_shifted_prefix_of_finiteDeletionComplete
      hmono hfinite hFfinite
  have hholes :
      ∀ᶠ M in atTop, ∃ t : ℕ,
        t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
            (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) :=
    evt_finite_singleton_holes_of_not_arbLargeLeastSmall_fixedBase_of_evtQuotientLtGold
      hmono hpos hFfinite hρ1 hρφ hupper hnot
  have hnextLarge : ∀ᶠ M in atTop, H ≤ nextSeedMargin a M :=
    evt_nextSeedMargin_ge_of_uniformRatioGap hmono hpos hgap H
  have hpairLarge : ∀ᶠ M in atTop, H ≤ pairSeedMargin a M :=
    evt_pairSeedMargin_ge_of_evtQuotientLtGold
      hmono hpos hρ1 hρφ hupper H
  filter_upwards [hholes, hnextLarge, hpairLarge] with M hhole hnextM hpairM
  rcases hhole with ⟨t, htT, hlt, hmiss, hlow⟩
  have hHt : H ≤ t := by
    rcases hlow with hlow | hlow
    · exact le_trans hnextM hlow
    · exact le_trans hpairM hlow
  have hshifted := hshift M t hHt hmiss hlt
  exact ⟨t, htT, hlt, hmiss, hshifted.1, hshifted.2, hlow⟩

lemma evt_prefix_shift_gaps_of_not_arbLargeLeastSmall_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop, ∃ s : ℕ,
      s ∈ prefixSubsetSums a Fᶜ M ∧
        s < nextSeedMargin a M ∧
          a (M + 1) + s < a (M + 2) ∧
            a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M := by
  have hholes :
      ∀ᶠ M in atTop, ∃ t : ℕ,
        t ≤ a (M + 2) - 1 ∧ t < a (M + 2) ∧
          t ∉ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ ∧
            a (M + 1) ≤ t ∧
              t - a (M + 1) ∈ prefixSubsetSums a Fᶜ M ∧
                (nextSeedMargin a M ≤ t ∨ pairSeedMargin a M ≤ t) :=
    evt_shifted_prefix_holes_of_not_arbLargeLeastSmall_fixedBase
      hmono hpos hgap hfinite hFfinite hρ1 hρφ hupper hnot
  filter_upwards [hholes] with M hM
  rcases hM with ⟨t, _htT, hlt, hmiss, ha, hsource, _hlow⟩
  exact shifted_prefix_hole_gives_prefix_shift_gap ha hsource hmiss hlt

lemma evt_nextSeedMargin_lt_least_of_not_arbLargeLeastSmall_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop,
      nextSeedMargin a M <
        leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) := by
  have hshift :
      ∀ᶠ M in atTop, ∃ s : ℕ,
        s ∈ prefixSubsetSums a Fᶜ M ∧
          s < nextSeedMargin a M ∧
            a (M + 1) + s < a (M + 2) ∧
              a (M + 1) + s ∉ prefixSubsetSums a Fᶜ M :=
    evt_prefix_shift_gaps_of_not_arbLargeLeastSmall_fixedBase
      hmono hpos hgap hfinite hFfinite hρ1 hρφ hupper hnot
  have hnext_le :
      ∀ᶠ M in atTop, nextSeedMargin a M ≤ a (M + 1) :=
    evt_nextSeedMargin_le_prev_of_evtQuotientLtGold
      hmono hpos hρ1 hρφ hupper
  filter_upwards [hshift, hnext_le] with M hM hnextM
  rcases hM with ⟨s, hs⟩
  exact prefix_shift_gap_forces_nextSeedMargin_lt_least hnextM hs

lemma evt_not_seed_keep_of_not_arbLargeLeastSmall_fixedBase
    {a : ℕ → ℕ} {F : Set ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hFfinite : F.Finite)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hnot :
      ¬ ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ F ⊆ Set.Iic M ∧
        (leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) ∧
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 3) ≤ a (M + 1) + a (M + 2))) :
    ∀ᶠ M in atTop,
      ¬ leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
          a (M + 1) ≤ a (M + 2) := by
  have hlt :
      ∀ᶠ M in atTop,
        nextSeedMargin a M <
          leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) :=
    evt_nextSeedMargin_lt_least_of_not_arbLargeLeastSmall_fixedBase
      hmono hpos hgap hfinite hFfinite hρ1 hρφ hupper hnot
  filter_upwards [hlt] with M hltM
  exact not_seed_keep_of_nextSeedMargin_lt_least
    ((hmono (by omega : M + 1 < M + 2)).le) hltM

lemma arbLargeLeastSmall_of_firstSmall_of_evtQuotientLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a) :
    ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a := by
  rcases hfirst with ⟨F, hFfinite, hfirstF⟩
  refine ⟨F, hFfinite, ?_⟩
  by_contra hnot
  have hnotKeep :
      ∀ᶠ M in atTop,
        ¬ leastPrefixCoverThreshold a Fᶜ M (a (M + 2) - 1) +
            a (M + 1) ≤ a (M + 2) :=
    evt_not_seed_keep_of_not_arbLargeLeastSmall_fixedBase
      hmono hpos hgap hfinite hFfinite hρ1 hρφ hupper hnot
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnotKeep
  obtain ⟨M, hNM, _hFM, hkeep⟩ := hfirstF N
  exact (hN M hNM) hkeep

theorem indexedPartialBudgetSeed_of_singleton_complete_and_numeric_conditions
    {a : ℕ → ℕ} {H M : ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcomplete :
      ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ)
    (hnum :
      H + a (M + 1) ≤ a (M + 2) ∧
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) := by
  have hTlt : a (M + 2) - 1 < a (M + 2) := by
    have hA2pos : 0 < a (M + 2) := hpos (M + 2)
    omega
  have hHT : H ≤ a (M + 2) - 1 := by
    have hA1pos : 0 < a (M + 1) := hpos (M + 1)
    have hkeep := hnum.1
    omega
  have hcover :
      CoversInterval a Set.univ M H (a (M + 2) - 1) :=
    prefix_cover_of_complete_avoiding_singleton_of_lt_next_next
      hmono hcomplete hTlt
  exact indexedPartialBudgetSeed_of_next_next_cover_and_numeric_conditions
    hpos hcover hHT hnum

theorem exists_indexedPartialBudgetSeed_of_eventual_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) :
    ∃ H M T start : ℕ, IndexedPartialBudgetSeed a H M T start := by
  rcases hsingleton with ⟨H, hH⟩
  have hnum :
      ∀ᶠ M in atTop,
        H + a (M + 1) ≤ a (M + 2) ∧
          a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
            H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
              ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_numeric_conditions_with_margin
      hmono hpos hratioGap hρ1 hρφ hupper H
  have hev :
      ∀ᶠ M in atTop,
        (∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) ∧
          (H + a (M + 1) ≤ a (M + 2) ∧
            a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
              H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
                ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) := by
    filter_upwards [hH, hnum] with M hcomplete hnumM
    exact ⟨hcomplete, hnumM⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨H, M, a (M + 2) - 1, M + 2, ?_⟩
  exact indexedPartialBudgetSeed_of_singleton_complete_and_numeric_conditions
    hmono hpos (hM M le_rfl).1 (hM M le_rfl).2

theorem exists_indexedInitialTailSeed_of_eventual_finite_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hFfinite : F.Finite)
    (hfiniteSingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t →
          t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    ∃ H M T start : ℕ, IndexedInitialTailSeed a F H M T start := by
  rcases hfiniteSingleton with ⟨H, hH⟩
  have hnum :
      ∀ᶠ M in atTop,
        H + a (M + 1) ≤ a (M + 2) ∧
          a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
            H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
              ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_numeric_conditions_with_margin
      hmono hpos hratioGap hρ1 hρφ hupper H
  obtain ⟨B, hB⟩ := finite_subset_iic hFfinite
  have hFevent : ∀ᶠ M in atTop, F ⊆ Set.Iic M := by
    refine eventually_atTop.2 ⟨B, ?_⟩
    intro M hBM i hi
    exact le_trans (hB hi) hBM
  have hev :
      ∀ᶠ M in atTop,
        (F ⊆ Set.Iic M) ∧
          (∀ t : ℕ, H ≤ t →
            t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) ∧
            (H + a (M + 1) ≤ a (M + 2) ∧
              a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
                H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
                  ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) := by
    filter_upwards [hFevent, hH, hnum] with M hFM hcompleteM hnumM
    exact ⟨hFM, hcompleteM, hnumM⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨H, M, a (M + 2) - 1, M + 2, ?_⟩
  exact indexedInitialTailSeed_of_finite_singleton_complete_and_numeric_conditions
    hmono hpos (hM M le_rfl).1 (hM M le_rfl).2.1 (hM M le_rfl).2.2

theorem exists_indexedInitialTailSeed_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hprefix : UniformFinSingletonPrefixCover a) :
    ∃ F : Set ℕ, ∃ H M T start : ℕ, IndexedInitialTailSeed a F H M T start := by
  rcases hprefix with ⟨F, _hFfinite, H, hcoverH⟩
  have hnum :
      ∀ᶠ M in atTop,
        H + a (M + 1) ≤ a (M + 2) ∧
          a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
            H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
              ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_numeric_conditions_with_margin
      hmono hpos hratioGap hρ1 hρφ hupper H
  have hev :
      ∀ᶠ M in atTop,
        (F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H (a (M + 2) - 1)) ∧
          (H + a (M + 1) ≤ a (M + 2) ∧
            a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
              H + a (M + 3) ≤ a (M + 1) + a (M + 2) ∧
                ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) := by
    filter_upwards [hcoverH, hnum] with M hcoverM hnumM
    exact ⟨hcoverM, hnumM⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  have hdata := hM M le_rfl
  have hHT : H ≤ a (M + 2) - 1 := by
    have hA1pos : 0 < a (M + 1) := hpos (M + 1)
    have hkeep := hdata.2.1
    omega
  refine ⟨F, H, M, a (M + 2) - 1, M + 2, ?_⟩
  exact indexedInitialTailSeed_of_next_next_cover_and_numeric_conditions
    hpos hdata.1.1 hdata.1.2 hHT hdata.2

theorem exists_indexedInitialTailSeed_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    ∃ F : Set ℕ, ∃ H M T start : ℕ, IndexedInitialTailSeed a F H M T start := by
  rcases hsmall with ⟨F, _hFfinite, hlarge⟩
  have htail :
      ∀ᶠ M in atTop,
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_tail_conditions_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  obtain ⟨M, hNM, H, hFM, hcover, hkeep, hmargin⟩ := hlarge N
  have htailM := hN M hNM
  have hHT : H ≤ a (M + 2) - 1 := by
    have hA1pos : 0 < a (M + 1) := hpos (M + 1)
    omega
  refine ⟨F, H, M, a (M + 2) - 1, M + 2, ?_⟩
  exact indexedInitialTailSeed_of_next_next_cover_and_numeric_conditions
    hpos hFM hcover hHT ⟨hkeep, htailM.1, hmargin, htailM.2⟩

theorem exists_indexedInitialTailSeed_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    ∃ F : Set ℕ, ∃ H M T start : ℕ, IndexedInitialTailSeed a F H M T start := by
  rcases hsmall with ⟨F, _hFfinite, hsmallM⟩
  have htail :
      ∀ᶠ M in atTop,
        a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
          ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1) :=
    evt_next_next_seed_tail_conditions_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper
  have hev :
      ∀ᶠ M in atTop,
        (∃ H : ℕ,
          F ⊆ Set.Iic M ∧ CoversInterval a Fᶜ M H (a (M + 2) - 1) ∧
            H + a (M + 1) ≤ a (M + 2) ∧
              H + a (M + 3) ≤ a (M + 1) + a (M + 2)) ∧
          (a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2) ∧
            ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) := by
    filter_upwards [hsmallM, htail] with M hsmallAtM htailM
    exact ⟨hsmallAtM, htailM⟩
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  rcases (hM M le_rfl).1 with ⟨H, hFM, hcover, hkeep, hmargin⟩
  have htailM := (hM M le_rfl).2
  have hHT : H ≤ a (M + 2) - 1 := by
    have hA1pos : 0 < a (M + 1) := hpos (M + 1)
    omega
  refine ⟨F, H, M, a (M + 2) - 1, M + 2, ?_⟩
  exact indexedInitialTailSeed_of_next_next_cover_and_numeric_conditions
    hpos hFM hcover hHT ⟨hkeep, htailM.1, hmargin, htailM.2⟩

lemma budgetBase_next_next_eq_zero_of_le
    {a : ℕ → ℕ} {H M : ℕ}
    (hpos : 0 < a (M + 2))
    (hbase : fullPrefixSum a M + H ≤ a (M + 2)) :
    budgetBase a H M (a (M + 2) - 1) = 0 := by
  dsimp [budgetBase]
  omega

theorem indexedPartialBudgetSeed_of_next_next_cover_and_zero_base_tail
    {a : ℕ → ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcover : CoversInterval a Set.univ M H (a (M + 2) - 1))
    (hHT : H ≤ a (M + 2) - 1)
    (hkeep : H + a (M + 1) ≤ a (M + 2))
    (hbase : fullPrefixSum a M + H ≤ a (M + 2))
    (hpair : a (M + 2) + a (M + 3) ≤ fullPrefixSum a (M + 2))
    (hstep : ∀ n : ℕ, M + 2 ≤ n → a (n + 2) ≤ a n + a (n + 1)) :
    IndexedPartialBudgetSeed a H M (a (M + 2) - 1) (M + 2) :=
  indexedPartialBudgetSeed_of_next_next_cover_and_two_step_tail
    hcover hHT hkeep
    (by
      have hbase0 :=
        budgetBase_next_next_eq_zero_of_le (a := a) (H := H) (M := M)
          (hpos (M + 2)) hbase
      simpa [hbase0] using hpair)
    hstep

/-- The explicit finite/tail conditions that are sufficient to produce an
`IndexedPartialBudgetSeed`.  This packages the remaining fixed-point choice:
find a prefix cover whose upper endpoint is large enough for the finite
before-budget, and whose `budgetBase` surplus starts before `start`. -/
structure IndexedPartialBudgetSeedParameters
    (a : ℕ → ℕ) (H M T start : ℕ) : Prop where
  cover : CoversInterval a Set.univ M H T
  nonempty : H ≤ T
  start_after : M < start
  before_bound : beforeBudgetNeed a H start ≤ T
  tail_surplus :
    ∀ n : ℕ, start ≤ n →
      budgetBase a H M T + a n + a (n + 1) ≤ fullPrefixSum a n

theorem indexedPartialBudgetSeed_of_parameters
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hparams : IndexedPartialBudgetSeedParameters a H M T start) :
    IndexedPartialBudgetSeed a H M T start :=
  indexedPartialBudgetSeed_of_cover_ge_beforeBudgetNeed_and_tail_surplus
    hparams.cover hparams.nonempty hparams.start_after hparams.before_bound
    hparams.tail_surplus

lemma indexedPartialBudgetSeedParameters_upper_le_fullPrefixSum
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hparams : IndexedPartialBudgetSeedParameters a H M T start) :
    T ≤ fullPrefixSum a M := by
  have hTmem : T ∈ prefixSubsetSums a Set.univ M :=
    hparams.cover T hparams.nonempty le_rfl
  exact prefixSubsetSum_le_fullPrefixSum hTmem

lemma indexedPartialBudgetSeedParameters_need_le_fullPrefixSum
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hparams : IndexedPartialBudgetSeedParameters a H M T start) :
    beforeBudgetNeed a H start ≤ fullPrefixSum a M := by
  exact le_trans hparams.before_bound
    (indexedPartialBudgetSeedParameters_upper_le_fullPrefixSum hparams)

theorem exists_indexedPartialBudgetData_of_seed
    {a : ℕ → ℕ} {H M T start : ℕ}
    (hmono : StrictMono a)
    (hsurplus :
      ∀ R : ℕ, ∀ᶠ n in atTop, R + a n + a (n + 1) ≤ fullPrefixSum a n)
    (hseed : IndexedPartialBudgetSeed a H M T start) :
    ∃ b : ℕ → ℕ,
      CoversInterval a Set.univ M H T ∧ IndexedPartialBudgetData a b H M T := by
  classical
  let C : ℕ := budgetBase a H M T
  let threshold : ℕ → ℕ :=
    fun R => Classical.choose (eventually_atTop.1 (hsurplus R))
  have hthreshold :
      ∀ R n : ℕ, threshold R ≤ n →
        R + a n + a (n + 1) ≤ fullPrefixSum a n := by
    intro R n hn
    exact Classical.choose_spec (eventually_atTop.1 (hsurplus R)) n hn
  let b : ℕ → ℕ := recursiveBudgetSeq a threshold C start
  have hb0 : b 0 = start := by
    simp [b, recursiveBudgetSeq_zero]
  have hgap : ∀ k : ℕ, b k + 1 < b (k + 1) := by
    intro k
    simpa [b] using recursiveBudgetSeq_gap
      (a := a) (threshold := threshold) (C := C) (start := start) k
  have hbmono : StrictMono b := strictMono_of_gap_one hgap
  have hstart_le : ∀ k : ℕ, start ≤ b k := by
    intro k
    have h0k : 0 ≤ k := Nat.zero_le k
    have hmono := hbmono.monotone h0k
    simpa [hb0] using hmono
  refine ⟨b, hseed.initial_cover, ?_⟩
  refine
    { gap := hgap
      avoids_initial := ?_
      initial_nonempty := hseed.initial_nonempty
      budget_before := ?_
      budget_between := ?_ }
  · intro k
    exact lt_of_lt_of_le hseed.avoids_initial (hstart_le k)
  · intro n hn hnstart hkeep
    have hn_ne_start : n + 1 ≠ start := by
      intro hnext
      have hmem : n + 1 ∈ Set.range b := ⟨0, by simpa [hb0] using hnext.symm⟩
      exact hkeep hmem
    have hbefore := hseed.budget_before n hn hnstart hn_ne_start
    exact hbefore
  · intro k n hbk_le hn_lt_next hkeep
    have hsur :
        C + indexedDeletedSum a b k + a n + a (n + 1) ≤
          fullPrefixSum a n := by
      cases k with
      | zero =>
          have hstartn : start ≤ n := by
            have hb0n : b 0 ≤ n := by simpa using hbk_le
            simpa [hb0] using hb0n
          simpa [C, indexedDeletedSum] using hseed.surplus_from n hstartn
      | succ k =>
          have hbk_threshold :
              threshold (C + indexedDeletedSum a b (k + 1)) ≤ b (k + 1) := by
            simpa [b] using recursiveBudgetSeq_threshold_le_succ
              (a := a) (threshold := threshold) (C := C) (start := start) (k := k)
          have hle_n :
              threshold (C + indexedDeletedSum a b (k + 1)) ≤ n := by
            omega
          exact hthreshold (C + indexedDeletedSum a b (k + 1)) n hle_n
    have hterm_le : a (b k) ≤ a n := by
      exact hmono.monotone hbk_le
    have hsum_le :
        indexedDeletedSum a b (k + 1) ≤ indexedDeletedSum a b k + a n := by
      rw [indexedDeletedSum_succ]
      omega
    have hsur' :
        C + indexedDeletedSum a b (k + 1) + a (n + 1) ≤
          fullPrefixSum a n := by
      omega
    have hmargin : fullPrefixSum a M + H ≤ T + C + 1 := by
      dsimp [C, budgetBase]
      omega
    have hfullM_le : fullPrefixSum a M ≤ fullPrefixSum a n :=
      fullPrefixSum_mono
        (le_trans (le_trans (Nat.le_of_lt hseed.avoids_initial) (hstart_le k)) hbk_le)
    have hfull_split :
        fullPrefixSum a M + (fullPrefixSum a n - fullPrefixSum a M) =
          fullPrefixSum a n := by
      omega
    omega

theorem exists_indexedPartialBudgetInitialTailData_of_seed
    {a : ℕ → ℕ} {F : Set ℕ} {H M T start : ℕ}
    (hmono : StrictMono a)
    (hsurplus :
      ∀ R : ℕ, ∀ᶠ n in atTop, R + a n + a (n + 1) ≤ fullPrefixSum a n)
    (hseed : IndexedInitialTailSeed a F H M T start) :
    ∃ b : ℕ → ℕ, IndexedPartialBudgetInitialTailData a F b H M T := by
  classical
  let C : ℕ := budgetBase a H M T
  let threshold : ℕ → ℕ :=
    fun R => Classical.choose (eventually_atTop.1 (hsurplus R))
  have hthreshold :
      ∀ R n : ℕ, threshold R ≤ n →
        R + a n + a (n + 1) ≤ fullPrefixSum a n := by
    intro R n hn
    exact Classical.choose_spec (eventually_atTop.1 (hsurplus R)) n hn
  let b : ℕ → ℕ := recursiveBudgetSeq a threshold C start
  have hb0 : b 0 = start := by
    simp [b, recursiveBudgetSeq_zero]
  have hgap : ∀ k : ℕ, b k + 1 < b (k + 1) := by
    intro k
    simpa [b] using recursiveBudgetSeq_gap
      (a := a) (threshold := threshold) (C := C) (start := start) k
  have hbmono : StrictMono b := strictMono_of_gap_one hgap
  have hstart_le : ∀ k : ℕ, start ≤ b k := by
    intro k
    have h0k : 0 ≤ k := Nat.zero_le k
    have hmono := hbmono.monotone h0k
    simpa [hb0] using hmono
  refine ⟨b, ?_⟩
  refine
    { initial_subset := hseed.initial_subset
      gap := hgap
      avoids_initial := ?_
      initial_nonempty := hseed.initial_nonempty
      initial_cover := hseed.initial_cover
      budget_before := ?_
      budget_between := ?_ }
  · intro k
    exact lt_of_lt_of_le hseed.avoids_initial (hstart_le k)
  · intro n hn hnstart hkeep
    have hn_ne_start : n + 1 ≠ start := by
      intro hnext
      have hmem : n + 1 ∈ initialTailDeletionSet F b :=
        Or.inr ⟨0, by simpa [hb0] using hnext.symm⟩
      exact hkeep hmem
    have hdel_le :
        deletedPrefixSum a (initialTailDeletionSet F b) n ≤
          deletedPrefixSum a (initialTailDeletionSet F b) M :=
      deletedPrefixSum_initialTail_le_initial_of_lt_first
        (a := a) (b := b) (F := F) (M := M) (n := n)
        hseed.initial_subset hbmono (by simpa [hb0] using hnstart)
    have hbefore := hseed.budget_before n hn hnstart hn_ne_start
    omega
  · intro k n hbk_le hn_lt_next _hkeep
    have hsur :
        C + indexedDeletedSum a b k + a n + a (n + 1) ≤
          fullPrefixSum a n := by
      cases k with
      | zero =>
          have hstartn : start ≤ n := by
            have hb0n : b 0 ≤ n := by simpa using hbk_le
            simpa [hb0] using hb0n
          simpa [C, indexedDeletedSum] using hseed.surplus_from n hstartn
      | succ k =>
          have hbk_threshold :
              threshold (C + indexedDeletedSum a b (k + 1)) ≤ b (k + 1) := by
            simpa [b] using recursiveBudgetSeq_threshold_le_succ
              (a := a) (threshold := threshold) (C := C) (start := start) (k := k)
          have hle_n :
              threshold (C + indexedDeletedSum a b (k + 1)) ≤ n := by
            omega
          exact hthreshold (C + indexedDeletedSum a b (k + 1)) n hle_n
    have hterm_le : a (b k) ≤ a n := by
      exact hmono.monotone hbk_le
    have hsum_le :
        indexedDeletedSum a b (k + 1) ≤ indexedDeletedSum a b k + a n := by
      rw [indexedDeletedSum_succ]
      omega
    have hsur' :
        C + indexedDeletedSum a b (k + 1) + a (n + 1) ≤
          fullPrefixSum a n := by
      omega
    have hmargin : fullPrefixSum a M + H ≤ T + C + 1 := by
      dsimp [C, budgetBase]
      omega
    omega

lemma indexedBudgetData_of_indexedPartialBudgetData
    {a b : ℕ → ℕ} {H M T : ℕ}
    (hdata : IndexedPartialBudgetData a b H M T) :
    IndexedBudgetData a b H M T where
  gap := hdata.gap
  avoids_initial := hdata.avoids_initial
  initial_nonempty := hdata.initial_nonempty
  budget := by
    intro n hn hkeep
    have hbmono : StrictMono b := strictMono_of_gap_one hdata.gap
    have hlarge : n < b (n + 1) := by
      have hge : b 0 + (n + 1) ≤ b (n + 1) :=
        strictMono_nat_add_le hbmono (n + 1)
      omega
    let K : ℕ := Nat.find (p := fun k => n < b k) ⟨n + 1, hlarge⟩
    have hK : n < b K :=
      Nat.find_spec (p := fun k => n < b k) ⟨n + 1, hlarge⟩
    by_cases hKzero : K = 0
    · have hK0 : n < b 0 := by
        simpa [hKzero] using hK
      have hdel0 :
          deletedPrefixSum a (Set.range b) n ≤ indexedDeletedSum a b 0 :=
        deletedPrefixSum_range_le_indexedDeletedSum_of_lt hbmono hK0
      have hbefore := hdata.budget_before n hn hK0 hkeep
      simp [indexedDeletedSum] at hdel0
      omega
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hKzero
      have hk_lt_K : k < K := by omega
      have hnot_prev : ¬ n < b k :=
        Nat.find_min (p := fun j => n < b j) ⟨n + 1, hlarge⟩
          hk_lt_K
      have hbk_le : b k ≤ n := Nat.le_of_not_gt hnot_prev
      have hKsucc : n < b (k + 1) := by
        simpa [hk] using hK
      have hdel :
          deletedPrefixSum a (Set.range b) n ≤ indexedDeletedSum a b (k + 1) :=
        deletedPrefixSum_range_le_indexedDeletedSum_of_lt hbmono hKsucc
      have hbetween := hdata.budget_between k n hbk_le hKsucc hkeep
      omega

lemma indexedBudgetInitialTailData_of_indexedPartialBudgetInitialTailData
    {a b : ℕ → ℕ} {F : Set ℕ} {H M T : ℕ}
    (hdata : IndexedPartialBudgetInitialTailData a F b H M T) :
    IndexedBudgetInitialTailData a F b H M T where
  initial_subset := hdata.initial_subset
  gap := hdata.gap
  avoids_initial := hdata.avoids_initial
  initial_nonempty := hdata.initial_nonempty
  initial_cover := hdata.initial_cover
  budget := by
    intro n hn hkeep
    have hbmono : StrictMono b := strictMono_of_gap_one hdata.gap
    have hlarge : n < b (n + 1) := by
      have hge : b 0 + (n + 1) ≤ b (n + 1) :=
        strictMono_nat_add_le hbmono (n + 1)
      omega
    let K : ℕ := Nat.find (p := fun k => n < b k) ⟨n + 1, hlarge⟩
    have hK : n < b K :=
      Nat.find_spec (p := fun k => n < b k) ⟨n + 1, hlarge⟩
    by_cases hKzero : K = 0
    · have hK0 : n < b 0 := by
        simpa [hKzero] using hK
      exact hdata.budget_before n hn hK0 hkeep
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hKzero
      have hk_lt_K : k < K := by omega
      have hnot_prev : ¬ n < b k :=
        Nat.find_min (p := fun j => n < b j) ⟨n + 1, hlarge⟩
          hk_lt_K
      have hbk_le : b k ≤ n := Nat.le_of_not_gt hnot_prev
      have hKsucc : n < b (k + 1) := by
        simpa [hk] using hK
      have hdel :
          deletedPrefixSum a (initialTailDeletionSet F b) n ≤
            deletedPrefixSum a (initialTailDeletionSet F b) M +
              indexedDeletedSum a b (k + 1) :=
        deletedPrefixSum_initialTail_le_initial_add_indexedDeletedSum_of_lt
          (a := a) (b := b) (F := F) (M := M) (n := n) (k := k + 1)
          hdata.initial_subset hbmono hKsucc
      have hbetween := hdata.budget_between k n hbk_le hKsucc hkeep
      omega

lemma brownBudgetData_of_indexedBudgetData
    {a b : ℕ → ℕ} {H M T : ℕ}
    (hdata : IndexedBudgetData a b H M T) :
    BrownBudgetData a (Set.range b) H M T where
  infinite := range_infinite_of_strictMono_nat (strictMono_of_gap_one hdata.gap)
  coinfinite := coinfinite_range_of_gap hdata.gap
  avoids_initial := by
    intro i hi hmem
    change i ≤ M at hi
    rcases hmem with ⟨k, hk⟩
    have hMi : M < i := by
      simpa [hk] using hdata.avoids_initial k
    omega
  initial_nonempty := hdata.initial_nonempty
  budget := hdata.budget

lemma brownBudgetCoverData_of_indexedBudgetInitialTailData
    {a b : ℕ → ℕ} {F : Set ℕ} {H M T : ℕ}
    (hdata : IndexedBudgetInitialTailData a F b H M T) :
    BrownBudgetCoverData a (initialTailDeletionSet F b) H M T where
  infinite := initialTailDeletionSet_infinite hdata.gap
  coinfinite := initialTailDeletionSet_coinfinite
    hdata.initial_subset hdata.gap hdata.avoids_initial
  initial_nonempty := hdata.initial_nonempty
  initial_cover := cover_initialTailDeletionSet_of_cover_initial
    hdata.initial_cover hdata.avoids_initial
  budget := hdata.budget

/-- Block version of the remaining deletion-control data.  Blocks allow the
construction to delete a term and wait until the current term is large enough
before the next kept-extension step. -/
structure IndexedBlockControlData
    (a : ℕ → ℕ) (b e : ℕ → ℕ) (H M T C : ℕ) : Prop where
  nonempty : ∀ k : ℕ, b k ≤ e k
  gap : ∀ k : ℕ, e k + 1 < b (k + 1)
  avoids_initial : ∀ k : ℕ, M < b k
  initial_nonempty : H ≤ T
  margin : fullPrefixSum a M + H ≤ T + C + 1
  surplus_from :
    ∀ n : ℕ, M ≤ n → C + a n + a (n + 1) ≤ fullPrefixSum a n
  deleted_bound :
    ∀ n : ℕ, M ≤ n → n + 1 ∉ blockDeletionSet b e →
      deletedPrefixSum a (blockDeletionSet b e) n ≤ a n

lemma deletedPrefixSum_ge_add_of_two_mem
    {a : ℕ → ℕ} {D : Set ℕ} {n i j : ℕ}
    (hi_le : i ≤ n) (hj_le : j ≤ n) (hij : i ≠ j)
    (hiD : i ∈ D) (hjD : j ∈ D) :
    a i + a j ≤ deletedPrefixSum a D n := by
  classical
  unfold deletedPrefixSum
  let s := (Finset.range (n + 1)).filter (fun x => x ∈ D)
  have hi_mem : i ∈ s := by
    simp [s, hi_le, hiD]
  have hj_mem : j ∈ s := by
    simp [s, hj_le, hjD]
  have hsubset : ({i, j} : Finset ℕ) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi_mem
    · exact hj_mem
  have hsum_le :
      (∑ x ∈ ({i, j} : Finset ℕ), a x) ≤ ∑ x ∈ s, a x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx_s hx_pair
      exact Nat.zero_le (a x))
  have hpair : (∑ x ∈ ({i, j} : Finset ℕ), a x) = a i + a j := by
    simp [hij]
  simpa [s, hpair] using hsum_le

/-- The earlier block-control condition is too strong: at the end of the
second deleted block the deleted prefix already contains a positive earlier
deleted term plus the current block endpoint. -/
theorem not_indexedBlockControlData_of_pos
    {a b e : ℕ → ℕ} {H M T C : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n) :
    ¬ IndexedBlockControlData a b e H M T C := by
  intro hdata
  have hb0e0 : b 0 ≤ e 0 := hdata.nonempty 0
  have hb1e1 : b 1 ≤ e 1 := hdata.nonempty 1
  have hgap0 : e 0 + 1 < b 1 := hdata.gap 0
  have hb0_lt_e1 : b 0 < e 1 := by omega
  have hM_e1 : M ≤ e 1 := by
    have hMb1 : M < b 1 := hdata.avoids_initial 1
    omega
  have hkeep : e 1 + 1 ∉ blockDeletionSet b e :=
    (block_gap_points_subset_compl hdata.nonempty hdata.gap) ⟨1, rfl⟩
  have hbound :
      deletedPrefixSum a (blockDeletionSet b e) (e 1) ≤ a (e 1) :=
    hdata.deleted_bound (e 1) hM_e1 hkeep
  have hb0mem : b 0 ∈ blockDeletionSet b e :=
    ⟨0, le_rfl, hb0e0⟩
  have he1mem : e 1 ∈ blockDeletionSet b e :=
    ⟨1, hb1e1, le_rfl⟩
  have hge :
      a (b 0) + a (e 1) ≤
        deletedPrefixSum a (blockDeletionSet b e) (e 1) :=
    deletedPrefixSum_ge_add_of_two_mem
      (a := a) (D := blockDeletionSet b e) (n := e 1)
      (i := b 0) (j := e 1)
      (le_of_lt hb0_lt_e1) le_rfl (by omega) hb0mem he1mem
  have hb0pos : 0 < a (b 0) := hpos (b 0)
  omega

lemma brownBudgetData_of_indexedBlockControlData
    {a b e : ℕ → ℕ} {H M T C : ℕ}
    (hdata : IndexedBlockControlData a b e H M T C) :
    BrownBudgetData a (blockDeletionSet b e) H M T where
  infinite := blockDeletionSet_infinite hdata.nonempty hdata.gap
  coinfinite := blockDeletionSet_coinfinite hdata.nonempty hdata.gap
  avoids_initial := by
    intro i hi hmem
    rcases hmem with ⟨k, hbk, hik⟩
    have hMi : M < i := lt_of_lt_of_le (hdata.avoids_initial k) hbk
    have hiM : i ≤ M := hi
    omega
  initial_nonempty := hdata.initial_nonempty
  budget := by
    intro n hn hkeep
    have hfullM_le : fullPrefixSum a M ≤ fullPrefixSum a n :=
      fullPrefixSum_mono hn
    have hdel : deletedPrefixSum a (blockDeletionSet b e) n ≤ a n :=
      hdata.deleted_bound n hn hkeep
    have hsur : C + a n + a (n + 1) ≤ fullPrefixSum a n :=
      hdata.surplus_from n hn
    have hsur_del :
        C + deletedPrefixSum a (blockDeletionSet b e) n + a (n + 1) ≤
          fullPrefixSum a n := by
      omega
    have hmargin : fullPrefixSum a M + H ≤ T + C + 1 := hdata.margin
    have hfull_split :
        fullPrefixSum a M + (fullPrefixSum a n - fullPrefixSum a M) =
          fullPrefixSum a n := by
      omega
    omega

lemma brownTailData_of_brownBudgetData
    {a : ℕ → ℕ} {D : Set ℕ} {H M T : ℕ}
    (hdata : BrownBudgetData a D H M T) :
    BrownTailData a D H M T where
  infinite := hdata.infinite
  coinfinite := hdata.coinfinite
  avoids_initial := hdata.avoids_initial
  initial_nonempty := hdata.initial_nonempty
  step := by
    intro n hn hkeep
    have hdelM : deletedPrefixSum a D M = 0 :=
      deletedPrefixSum_eq_zero_of_avoid hdata.avoids_initial
    have hKM : keptPrefixSum a D M = fullPrefixSum a M := by
      have hsum := keptPrefixSum_add_deletedPrefixSum (a := a) (D := D) (n := M)
      omega
    have hKn :
        keptPrefixSum a D n = fullPrefixSum a n - deletedPrefixSum a D n :=
      keptPrefixSum_eq_fullPrefixSum_sub_deletedPrefixSum
    have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
      keptPrefixSum_mono hn
    have hbudget := hdata.budget n hn hkeep
    omega

lemma brownTailCoverData_of_brownBudgetCoverData
    {a : ℕ → ℕ} {D : Set ℕ} {H M T : ℕ}
    (hdata : BrownBudgetCoverData a D H M T) :
    BrownTailCoverData a D H M T where
  infinite := hdata.infinite
  coinfinite := hdata.coinfinite
  initial_nonempty := hdata.initial_nonempty
  initial_cover := hdata.initial_cover
  step := by
    intro n hn hkeep
    have hsumN :
        keptPrefixSum a D n + deletedPrefixSum a D n = fullPrefixSum a n :=
      keptPrefixSum_add_deletedPrefixSum
    have hsumM :
        keptPrefixSum a D M + deletedPrefixSum a D M = fullPrefixSum a M :=
      keptPrefixSum_add_deletedPrefixSum
    have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
      keptPrefixSum_mono hn
    have hbudget := hdata.budget n hn hkeep
    have hadd :
        a (n + 1) + keptPrefixSum a D M + H ≤
          T + keptPrefixSum a D n + 1 := by
      omega
    omega

lemma brownDeletionData_of_brownStepData
    {a : ℕ → ℕ} {D : Set ℕ} {H M : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : BrownStepData a D H M) :
    BrownDeletionData a D H M where
  infinite := hdata.infinite
  initial_nonempty := hdata.initial_nonempty
  initial_cover := hdata.initial_cover
  step := hdata.step
  unbounded := by
    intro t ht
    exact exists_keptPrefixSum_ge_of_infinite_compl hpos hdata.coinfinite t M

lemma coversInterval_keptPrefixSum_of_brown
    {a : ℕ → ℕ} {D : Set ℕ} {H M n : ℕ}
    (hdata : BrownDeletionData a D H M) (hn : M ≤ n) :
    CoversInterval a Dᶜ n H (keptPrefixSum a D n) ∧
      H ≤ keptPrefixSum a D n := by
  induction hn with
  | refl =>
      exact ⟨hdata.initial_cover, hdata.initial_nonempty⟩
  | @step n hn ih =>
      rcases ih with ⟨hcover, hnonempty⟩
      by_cases hdel : n + 1 ∈ D
      · have hsum : keptPrefixSum a D (n + 1) = keptPrefixSum a D n :=
          keptPrefixSum_succ_of_mem hdel
        constructor
        · rw [hsum]
          exact CoversInterval.mono_index hcover (Nat.le_succ n)
        · simpa [hsum] using hnonempty
      · have hsum : keptPrefixSum a D (n + 1) =
            keptPrefixSum a D n + a (n + 1) :=
          keptPrefixSum_succ_of_not_mem hdel
        constructor
        · rw [hsum]
          exact coversInterval_step_of_kept hcover hnonempty hdel
            (hdata.step n hn hdel)
        · rw [hsum]
          omega

theorem complete_of_brownDeletionData
    {a : ℕ → ℕ} {D : Set ℕ} {H M : ℕ}
    (hdata : BrownDeletionData a D H M) :
    D.Infinite ∧ IsCompleteOn a Dᶜ := by
  refine ⟨hdata.infinite, ⟨H, ?_⟩⟩
  intro t ht
  obtain ⟨n, hnM, htn⟩ := hdata.unbounded t ht
  exact prefixSubsetSums_subset ((coversInterval_keptPrefixSum_of_brown hdata hnM).1 t ht htn)

lemma coversInterval_seedBound_of_brownSeed
    {a : ℕ → ℕ} {D : Set ℕ} {H M C n : ℕ}
    (hdata : BrownSeedData a D H M C) (hn : M ≤ n) :
    CoversInterval a Dᶜ n H (C + keptPrefixSum a D n) ∧
      H ≤ C + keptPrefixSum a D n := by
  induction hn with
  | refl =>
      exact ⟨hdata.initial_cover, hdata.initial_nonempty⟩
  | @step n hn ih =>
      rcases ih with ⟨hcover, hnonempty⟩
      by_cases hdel : n + 1 ∈ D
      · have hsum : keptPrefixSum a D (n + 1) = keptPrefixSum a D n :=
          keptPrefixSum_succ_of_mem hdel
        constructor
        · rw [hsum]
          exact CoversInterval.mono_index hcover (Nat.le_succ n)
        · simpa [hsum] using hnonempty
      · have hsum : keptPrefixSum a D (n + 1) =
            keptPrefixSum a D n + a (n + 1) :=
          keptPrefixSum_succ_of_not_mem hdel
        constructor
        · rw [hsum]
          simpa [Nat.add_assoc] using
            coversInterval_step_of_kept hcover hnonempty hdel
              (hdata.step n hn hdel)
        · rw [hsum]
          omega

theorem complete_of_brownSeedData
    {a : ℕ → ℕ} {D : Set ℕ} {H M C : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : BrownSeedData a D H M C) :
    D.Infinite ∧ IsCompleteOn a Dᶜ := by
  refine ⟨hdata.infinite, ⟨H, ?_⟩⟩
  intro t ht
  obtain ⟨n, hnM, htn⟩ :=
    exists_keptPrefixSum_ge_of_infinite_compl hpos hdata.coinfinite t M
  exact prefixSubsetSums_subset
    ((coversInterval_seedBound_of_brownSeed hdata hnM).1 t ht (by omega))

lemma coversInterval_tailBound_of_brownTail
    {a : ℕ → ℕ} {D : Set ℕ} {H M T n : ℕ}
    (hcover0 : CoversInterval a Set.univ M H T)
    (hdata : BrownTailData a D H M T) (hn : M ≤ n) :
    CoversInterval a Dᶜ n H
        (T + (keptPrefixSum a D n - keptPrefixSum a D M)) ∧
      H ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) := by
  induction hn with
  | refl =>
      have hcoverD : CoversInterval a Dᶜ M H T :=
        cover_compl_of_cover_univ_of_avoid hcover0 hdata.avoids_initial
      constructor
      · simpa using hcoverD
      · simpa using hdata.initial_nonempty
  | @step n hn ih =>
      rcases ih with ⟨hcover, hnonempty⟩
      by_cases hdel : n + 1 ∈ D
      · have hsum : keptPrefixSum a D (n + 1) = keptPrefixSum a D n :=
          keptPrefixSum_succ_of_mem hdel
        constructor
        · rw [hsum]
          exact CoversInterval.mono_index hcover (Nat.le_succ n)
        · simpa [hsum] using hnonempty
      · have hsum : keptPrefixSum a D (n + 1) =
            keptPrefixSum a D n + a (n + 1) :=
          keptPrefixSum_succ_of_not_mem hdel
        have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
          keptPrefixSum_mono hn
        have htop :
            T + (keptPrefixSum a D n + a (n + 1) - keptPrefixSum a D M) =
              T + (keptPrefixSum a D n - keptPrefixSum a D M) + a (n + 1) := by
          omega
        constructor
        · rw [hsum, htop]
          exact coversInterval_step_of_kept hcover hnonempty hdel
            (hdata.step n hn hdel)
        · rw [hsum, htop]
          omega

theorem complete_of_brownTailData
    {a : ℕ → ℕ} {D : Set ℕ} {H M T : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hcover0 : CoversInterval a Set.univ M H T)
    (hdata : BrownTailData a D H M T) :
    D.Infinite ∧ IsCompleteOn a Dᶜ := by
  refine ⟨hdata.infinite, ⟨H, ?_⟩⟩
  intro t ht
  obtain ⟨n, hnM, htn⟩ :=
    exists_keptPrefixSum_ge_of_infinite_compl hpos hdata.coinfinite
      (t + keptPrefixSum a D M) M
  exact prefixSubsetSums_subset
    ((coversInterval_tailBound_of_brownTail hcover0 hdata hnM).1 t ht (by omega))

lemma coversInterval_tailBound_of_brownTailCover
    {a : ℕ → ℕ} {D : Set ℕ} {H M T n : ℕ}
    (hdata : BrownTailCoverData a D H M T) (hn : M ≤ n) :
    CoversInterval a Dᶜ n H
        (T + (keptPrefixSum a D n - keptPrefixSum a D M)) ∧
      H ≤ T + (keptPrefixSum a D n - keptPrefixSum a D M) := by
  induction hn with
  | refl =>
      constructor
      · simpa using hdata.initial_cover
      · simpa using hdata.initial_nonempty
  | @step n hn ih =>
      rcases ih with ⟨hcover, hnonempty⟩
      by_cases hdel : n + 1 ∈ D
      · have hsum : keptPrefixSum a D (n + 1) = keptPrefixSum a D n :=
          keptPrefixSum_succ_of_mem hdel
        constructor
        · rw [hsum]
          exact CoversInterval.mono_index hcover (Nat.le_succ n)
        · simpa [hsum] using hnonempty
      · have hsum : keptPrefixSum a D (n + 1) =
            keptPrefixSum a D n + a (n + 1) :=
          keptPrefixSum_succ_of_not_mem hdel
        have hKMle : keptPrefixSum a D M ≤ keptPrefixSum a D n :=
          keptPrefixSum_mono hn
        have htop :
            T + (keptPrefixSum a D n + a (n + 1) - keptPrefixSum a D M) =
              T + (keptPrefixSum a D n - keptPrefixSum a D M) + a (n + 1) := by
          omega
        constructor
        · rw [hsum, htop]
          exact coversInterval_step_of_kept hcover hnonempty hdel
            (hdata.step n hn hdel)
        · rw [hsum, htop]
          omega

theorem complete_of_brownTailCoverData
    {a : ℕ → ℕ} {D : Set ℕ} {H M T : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : BrownTailCoverData a D H M T) :
    D.Infinite ∧ IsCompleteOn a Dᶜ := by
  refine ⟨hdata.infinite, ⟨H, ?_⟩⟩
  intro t ht
  obtain ⟨n, hnM, htn⟩ :=
    exists_keptPrefixSum_ge_of_infinite_compl hpos hdata.coinfinite
      (t + keptPrefixSum a D M) M
  exact prefixSubsetSums_subset
    ((coversInterval_tailBound_of_brownTailCover hdata hnM).1 t ht (by omega))

theorem complete_of_brownBudgetCoverData
    {a : ℕ → ℕ} {D : Set ℕ} {H M T : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : BrownBudgetCoverData a D H M T) :
    D.Infinite ∧ IsCompleteOn a Dᶜ :=
  complete_of_brownTailCoverData hpos
    (brownTailCoverData_of_brownBudgetCoverData hdata)

theorem complete_of_periodicDeletion_budget
    {a : ℕ → ℕ} {H M T start period : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hperiod : 2 ≤ period)
    (hMstart : M < start)
    (hnonempty : H ≤ T)
    (hcover : CoversInterval a Set.univ M H T)
    (hbudget :
      ∀ n : ℕ, M ≤ n → n + 1 ∉ periodicDeletionSet start period →
        deletedPrefixSum a (periodicDeletionSet start period) n +
            a (n + 1) ≤
          T + (fullPrefixSum a n - fullPrefixSum a M) - H + 1) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  have hperiod_pos : 0 < period := by omega
  have hdata :
      BrownBudgetData a (periodicDeletionSet start period) H M T := by
    refine
      { infinite := ?_
        coinfinite := ?_
        avoids_initial := ?_
        initial_nonempty := hnonempty
        budget := ?_ }
    · exact periodicDeletionSet_infinite (start := start) hperiod_pos
    · exact periodicDeletionSet_coinfinite_of_two_le_period
        (start := start) hperiod
    · exact periodicDeletionSet_avoids_initial
        (M := M) (start := start) (period := period) hMstart
    · intro n hn hkeep
      exact hbudget n hn hkeep
  exact ⟨periodicDeletionSet start period, complete_of_brownTailData hpos hcover
    (brownTailData_of_brownBudgetData hdata)⟩

theorem complete_of_periodicDeletion_step
    {a : ℕ → ℕ} {H M T start period : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hperiod : 2 ≤ period)
    (hMstart : M < start)
    (hnonempty : H ≤ T)
    (hcover : CoversInterval a Set.univ M H T)
    (hstep :
      ∀ n : ℕ, M ≤ n → n + 1 ∉ periodicDeletionSet start period →
        a (n + 1) ≤
          T + (keptPrefixSum a (periodicDeletionSet start period) n -
            keptPrefixSum a (periodicDeletionSet start period) M) - H + 1) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  have hperiod_pos : 0 < period := by omega
  have hdata :
      BrownTailData a (periodicDeletionSet start period) H M T := by
    refine
      { infinite := ?_
        coinfinite := ?_
        avoids_initial := ?_
        initial_nonempty := hnonempty
        step := ?_ }
    · exact periodicDeletionSet_infinite (start := start) hperiod_pos
    · exact periodicDeletionSet_coinfinite_of_two_le_period
        (start := start) hperiod
    · exact periodicDeletionSet_avoids_initial
        (M := M) (start := start) (period := period) hMstart
    · intro n hn hkeep
      exact hstep n hn hkeep
  exact ⟨periodicDeletionSet start period,
    complete_of_brownTailData hpos hcover hdata⟩

theorem complete_of_periodicDeletion_fixedBlockSurplus
    {a : ℕ → ℕ} {H M T m : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hmpos : 0 < m)
    (hnonempty : H ≤ T)
    (hcover : CoversInterval a Set.univ M H T)
    (hbase : a (M + 1) ≤ T - H + 1)
    (htwo : ∀ n : ℕ, M ≤ n → a (n + 2) ≤ 2 * a (n + 1))
    (hsurplus : FixedLengthBlockSurplusFrom a m (M + m + 1)) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  exact complete_of_periodicDeletion_step
    (a := a) (H := H) (M := M) (T := T)
    (start := M + m + 1) (period := m + 2)
    hpos (by omega) (by omega) hnonempty hcover
    (periodicDeletion_step_of_fixedBlockSurplus
      (a := a) (H := H) (M := M) (T := T) (m := m)
      hmpos hnonempty hbase htwo hsurplus)

theorem infCompleteDeletion_of_evtRatioLtGold_of_geometricBlockSurplus
    {a : ℕ → ℕ} {ρ : ℝ} {m : ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hcomplete : IsCompleteOn a Set.univ)
    (hmpos : 0 < m)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hgeom : GeometricBlockSurplus ρ m)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨Nsurplus, hsurplus⟩ :=
    fixedLengthBlockSurplusFrom_of_geometricBlockSurplus_of_eventual_quotient_lt
      (a := a) (ρ := ρ) (m := m)
      hpos (lt_trans Real.zero_lt_one hρ1) hgeom hupper
  have htwo_ev :
      ∀ᶠ n in atTop, a (n + 2) < 2 * a (n + 1) :=
    evt_two_mul_of_eventual_quotient_lt_of_lt_two
      hpos (lt_trans hρφ goldenRatio_lt_two) hupper
  obtain ⟨Ntwo, hNtwo⟩ := eventually_atTop.1 htwo_ev
  let B := max Nsurplus Ntwo
  obtain ⟨H, q, hBq, hnonempty, hcover, hbudget⟩ :=
    exists_initial_global_budget_seed_after_of_complete_of_evtQuotientLtGold
      (a := a) (ρ := ρ)
      hmono hpos hratioGap hcomplete hρ1 hρφ hupper B
  let M := q + 1
  let T := 2 * a (q + 1) - 1
  have hNsurplusM : Nsurplus ≤ M + m + 1 := by
    dsimp [M, B] at *
    omega
  have hsurplusM : FixedLengthBlockSurplusFrom a m (M + m + 1) :=
    hsurplus.mono hNsurplusM
  have hNtwoM : Ntwo ≤ M := by
    dsimp [M, B] at *
    omega
  have htwo :
      ∀ n : ℕ, M ≤ n → a (n + 2) ≤ 2 * a (n + 1) := by
    intro n hn
    exact (hNtwo n (le_trans hNtwoM hn)).le
  have hcoverM : CoversInterval a Set.univ M H T := by
    simpa [M, T] using hcover
  have hbase : a (M + 1) ≤ T - H + 1 := by
    have hTplus : T + 1 = 2 * a (q + 1) := by
      have hOne : 1 ≤ 2 * a (q + 1) := by
        have hp := hpos (q + 1)
        omega
      dsimp [T]
      exact Nat.sub_add_cancel hOne
    have hsub_comm : T - H + 1 = T + 1 - H := by
      omega
    dsimp [M]
    rw [hsub_comm, hTplus]
    simpa [Nat.add_assoc] using hbudget
  exact complete_of_periodicDeletion_fixedBlockSurplus
    (a := a) (H := H) (M := M) (T := T) (m := m)
    hpos hmpos hnonempty hcoverM hbase htwo hsurplusM

theorem complete_of_indexedBudgetInitialTailData
    {a b : ℕ → ℕ} {F : Set ℕ} {H M T : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : IndexedBudgetInitialTailData a F b H M T) :
    (initialTailDeletionSet F b).Infinite ∧
      IsCompleteOn a (initialTailDeletionSet F b)ᶜ :=
  complete_of_brownBudgetCoverData hpos
    (brownBudgetCoverData_of_indexedBudgetInitialTailData hdata)

theorem complete_of_indexedPartialBudgetInitialTailData
    {a b : ℕ → ℕ} {F : Set ℕ} {H M T : ℕ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hdata : IndexedPartialBudgetInitialTailData a F b H M T) :
    (initialTailDeletionSet F b).Infinite ∧
      IsCompleteOn a (initialTailDeletionSet F b)ᶜ :=
  complete_of_indexedBudgetInitialTailData hpos
    (indexedBudgetInitialTailData_of_indexedPartialBudgetInitialTailData hdata)

theorem complete_of_indexedInitialTailSeed
    {a : ℕ → ℕ} {F : Set ℕ} {H M T start : ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hsurplus :
      ∀ R : ℕ, ∀ᶠ n in atTop, R + a n + a (n + 1) ≤ fullPrefixSum a n)
    (hseed : IndexedInitialTailSeed a F H M T start) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨b, hdata⟩ :=
    exists_indexedPartialBudgetInitialTailData_of_seed hmono hsurplus hseed
  exact ⟨initialTailDeletionSet F b,
    complete_of_indexedPartialBudgetInitialTailData hpos hdata⟩

lemma propagated_hole_step {a : ℕ → ℕ} {N m y : ℕ}
    (hmono : StrictMono a)
    (hgap : a m + a (m + 1) < a (m + 2))
    (hnot : y ∉ subsetSums a (Set.Ici N))
    (hylt : y < a m)
    (hsumlt : ∑ i ∈ Finset.Icc N m, a i < y + a (m + 1)) :
    y + a (m + 1) ∉ subsetSums a (Set.Ici N) := by
  classical
  intro hmem
  rcases hmem with ⟨F, hFI, hsum⟩
  have htarget_lt : y + a (m + 1) < a (m + 2) := by
    omega
  have hlt_m2 : ∀ i ∈ F, i < m + 2 := by
    intro i hi
    by_contra hnotlt
    have hm2i : m + 2 ≤ i := Nat.le_of_not_gt hnotlt
    have hm2_ai : a (m + 2) ≤ a i := hmono.monotone hm2i
    have hai_sum : a i ≤ ∑ j ∈ F, a j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
    omega
  by_cases hm1F : m + 1 ∈ F
  · have hEraseSubset : ↑(F.erase (m + 1)) ⊆ Set.Ici N := by
      intro i hi
      exact hFI (Finset.mem_of_mem_erase hi)
    have hEraseSum : ∑ i ∈ F.erase (m + 1), a i = y := by
      have hsplit := Finset.add_sum_erase F a hm1F
      omega
    exact hnot ⟨F.erase (m + 1), hEraseSubset, hEraseSum⟩
  · have hm_le : ∀ i ∈ F, i ≤ m := by
      intro i hi
      have hi_le_m1 : i ≤ m + 1 := Nat.le_of_lt_succ (hlt_m2 i hi)
      have hi_ne_m1 : i ≠ m + 1 := by
        intro h
        exact hm1F (h ▸ hi)
      omega
    have hsum_le :
        ∑ i ∈ F, a i ≤ ∑ i ∈ Finset.Icc N m, a i :=
      finset_sum_le_Icc_sum_of_subset_Ici_of_forall_le hFI hm_le
    omega

lemma propagatedGap_invariants {a : ℕ → ℕ} {N : ℕ}
    (hmono : StrictMono a)
    (hgap : ∀ n : ℕ, N ≤ n → a n + a (n + 1) < a (n + 2))
    (hNgt : 1 < a N) :
    ∀ k : ℕ,
      propagatedGap a N k ∉ subsetSums a (Set.Ici N) ∧
        propagatedGap a N k < a (N + 2 * k) ∧
          (∑ i ∈ Finset.Icc N (N + 2 * k), a i) <
            propagatedGap a N k + a (N + 2 * k + 1) := by
  classical
  intro k
  induction k with
  | zero =>
      have hnot : a N - 1 ∉ subsetSums a (Set.Ici N) := by
        intro hmem
        rcases hmem with ⟨F, hFI, hsum⟩
        by_cases hF : F = ∅
        · simp [hF] at hsum
          omega
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hF
          have hNi : N ≤ i := hFI hi
          have hAi : a N ≤ a i := hmono.monotone hNi
          have hai_sum : a i ≤ ∑ j ∈ F, a j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
          omega
      have hlt : a N - 1 < a (N + 2 * 0) := by
        simp
        omega
      have hsumlt :
          (∑ i ∈ Finset.Icc N (N + 2 * 0), a i) <
            propagatedGap a N 0 + a (N + 2 * 0 + 1) := by
        have hN1 : 1 < a (N + 1) := by
          have hstrict : a N < a (N + 1) := hmono (Nat.lt_succ_self N)
          omega
        simp [propagatedGap]
        omega
      exact ⟨by simpa [propagatedGap] using hnot, hlt, hsumlt⟩
  | succ k ih =>
      rcases ih with ⟨hnot, hylt, hsumlt⟩
      let m := N + 2 * k
      have hm_def : m = N + 2 * k := rfl
      have hNm : N ≤ m := by
        dsimp [m]
        omega
      have hgapm : a m + a (m + 1) < a (m + 2) := hgap m hNm
      have hnot' :
          propagatedGap a N k + a (m + 1) ∉ subsetSums a (Set.Ici N) :=
        propagated_hole_step (a := a) (N := N) (m := m)
          hmono hgapm hnot (by simpa [m] using hylt) (by simpa [m] using hsumlt)
      have hylt' :
          propagatedGap a N k + a (m + 1) < a (m + 2) := by
        have hylt_m : propagatedGap a N k < a m := by
          simpa [m] using hylt
        omega
      have hsum_expand :
          (∑ i ∈ Finset.Icc N (m + 2), a i) =
            (∑ i ∈ Finset.Icc N m, a i) + a (m + 1) + a (m + 2) := by
        have hstep1 :
            (∑ i ∈ Finset.Icc N (m + 1), a i) =
              (∑ i ∈ Finset.Icc N m, a i) + a (m + 1) :=
          Finset.sum_Icc_succ_top (a := N) (b := m) (by omega) a
        have hstep2 :
            (∑ i ∈ Finset.Icc N (m + 2), a i) =
              (∑ i ∈ Finset.Icc N (m + 1), a i) + a (m + 2) :=
          Finset.sum_Icc_succ_top (a := N) (b := m + 1) (by omega) a
        rw [hstep2, hstep1]
      have hsumlt' :
          (∑ i ∈ Finset.Icc N (m + 2), a i) <
            (propagatedGap a N k + a (m + 1)) + a (m + 3) := by
        have hsumlt_m :
            (∑ i ∈ Finset.Icc N m, a i) <
              propagatedGap a N k + a (m + 1) := by
          simpa [m] using hsumlt
        have hgap_next : a (m + 1) + a (m + 2) < a (m + 3) :=
          hgap (m + 1) (by omega)
        rw [hsum_expand]
        omega
      have hsucc_eq :
          propagatedGap a N (k + 1) =
            propagatedGap a N k + a (m + 1) := by
        simp [propagatedGap, m, Nat.add_assoc]
      have hm_next : N + 2 * (k + 1) = m + 2 := by
        dsimp [m]
        omega
      constructor
      · rw [hsucc_eq]
        exact hnot'
      constructor
      · rw [hsucc_eq, hm_next]
        exact hylt'
      · rw [hsucc_eq, hm_next]
        simpa [Nat.add_assoc] using hsumlt'

/-!
## Proved analytic steps

The first theorem below turns `L > φ` into the eventual two-step gap.  The
gap-propagation theorem after it is also proved in Lean.  The lower-bound
`L < φ` side is handled later by the axiom-free global-budget periodic deletion
construction.
-/

/-- If the ratio limit is larger than the golden ratio, then eventually there is
a two-step gap. -/
theorem evt_two_step_gap_of_goldenRatio_lt_limit
    {a : ℕ → ℕ} {L : ℝ}
    (hpos : ∀ n : ℕ, 0 < a n)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hgt : Real.goldenRatio < L) :
    ∀ᶠ n in atTop, a n + a (n + 1) < a (n + 2) := by
  have hq : ∀ᶠ n in atTop, Real.goldenRatio < quotient a n :=
    hlim.eventually (eventually_gt_nhds hgt)
  have hq_succ : ∀ᶠ n in atTop, Real.goldenRatio < quotient a (n + 1) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hq
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    exact hN (n + 1) (le_trans hn (Nat.le_succ n))
  filter_upwards [hq, hq_succ] with n hn hn1
  exact two_step_gap_of_quotient_gt_goldenRatio hpos hn hn1

/-- A tail satisfying the eventual two-step gap cannot be complete. -/
theorem noncomplete_tail_of_evt_two_step_gap
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : ∀ᶠ n in atTop, a n + a (n + 1) < a (n + 2)) :
    ∃ N : ℕ, ¬ IsCompleteOn a (Set.Ici N) := by
  obtain ⟨G, hG⟩ := eventually_atTop.1 hgap
  let N := max G 1
  have hNG : G ≤ N := by
    dsimp [N]
    exact le_max_left G 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hNgt : 1 < a N := by
    have h0pos : 0 < a 0 := hpos 0
    have h0lt : a 0 < a N := hmono hNpos
    omega
  have hgapN : ∀ n : ℕ, N ≤ n → a n + a (n + 1) < a (n + 2) := by
    intro n hn
    exact hG n (le_trans hNG hn)
  refine ⟨N, ?_⟩
  intro hcomplete
  rcases hcomplete with ⟨H, hH⟩
  let y := propagatedGap a N H
  have hy_large : H ≤ y := by
    dsimp [y]
    exact propagatedGap_ge_self hpos H
  have hynot : y ∉ subsetSums a (Set.Ici N) := by
    dsimp [y]
    exact (propagatedGap_invariants hmono hgapN hNgt H).1
  exact hynot (hH y hy_large)

theorem exists_indexedBudgetData_of_eventual_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ) (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) :
    ∃ b : ℕ → ℕ, ∃ H M T : ℕ,
      CoversInterval a Set.univ M H T ∧ IndexedBudgetData a b H M T := by
  obtain ⟨H, M, T, start, hseed⟩ :=
    exists_indexedPartialBudgetSeed_of_eventual_singleton_complete
      hmono hpos hratioGap hρ1 hρφ hupper hsingleton
  obtain ⟨b, hcover, hpartial⟩ :=
    exists_indexedPartialBudgetData_of_seed hmono
      (evt_pair_prefix_surplus_of_evtQuotientLtGold
        hpos hρ1 hρφ hupper)
      hseed
  exact ⟨b, H, M, T, hcover,
    indexedBudgetData_of_indexedPartialBudgetData hpartial⟩

theorem exists_brownBudgetData_of_evtRatioLtGold_of_eventual_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) :
    ∃ D : Set ℕ, ∃ H M T : ℕ,
      CoversInterval a Set.univ M H T ∧ BrownBudgetData a D H M T := by
  obtain ⟨b, H, M, T, hcover, hdata⟩ :=
    exists_indexedBudgetData_of_eventual_singleton_complete
      hmono hpos hratioGap hρ1 hρφ hupper hsingleton
  exact ⟨Set.range b, H, M, T, hcover,
    brownBudgetData_of_indexedBudgetData hdata⟩

/-- The Brown-style sparse deletion data gives the lower-bound deletion
counterexample needed in the main proof. -/
theorem infCompleteDeletion_of_evtRatioLtGold
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hcomplete : IsCompleteOn a Set.univ)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨m, hmpos, hgeom⟩ :=
    exists_geometricBlockSurplus_of_lt_goldenRatio hρ1 hρφ
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_geometricBlockSurplus
      hmono hpos hgap hcomplete hmpos hρ1 hρφ hgeom hupper

theorem infCompleteDeletion_of_evtRatioLtGold_of_eventual_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t → t ∈ subsetSums a ({M + 1} : Set ℕ)ᶜ) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨D, H, M, T, hcover0, hdata⟩ :=
    exists_brownBudgetData_of_evtRatioLtGold_of_eventual_singleton_complete
      hmono hpos hratioGap hρ1 hρφ hupper hsingleton
  exact ⟨D, complete_of_brownTailData hpos hcover0
    (brownTailData_of_brownBudgetData hdata)⟩

theorem infCompleteDeletion_of_evtRatioLtGold_of_eventual_finite_singleton_complete
    {a : ℕ → ℕ} {ρ : ℝ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hFfinite : F.Finite)
    (hfiniteSingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t →
          t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨H, M, T, start, hseed⟩ :=
    exists_indexedInitialTailSeed_of_eventual_finite_singleton_complete
      hmono hpos hratioGap hρ1 hρφ hupper hFfinite hfiniteSingleton
  exact complete_of_indexedInitialTailSeed hmono hpos
    (evt_pair_prefix_surplus_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper)
    hseed

theorem infCompleteDeletion_of_evtRatioLtGold_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hprefix : UniformFinSingletonPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨F, H, M, T, start, hseed⟩ :=
    exists_indexedInitialTailSeed_of_uniformFinSingletonPrefixCover
      hmono hpos hratioGap hρ1 hρφ hupper hprefix
  exact complete_of_indexedInitialTailSeed hmono hpos
    (evt_pair_prefix_surplus_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper)
    hseed

theorem infCompleteDeletion_of_evtRatioLtGold_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨F, H, M, T, start, hseed⟩ :=
    exists_indexedInitialTailSeed_of_eventualFinSingletonSmallPrefixCover
      hpos hρ1 hρφ hupper hsmall
  exact complete_of_indexedInitialTailSeed hmono hpos
    (evt_pair_prefix_surplus_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper)
    hseed

theorem infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  obtain ⟨F, H, M, T, start, hseed⟩ :=
    exists_indexedInitialTailSeed_of_arbLargeFinSingletonSmallPrefixCover
      hpos hρ1 hρφ hupper hsmall
  exact complete_of_indexedInitialTailSeed hmono hpos
    (evt_pair_prefix_surplus_of_evtQuotientLtGold
      hpos hρ1 hρφ hupper)
    hseed

theorem infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  have hleast :
      ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a :=
    arbLargeLeastSmall_of_firstSmall_of_evtQuotientLtGold
      hmono hpos hgap hfinite hρ1 hρφ hupper hfirst
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonSmallPrefixCover
      hmono hpos hρ1 hρφ hupper
      (arbLargeFinSingletonSmallPrefixCover_of_leastLarge hleast)

theorem infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ} {ρ : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hρ1 : 1 < ρ)
    (hρφ : ρ < Real.goldenRatio)
    (hupper : ∀ᶠ n in atTop, quotient a n < ρ)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ :=
  infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonFirstSmallPrefixCover
    hmono hpos hgap hfinite hρ1 hρφ hupper
    (arbLargeFinSingletonFirstSmallPrefixCover_of_firstPrefixCover
      hmono hcover)

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_eventual_finite_singleton_complete
    {a : ℕ → ℕ} {L : ℝ} {F : Set ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hFfinite : F.Finite)
    (hfiniteSingleton :
      ∃ H : ℕ, ∀ᶠ M in atTop,
        ∀ t : ℕ, H ≤ t →
          t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_eventual_finite_singleton_complete
      hmono hpos hratioGap hρ1 hρφ hupper hFfinite hfiniteSingleton

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hprefix : UniformFinSingletonPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_uniformFinSingletonPrefixCover
      hmono hpos hratioGap hρ1 hρφ hupper hprefix

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_eventualFinSingletonSmallPrefixCover
      hmono hpos hρ1 hρφ hupper hsmall

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonSmallPrefixCover
      hmono hpos hρ1 hρφ hupper hsmall

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonFirstSmallPrefixCover
      hmono hpos hgap hfinite hρ1 hρφ hupper hfirst

theorem infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact
    infCompleteDeletion_of_evtRatioLtGold_of_arbLargeFinSingletonFirstPrefixCover
      hmono hpos hgap hfinite hρ1 hρφ hupper hcover

/-- If the ratio limit lies strictly between `1` and `φ`, then one can delete
an infinite, sufficiently sparse set of indices and still remain complete.  The
limit-to-eventual-bound part is proved here; the remaining sparse-deletion
construction is isolated above. -/
theorem infCompleteDeletion_of_limit_lt_goldenRatio
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hcomplete : IsCompleteOn a Set.univ)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hlt : L < Real.goldenRatio) :
    ∃ D : Set ℕ, D.Infinite ∧ IsCompleteOn a Dᶜ := by
  let ρ : ℝ := (L + Real.goldenRatio) / 2
  have hLρ : L < ρ := by
    dsimp [ρ]
    linarith
  have hρφ : ρ < Real.goldenRatio := by
    dsimp [ρ]
    linarith
  have hρ1 : 1 < ρ := by
    dsimp [ρ]
    linarith
  have hupper : ∀ᶠ n in atTop, quotient a n < ρ :=
    hlim.eventually (eventually_lt_nhds hLρ)
  exact infCompleteDeletion_of_evtRatioLtGold
    hmono hpos hgap hcomplete hρ1 hρφ hupper

/-!
## Consequences of the inputs
-/

theorem limit_le_goldenRatio
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L)) :
    L ≤ Real.goldenRatio := by
  by_contra hnot
  have hgt : Real.goldenRatio < L := lt_of_not_ge hnot
  have hgap :
      ∀ᶠ n in atTop, a n + a (n + 1) < a (n + 2) :=
    evt_two_step_gap_of_goldenRatio_lt_limit hpos hlim hgt
  obtain ⟨N, hbad⟩ := noncomplete_tail_of_evt_two_step_gap hmono hpos hgap
  exact hbad (tail_complete_of_finiteDeletionComplete hfinite N)

theorem goldenRatio_le_limit_of_eventual_finite_singleton_complete
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hfiniteSingleton :
      ∃ F : Set ℕ, F.Finite ∧
        ∃ H : ℕ, ∀ᶠ M in atTop,
          ∀ t : ℕ, H ≤ t →
            t ∈ subsetSums a (F ∪ ({M + 1} : Set ℕ))ᶜ) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  rcases hfiniteSingleton with ⟨F, hFfinite, hFS⟩
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_eventual_finite_singleton_complete
      hmono hpos hratioGap hlim hL1 hlt hFfinite hFS
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hprefix : UniformFinSingletonPrefixCover a) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_uniformFinSingletonPrefixCover
      hmono hpos hratioGap hlim hL1 hlt hprefix
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hsmall : EventualFinSingletonSmallPrefixCover a) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_eventualFinSingletonSmallPrefixCover
      hmono hpos hlim hL1 hlt hsmall
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonSmallPrefixCover
      hmono hpos hlim hL1 hlt hsmall
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonFirstSmallPrefixCover
      hmono hpos hgap hfinite hlim hL1 hlt hfirst
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio_of_arbLargeFinSingletonFirstPrefixCover
      hmono hpos hgap hfinite hlim hL1 hlt hcover
  exact (hinfinite D hDinf) hDcomplete

theorem goldenRatio_le_limit_of_uniformFinSingletonComplete
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L)
    (huniform : UniformFinSingletonComplete a) :
    Real.goldenRatio ≤ L :=
  goldenRatio_le_limit_of_eventual_finite_singleton_complete
    hmono hpos hratioGap hinfinite hlim hL1 huniform

theorem goldenRatio_le_limit
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Real.goldenRatio ≤ L := by
  by_contra hnot
  have hlt : L < Real.goldenRatio := lt_of_not_ge hnot
  obtain ⟨D, hDinf, hDcomplete⟩ :=
    infCompleteDeletion_of_limit_lt_goldenRatio
      hmono hpos hratioGap (complete_univ_of_finiteDeletionComplete hfinite)
      hlim hL1 hlt
  exact (hinfinite D hDinf) hDcomplete

/-- Conditional value theorem for the interpretation where the ratio limit is
assumed to exist and to be greater than one. -/
theorem ratio_limit_eq_goldenRatio
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit hmono hpos hratioGap hfinite hinfinite hlim hL1)

/-- Legacy conditional value theorem under the explicit uniform finite-base
singleton completeness condition.  The main theorem no longer needs this route,
but it remains as a named sufficient condition for the older singleton-threshold
approach. -/
theorem ratio_limit_eq_goldenRatio_of_uniformFinSingletonComplete
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (huniform : UniformFinSingletonComplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_uniformFinSingletonComplete
      hmono hpos hratioGap hinfinite hlim hL1 huniform)

/-- A fully proved variant of the value theorem under the weaker uniform prefix
cover condition used by the finite-initial-tail seed. -/
theorem ratio_limit_eq_goldenRatio_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hprefix : UniformFinSingletonPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_uniformFinSingletonPrefixCover
      hmono hpos hratioGap hinfinite hlim hL1 hprefix)

/-- Value theorem under the small, `M`-dependent prefix-cover window condition.
This is weaker than the uniform prefix-cover condition: the threshold can vary
with `M`, provided it is small enough for that `M`. -/
theorem ratio_limit_eq_goldenRatio_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : EventualFinSingletonSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_eventualFinSingletonSmallPrefixCover
      hmono hpos hinfinite hlim hL1 hsmall)

/-- Value theorem under the still weaker condition that suitable small
finite-singleton windows occur arbitrarily far out. -/
theorem ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_arbLargeFinSingletonSmallPrefixCover
      hmono hpos hinfinite hlim hL1 hsmall)

/-- Value theorem under the current weakest finite-window condition: arbitrarily
far out, only the first seed inequality is assumed. -/
theorem ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_arbLargeFinSingletonFirstSmallPrefixCover
      hmono hpos hgap hfinite hinfinite hlim hL1 hfirst)

/-- Value theorem under the equivalent direct-cover form of the current weakest
finite-window condition. -/
theorem ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    L = Real.goldenRatio := by
  exact le_antisymm
    (limit_le_goldenRatio hmono hpos hfinite hlim)
    (goldenRatio_le_limit_of_arbLargeFinSingletonFirstPrefixCover
      hmono hpos hgap hfinite hinfinite hlim hL1 hcover)

/-- Same theorem phrased as convergence to the golden ratio. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio
      hmono hpos hratioGap hfinite hinfinite hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_uniformFinSingletonComplete`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_uniformFinSingletonComplete
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (huniform : UniformFinSingletonComplete a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_uniformFinSingletonComplete
      hmono hpos hratioGap hfinite hinfinite huniform hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_uniformFinSingletonPrefixCover`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hprefix : UniformFinSingletonPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_uniformFinSingletonPrefixCover
      hmono hpos hratioGap hfinite hinfinite hprefix hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_eventualFinSingletonSmallPrefixCover`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : EventualFinSingletonSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_eventualFinSingletonSmallPrefixCover
      hmono hpos hfinite hinfinite hsmall hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonSmallPrefixCover`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonSmallPrefixCover
      hmono hpos hfinite hinfinite hsmall hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstSmallPrefixCover`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstSmallPrefixCover
      hmono hpos hgap hfinite hinfinite hfirst hlim hL1
  simpa [hEq] using hlim

/-- Convergence form of
`ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstPrefixCover`. -/
theorem ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ} {L : ℝ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a)
    (hlim : Tendsto (quotient a) atTop (nhds L))
    (hL1 : 1 < L) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  have hEq : L = Real.goldenRatio :=
    ratio_limit_eq_goldenRatio_of_arbLargeFinSingletonFirstPrefixCover
      hmono hpos hgap hfinite hinfinite hcover hlim hL1
  simpa [hEq] using hlim

/-- Compact formulation: if a ratio limit `L > 1` exists, then it is `φ`. -/
theorem intended_problem_if_limit_exists
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists
    hmono hpos hratioGap hfinite hinfinite hlim hL1

/-- Compact formulation of the axiom-free conditional route using the explicit
uniform finite-base singleton completeness hypothesis. -/
theorem intended_problem_if_limit_exists_of_uniformFinSingletonComplete
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (huniform : UniformFinSingletonComplete a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_uniformFinSingletonComplete
    hmono hpos hratioGap hfinite hinfinite huniform hlim hL1

/-- Compact formulation of the axiom-free conditional route using only the
weaker uniform finite-base prefix-cover hypothesis. -/
theorem intended_problem_if_limit_exists_of_uniformFinSingletonPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hprefix : UniformFinSingletonPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_uniformFinSingletonPrefixCover
    hmono hpos hratioGap hfinite hinfinite hprefix hlim hL1

/-- Compact formulation of the axiom-free conditional route using the
`M`-dependent small prefix-cover window condition. -/
theorem intended_problem_if_limit_exists_of_eventualFinSingletonSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : EventualFinSingletonSmallPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_eventualFinSingletonSmallPrefixCover
    hmono hpos hfinite hinfinite hsmall hlim hL1

/-- Compact formulation using only arbitrarily late good finite-singleton
prefix-cover windows. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hsmall : ArbitrarilyLargeFinSingletonSmallPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonSmallPrefixCover
    hmono hpos hfinite hinfinite hsmall hlim hL1

/-- Compact formulation using only arbitrarily late first seed inequalities. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonFirstSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hfirst : ArbitrarilyLargeFinSingletonFirstSmallPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonFirstSmallPrefixCover
    hmono hpos hgap hfinite hinfinite hfirst hlim hL1

/-- Compact formulation using the direct finite-prefix cover of the first seed
window `[nextSeedMargin a M, a (M + 2) - 1]`. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonFirstPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hcover : ArbitrarilyLargeFinSingletonFirstPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) := by
  obtain ⟨L, hL1, hlim⟩ := hexists
  exact ratio_tendsto_goldenRatio_of_limit_exists_of_arbLargeFinSingletonFirstPrefixCover
    hmono hpos hgap hfinite hinfinite hcover hlim hL1

/-- Compact formulation using the local first-window shift-closure condition.
Finite-deletion completeness supplies the prefix cover through `M + 1`; the
shift-closure condition is exactly what lowers that cover to the prefix through
`M`. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonFirstWindowShiftClosed
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hclosed : ArbitrarilyLargeFinSingletonFirstWindowShiftClosed a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  intended_problem_if_limit_exists_of_arbLargeFinSingletonFirstPrefixCover
    hmono hpos hgap hfinite hinfinite
    (arbLargeFinSingletonFirstPrefixCover_of_firstWindowShiftClosed
      hmono hpos hgap hfinite hclosed)
    hexists

/-- Compact formulation using the moving singleton-deletion threshold condition:
arbitrarily far out, after deleting `F ∪ {M + 1}`, completeness starts no later
than `a (M + 1)`. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonCompleteBelowPrev
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hgap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hbelow : ArbitrarilyLargeFinSingletonCompleteBelowPrev a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  intended_problem_if_limit_exists_of_arbLargeFinSingletonFirstPrefixCover
    hmono hpos hgap hfinite hinfinite
    (arbLargeFinSingletonFirstPrefixCover_of_completeBelowPrev
      hmono hpos hgap hfinite hbelow)
    hexists

/-- Compact formulation using the least-threshold phrasing of the small
finite-window condition. -/
theorem intended_problem_if_limit_exists_of_eventualFinSingletonLeastSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hleast : EventualFinSingletonLeastSmallPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  intended_problem_if_limit_exists_of_eventualFinSingletonSmallPrefixCover
    hmono hpos hfinite hinfinite
    (eventualFinSingletonSmallPrefixCover_of_leastSmall hleast) hexists

/-- Compact formulation using the least-threshold phrasing of the arbitrarily
late small finite-window condition. -/
theorem intended_problem_if_limit_exists_of_arbLargeFinSingletonLeastSmallPrefixCover
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hleast : ArbitrarilyLargeFinSingletonLeastSmallPrefixCover a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  intended_problem_if_limit_exists_of_arbLargeFinSingletonSmallPrefixCover
    hmono hpos hfinite hinfinite
    (arbLargeFinSingletonSmallPrefixCover_of_leastLarge hleast) hexists

/-- Short public-facing name for the main theorem. -/
theorem main
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : FiniteDeletionComplete a)
    (hinfinite : InfiniteDeletionIncomplete a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  intended_problem_if_limit_exists
    hmono hpos hratioGap hfinite hinfinite hexists

/-- Expanded statement for human inspection.

This is definitionally the same theorem as `main`, but the three compact
hypotheses `HasUniformRatioGap`, `FiniteDeletionComplete`, and
`InfiniteDeletionIncomplete` are expanded in the theorem statement. -/
theorem main_expanded
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ n : ℕ, 1 + ε ≤ quotient a n)
    (hfinite :
      ∀ D : Set ℕ, D.Finite →
        ∃ H : ℕ, ∀ n : ℕ, H ≤ n →
          n ∈ subsetSums a Dᶜ)
    (hinfinite :
      ∀ D : Set ℕ, D.Infinite →
        ¬ ∃ H : ℕ, ∀ n : ℕ, H ≤ n →
          n ∈ subsetSums a Dᶜ)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  main hmono hpos hratioGap hfinite hinfinite hexists

/-- Public-facing theorem using value deletion rather than index deletion.
Finite and infinite deletion hypotheses are stated for sets `B : Set ℕ` of
sequence values. -/
theorem main_valueDeletion
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap : HasUniformRatioGap a)
    (hfinite : ValueFiniteDeletionComplete a)
    (hinfinite : ValueInfiniteDeletionIncomplete a)
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  main hmono hpos hratioGap
    (finiteDeletionComplete_of_valueFiniteDeletionComplete hmono hfinite)
    (infiniteDeletionIncomplete_of_valueInfiniteDeletionIncomplete hmono hinfinite)
    hexists

/-- Expanded value-deletion statement for human inspection. -/
theorem main_valueDeletion_expanded
    {a : ℕ → ℕ}
    (hmono : StrictMono a)
    (hpos : ∀ n : ℕ, 0 < a n)
    (hratioGap :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ n : ℕ, 1 + ε ≤ quotient a n)
    (hfinite :
      ∀ B : Set ℕ, B.Finite →
        ∃ H : ℕ, ∀ n : ℕ, H ≤ n →
          n ∈ subsetSums a {i : ℕ | a i ∉ B})
    (hinfinite :
      ∀ B : Set ℕ, B.Infinite → B ⊆ Set.range a →
        ¬ ∃ H : ℕ, ∀ n : ℕ, H ≤ n →
          n ∈ subsetSums a {i : ℕ | a i ∉ B})
    (hexists : ∃ L : ℝ, 1 < L ∧ Tendsto (quotient a) atTop (nhds L)) :
    Tendsto (quotient a) atTop (nhds Real.goldenRatio) :=
  main_valueDeletion hmono hpos hratioGap hfinite hinfinite hexists



end

end Erdos346
