/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Convert

/-!
# Analytic lemmas for the block construction

Convergence of a real series is expressed through its ordered partial sums.
In particular, the conclusion below is deliberately a `Tendsto` statement:
`Summable` for real series would assert unconditional (absolute) convergence.
-/

@[expose] public section

open Filter Finset Topology

namespace NonMRR

/-- The partial sum of a series in the order specified by a permutation. -/
def rearrangedPartialSum (a : ℕ → ℝ) (π : Equiv.Perm ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ range j, a (π i)

/-- A coordinate belongs to at most one member of a disjoint block family. -/
theorem summable_blocks_at_coordinate
    (u : ℕ → ℕ → ℝ) (I : ℕ → Finset ℕ)
    (hdisjoint : Pairwise (fun n m ↦ Disjoint (I n) (I m)))
    (hsupport : ∀ n i, i ∉ I n → u n i = 0) (i : ℕ) :
    Summable (fun n ↦ u n i) := by
  apply summable_of_hasFiniteSupport
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra hne
  have hin : i ∈ I n := by
    by_contra hni
    exact hn (hsupport n i hni)
  have him : i ∈ I m := by
    by_contra hmi
    exact hm (hsupport m i hmi)
  exact (Finset.disjoint_left.mp (hdisjoint hne)) hin him

/-- The coordinatewise sum of disjoint blocks equals the unique relevant block. -/
theorem tsum_blocks_eq_of_mem
    (u : ℕ → ℕ → ℝ) (I : ℕ → Finset ℕ)
    (hdisjoint : Pairwise (fun n m ↦ Disjoint (I n) (I m)))
    (hsupport : ∀ n i, i ∉ I n → u n i = 0)
    (n i : ℕ) (hi : i ∈ I n) :
    (∑' m, u m i) = u n i := by
  apply tsum_eq_single n
  intro m hmn
  apply hsupport m i
  intro hm
  exact (Finset.disjoint_left.mp (hdisjoint hmn)) hm hi

/-- Summably dominated blocks with sum zero have total ordered sum zero.

The domination may fail at finitely many block indices. The local summability
hypothesis is automatic for pairwise disjoint finite supports. -/
theorem tendsto_zero_of_dominated_blocks
    (u : ℕ → ℕ → ℝ) (π : Equiv.Perm ℕ)
    (hzero : ∀ n, HasSum (u n) 0)
    (hlocal : ∀ i, Summable (fun n ↦ u n i))
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ᶠ n in atTop, ∀ j, ‖rearrangedPartialSum (u n) π j‖ ≤ b n) :
    Tendsto (rearrangedPartialSum (fun i ↦ ∑' n, u n i) π) atTop (𝓝 0) := by
  classical
  have hconv (n : ℕ) :
      Tendsto (rearrangedPartialSum (u n) π) atTop (𝓝 0) := by
    exact (π.hasSum_iff.mpr (hzero n)).tendsto_sum_nat
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  let bound : ℕ → ℝ := fun n ↦ if n < N then 1 else b n
  have hsum : Summable bound := hb.congr_atTop (by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [bound, not_lt.mpr hn])
  have hfinite : ∀ᶠ j in atTop, ∀ n ∈ range N,
      ‖rearrangedPartialSum (u n) π j‖ ≤ (1 : ℝ) := by
    apply (eventually_all_finset (range N)).mpr
    intro n _
    have hn := (tendsto_order.1 (hconv n).norm).2 1 (by simp)
    exact hn.mono fun _ h ↦ h.le
  have hdom : ∀ᶠ j in atTop, ∀ n,
      ‖rearrangedPartialSum (u n) π j‖ ≤ bound n := by
    filter_upwards [hfinite] with j hj n
    by_cases hn : n < N
    · simpa [bound, hn] using hj n (mem_range.mpr hn)
    · simpa [bound, hn] using hN n (not_lt.mp hn) j
  have ht := tendsto_tsum_of_dominated_convergence hsum hconv hdom
  simp only [tsum_zero] at ht
  convert ht using 1
  ext j
  exact (Summable.tsum_finsetSum (fun i (_ : i ∈ range j) ↦ hlocal (π i))).symm

/-- Infinitely many disjoint blocks of absolute mass at least one prevent
absolute convergence. The blocks need not be intervals. -/
theorem not_summable_norm_of_disjoint_blocks
    (a : ℕ → ℝ) (I : ℕ → Finset ℕ) (A : Set ℕ)
    (hA : A.Infinite) (hdisjoint : A.PairwiseDisjoint I)
    (hmass : ∀ n ∈ A, 1 ≤ ∑ i ∈ I n, ‖a i‖) :
    ¬ Summable (fun i ↦ ‖a i‖) := by
  classical
  intro ha
  obtain ⟨N, hN⟩ := exists_nat_gt (∑' i, ‖a i‖)
  obtain ⟨s, hs, hcard⟩ := hA.exists_subset_card_eq N
  have hpair : (↑s : Set ℕ).PairwiseDisjoint I :=
    fun _ hn _ hm hne ↦ hdisjoint (hs hn) (hs hm) hne
  have hle : (N : ℝ) ≤ ∑' i, ‖a i‖ := calc
    (N : ℝ) = ∑ _n ∈ s, (1 : ℝ) := by simp [hcard]
    _ ≤ ∑ n ∈ s, ∑ i ∈ I n, ‖a i‖ :=
      sum_le_sum fun n hn ↦ hmass n (hs hn)
    _ = ∑ i ∈ s.biUnion I, ‖a i‖ := (sum_biUnion hpair).symm
    _ ≤ ∑' i, ‖a i‖ := ha.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _)
  exact (not_le_of_gt hN) hle

/-- The analytic conclusion used in the slalom construction: disjoint balanced
finite blocks, uniformly small outside finitely many indices in both relevant
orders, give a conditionally convergent series whose sum the permutation preserves. -/
theorem conditional_series_of_disjoint_balanced_blocks
    (u : ℕ → ℕ → ℝ) (I : ℕ → Finset ℕ) (A : Set ℕ)
    (π : Equiv.Perm ℕ)
    (hdisjoint : Pairwise (fun n m ↦ Disjoint (I n) (I m)))
    (hsupport : ∀ n i, i ∉ I n → u n i = 0)
    (hbalance : ∀ n, ∑ i ∈ I n, u n i = 0)
    (hA : A.Infinite)
    (hmass : ∀ n ∈ A, 1 ≤ ∑ i ∈ I n, ‖u n i‖)
    (b : ℕ → ℝ) (hb : Summable b)
    (hid : ∀ᶠ n in atTop, ∀ j,
      ‖rearrangedPartialSum (u n) (Equiv.refl ℕ) j‖ ≤ b n)
    (hπ : ∀ᶠ n in atTop, ∀ j, ‖rearrangedPartialSum (u n) π j‖ ≤ b n) :
    let a : ℕ → ℝ := fun i ↦ ∑' n, u n i
    Tendsto (rearrangedPartialSum a (Equiv.refl ℕ)) atTop (𝓝 0) ∧
    Tendsto (rearrangedPartialSum a π) atTop (𝓝 0) ∧
    ¬ Summable (fun i ↦ ‖a i‖) := by
  classical
  dsimp only
  have hz (n : ℕ) : HasSum (u n) 0 := by
    rw [← hbalance n]
    exact hasSum_sum_of_ne_finset_zero (hsupport n)
  have hl := summable_blocks_at_coordinate u I hdisjoint hsupport
  refine ⟨tendsto_zero_of_dominated_blocks u _ hz hl b hb hid,
    tendsto_zero_of_dominated_blocks u π hz hl b hb hπ, ?_⟩
  apply not_summable_norm_of_disjoint_blocks _ I A hA
  · exact fun _ _ _ _ hne ↦ hdisjoint hne
  · intro n hn
    convert hmass n hn using 1
    apply sum_congr rfl
    intro i hi
    rw [tsum_blocks_eq_of_mem u I hdisjoint hsupport n i hi]

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
