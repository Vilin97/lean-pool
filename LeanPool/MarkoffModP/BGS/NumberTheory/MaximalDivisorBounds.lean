/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.JointNeighborDivisorBound
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Maximal-divisor bounds

This file proves the finite-poset cover behind the paper's maximal-divisor
improvement and combines it with the new joint `p - 1`, `p + 1` estimate.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- Divisors of `n` maximal under divisibility among those strictly below
`bound`. -/
def maximalDivisorsBelow (n bound : ℕ) : Finset ℕ :=
  n.divisors.filter fun d =>
    d < bound ∧
      ∀ e ∈ n.divisors, e < bound → d ∣ e → e = d

@[simp]
theorem mem_maximalDivisorsBelow_iff
    {n bound d : ℕ} :
    d ∈ maximalDivisorsBelow n bound ↔
      d ∈ n.divisors ∧ d < bound ∧
        ∀ e ∈ n.divisors, e < bound → d ∣ e → e = d := by
  simp [maximalDivisorsBelow]

theorem maximalDivisorsBelow_subset_divisors (n bound : ℕ) :
    maximalDivisorsBelow n bound ⊆ n.divisors := by
  intro d hd
  exact (mem_maximalDivisorsBelow_iff.mp hd).1

theorem maximalDivisorsBelow_card_le_card_divisors (n bound : ℕ) :
    (maximalDivisorsBelow n bound).card ≤ n.divisors.card :=
  Finset.card_le_card (maximalDivisorsBelow_subset_divisors n bound)

/-- Every divisor below the cutoff divides a maximal divisor below it. -/
theorem exists_dvd_maximalDivisorBelow
    {n bound d : ℕ} (hn : n ≠ 0) (hdn : d ∣ n) (hdbound : d < bound) :
    ∃ m ∈ maximalDivisorsBelow n bound, d ∣ m := by
  let candidates := n.divisors.filter fun m => m < bound ∧ d ∣ m
  have hdmem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdn, hn⟩
  have hnonempty : candidates.Nonempty := by
    refine ⟨d, ?_⟩
    simp [candidates, hdmem, hdbound]
  let m := candidates.max' hnonempty
  have hmmem : m ∈ candidates := Finset.max'_mem candidates hnonempty
  have hmdata : m ∈ n.divisors ∧ m < bound ∧ d ∣ m := by
    simpa [candidates] using hmmem
  refine ⟨m, ?_, hmdata.2.2⟩
  rw [mem_maximalDivisorsBelow_iff]
  refine ⟨hmdata.1, hmdata.2.1, ?_⟩
  intro e hediv hebound hme
  have hde : d ∣ e := hmdata.2.2.trans hme
  have hemem : e ∈ candidates := by
    simp only [candidates, Finset.mem_filter]
    exact ⟨hediv, hebound, hde⟩
  have hem : e ≤ m := Finset.le_max' candidates e hemem
  have hepos : 0 < e :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hediv).1 (Nat.pos_of_ne_zero hn)
  have hme' : m ≤ e := Nat.le_of_dvd hepos hme
  exact Nat.le_antisymm hem hme'

section CyclicCover

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

/-- Elements killed by the `m`-th power map. -/
def elementsWithPowOne (m : ℕ) : Finset G :=
  Finset.univ.filter fun g => g ^ m = 1

@[simp]
theorem mem_elementsWithPowOne_iff {m : ℕ} {g : G} :
    g ∈ elementsWithPowOne G m ↔ g ^ m = 1 := by
  simp [elementsWithPowOne]

/-- Low-order elements in a cyclic group are covered by roots-of-unity sets
indexed by maximal divisors. -/
theorem elementsOfOrderLessThan_subset_maximalDivisorCover
    [IsCyclic G] (bound : ℕ) :
    (Finset.univ.filter fun g : G => orderOf g < bound) ⊆
      (maximalDivisorsBelow (Fintype.card G) bound).biUnion
        (elementsWithPowOne G) := by
  intro g hg
  have hgorder : orderOf g < bound := (Finset.mem_filter.mp hg).2
  obtain ⟨m, hmmax, horderDvd⟩ :=
    exists_dvd_maximalDivisorBelow Fintype.card_ne_zero orderOf_dvd_card hgorder
  rw [Finset.mem_biUnion]
  refine ⟨m, hmmax, ?_⟩
  rw [mem_elementsWithPowOne_iff]
  exact orderOf_dvd_iff_pow_eq_one.mp horderDvd

/-- The cyclic low-order count using only maximal divisors. -/
theorem elementsOfOrderLessThan_card_le_maximalDivisors
    [IsCyclic G] (bound : ℕ) :
    (Finset.univ.filter fun g : G => orderOf g < bound).card ≤
      (bound - 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
  calc
    (Finset.univ.filter fun g : G => orderOf g < bound).card ≤
        ((maximalDivisorsBelow (Fintype.card G) bound).biUnion
          (elementsWithPowOne G)).card :=
      Finset.card_le_card
        (elementsOfOrderLessThan_subset_maximalDivisorCover G bound)
    _ ≤ (maximalDivisorsBelow (Fintype.card G) bound).card *
        (bound - 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro m hm
      have hmLt : m < bound :=
        (mem_maximalDivisorsBelow_iff.mp hm).2.1
      have hmPos : 0 < m := by
        have hmDvd : m ∣ Fintype.card G :=
          (Nat.mem_divisors.mp
            (mem_maximalDivisorsBelow_iff.mp hm).1).1
        exact Nat.pos_of_dvd_of_pos hmDvd Fintype.card_pos
      calc
        (elementsWithPowOne G m).card ≤ m :=
          IsCyclic.card_pow_eq_one_le hmPos
        _ ≤ bound - 1 := Nat.le_sub_one_of_lt hmLt
    _ = (bound - 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card :=
      Nat.mul_comm _ _

end CyclicCover

/-- The two maximal-divisor counts inherit the exact joint tenth moment. -/
theorem maximalDivisorCounts_product_pow_ten_le
    {p bound : ℕ} (hp : Odd p) (hpTwo : 2 < p) :
    ((maximalDivisorsBelow (p - 1) bound).card *
      (maximalDivisorsBelow (p + 1) bound).card) ^ 10 ≤
        2 ^ 457 * (p ^ 2 - 1) := by
  have hminus :
      (maximalDivisorsBelow (p - 1) bound).card ≤
        (p - 1).divisors.card :=
    maximalDivisorsBelow_card_le_card_divisors _ _
  have hplus :
      (maximalDivisorsBelow (p + 1) bound).card ≤
        (p + 1).divisors.card :=
    maximalDivisorsBelow_card_le_card_divisors _ _
  calc
    ((maximalDivisorsBelow (p - 1) bound).card *
        (maximalDivisorsBelow (p + 1) bound).card) ^ 10 ≤
        ((p - 1).divisors.card * (p + 1).divisors.card) ^ 10 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hminus hplus) 10
    _ ≤ 2 ^ 456 * (p ^ 2 - 1) :=
      card_divisors_pred_mul_card_divisors_succ_pow_ten_le hp hpTwo
    _ ≤ 2 ^ 457 * (p ^ 2 - 1) := by gcongr; norm_num

/-- The new square envelope for the sum of the two maximal-divisor counts. -/
theorem maximalDivisorCounts_add_sq_le
    {p bound C J : ℕ}
    (hminus : (maximalDivisorsBelow (p - 1) bound).card ≤ C)
    (hplus : (maximalDivisorsBelow (p + 1) bound).card ≤ C)
    (hproduct :
      (maximalDivisorsBelow (p - 1) bound).card *
        (maximalDivisorsBelow (p + 1) bound).card ≤ J) :
    ((maximalDivisorsBelow (p - 1) bound).card +
      (maximalDivisorsBelow (p + 1) bound).card) ^ 2 ≤
        C ^ 2 + 3 * J :=
  add_sq_le_sq_add_three_mul_of_le_of_mul_le hminus hplus hproduct

end BGS.NumberTheory
