/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.OrderEscape
public import LeanPool.MarkoffModP.BGS.NumberTheory.MaximalDivisorBounds

/-!
# Maximal candidate orders in the Markoff middle game

Every ordinary candidate order divides a divisibility-maximal candidate, and
the canonical roots-of-unity subgroups are monotone under that divisibility.
Hence the Corvaja--Zannier union only needs maximal orders.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

def middleGameMaximalOrders (p currentOrder : ℕ) : Finset ℕ :=
  maximalDivisorsBelow (p - 1) (currentOrder + 1) ∪
    maximalDivisorsBelow (p + 1) (currentOrder + 1)

theorem middleGameMaximalOrders_card_le
    (p currentOrder : ℕ) :
    (middleGameMaximalOrders p currentOrder).card ≤
      (maximalDivisorsBelow (p - 1) (currentOrder + 1)).card +
        (maximalDivisorsBelow (p + 1) (currentOrder + 1)).card :=
  Finset.card_union_le _ _

theorem middleGameMaximalOrders_subset_candidateOrders
    {p currentOrder : ℕ} (hp : 1 < p) :
    middleGameMaximalOrders p currentOrder ⊆
      middleGameCandidateOrders p currentOrder := by
  intro m hm
  rw [middleGameMaximalOrders, Finset.mem_union] at hm
  rw [mem_middleGameCandidateOrders_iff]
  rcases hm with hm | hm
  · have hdata := mem_maximalDivisorsBelow_iff.mp hm
    refine ⟨by omega, Or.inl ?_⟩
    exact ⟨(Nat.mem_divisors.mp hdata.1).1, by omega⟩
  · have hdata := mem_maximalDivisorsBelow_iff.mp hm
    exact ⟨by omega, Or.inr (Nat.mem_divisors.mp hdata.1).1⟩

theorem exists_dvd_middleGameMaximalOrder
    {p currentOrder d : ℕ} (hp : 1 < p)
    (hd : d ∈ middleGameCandidateOrders p currentOrder) :
    ∃ m ∈ middleGameMaximalOrders p currentOrder, d ∣ m := by
  have hdbound : d < currentOrder + 1 :=
    Nat.lt_succ_of_le (mem_middleGameCandidateOrders_iff.mp hd).1
  rcases (mem_middleGameCandidateOrders_iff.mp hd).2 with hminus | hplus
  · obtain ⟨m, hm, hdm⟩ :=
      exists_dvd_maximalDivisorBelow hminus.2 hminus.1 hdbound
    exact ⟨m, by
      rw [middleGameMaximalOrders, Finset.mem_union]
      exact Or.inl hm, hdm⟩
  · obtain ⟨m, hm, hdm⟩ :=
      exists_dvd_maximalDivisorBelow (by omega : p + 1 ≠ 0) hplus hdbound
    exact ⟨m, by
      rw [middleGameMaximalOrders, Finset.mem_union]
      exact Or.inr hm, hdm⟩

theorem middleGameRightSubgroup_mono
    (p d m : ℕ) [Fact p.Prime] (hdm : d ∣ m) :
    middleGameRightSubgroup p d ≤ middleGameRightSubgroup p m := by
  intro u hu
  rw [mem_middleGameRightSubgroup_iff_pow_eq_one] at hu ⊢
  obtain ⟨k, rfl⟩ := hdm
  rw [pow_mul, hu, one_pow]

theorem exists_middleGameMaximalOrder_trace_of_nonparabolic
    (p currentOrder : ℕ) [Fact p.Prime]
    (hpTwo : p ≠ 2) (hp : 1 < p)
    (t : ZMod p) (hnonparabolic : t ^ 2 ≠ 4)
    (hsmall : rotationOrder t ≤ currentOrder) :
    ∃ m ∈ middleGameMaximalOrders p currentOrder,
      ∃ h₂ : middleGameRightSubgroup p m,
        algebraMap (ZMod p) (quadraticFiniteField p) t =
          splitTorusTrace h₂ := by
  have hd :
      rotationOrder t ∈ middleGameCandidateOrders p currentOrder :=
    rotationOrder_mem_middleGameCandidateOrders_of_nonparabolic
      p currentOrder hpTwo t hnonparabolic hsmall
  obtain ⟨m, hm, horderDvd⟩ :=
    exists_dvd_middleGameMaximalOrder hp hd
  obtain ⟨h₂, htrace⟩ :=
    exists_middleGameRightSubgroup_trace_of_nonparabolic_rotationOrder
      p (rotationOrder t) hpTwo t hnonparabolic rfl
  let h₂max : middleGameRightSubgroup p m :=
    ⟨h₂, middleGameRightSubgroup_mono p (rotationOrder t) m horderDvd h₂.2⟩
  exact ⟨m, hm, h₂max, htrace⟩

theorem middleGameMaximalOrder_rightSubgroup_natCard
    (p currentOrder m : ℕ) [Fact p.Prime] (hp : 1 < p)
    (hm : m ∈ middleGameMaximalOrders p currentOrder) :
    Nat.card (middleGameRightSubgroup p m) = m :=
  middleGameRightSubgroup_natCard p currentOrder m
    (middleGameMaximalOrders_subset_candidateOrders hp hm)

end BGS.Markoff
