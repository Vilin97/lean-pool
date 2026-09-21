/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.RankinWidthEnvelope
import Mathlib.Order.Antichain

/-!
# One joint antichain for the two neighboring tori

The maximal candidate orders dividing `p - 1` and `p + 1` are not two
independent divisor families.  After removing the possible divisors `1` and
`2`, their union is a single antichain: a cross-side divisibility relation
would force its smaller term to divide the difference `2`.

This is the arithmetic input that makes the width-sensitive Rankin endpoint
strictly sharper than summing two complete divisor counts.
-/

namespace BGS.Markoff

open BGS.NumberTheory

/-- The actual middle-game maximal orders after removing the only divisors of
the neighbor difference `2`. -/
def nontrivialMiddleGameMaximalOrders (p bound : Nat) : Finset Nat :=
  (middleGameMaximalOrders p bound).filter fun d => ¬ d ∣ 2

@[simp] theorem mem_nontrivialMiddleGameMaximalOrders_iff
    {p bound d : Nat} :
    d ∈ nontrivialMiddleGameMaximalOrders p bound <->
      (d ∈ maximalDivisorsBelow (p - 1) (bound + 1) \/
        d ∈ maximalDivisorsBelow (p + 1) (bound + 1)) /\
          ¬ d ∣ 2 := by
  simp [nontrivialMiddleGameMaximalOrders, middleGameMaximalOrders]

/-- Every nontrivial maximal order divides the common product `p^2 - 1`. -/
theorem nontrivialMiddleGameMaximalOrders_subset_divisors_sq_sub_one
    {p bound : Nat} (hp : 1 < p) :
    nontrivialMiddleGameMaximalOrders p bound ⊆
      (p ^ 2 - 1).divisors := by
  intro d hd
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (sq_tsub_sq p 1)
  have hsq : 1 < p ^ 2 := by nlinarith
  have hcommonNe : p ^ 2 - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt hsq).ne'
  have hdData := mem_nontrivialMiddleGameMaximalOrders_iff.mp hd
  apply Nat.mem_divisors.mpr
  refine ⟨?_, hcommonNe⟩
  rcases hdData.1 with hdMinus | hdPlus
  · have hdDvd : d ∣ p - 1 :=
      (Nat.mem_divisors.mp
        (mem_maximalDivisorsBelow_iff.mp hdMinus).1).1
    obtain ⟨k, hk⟩ := hdDvd
    refine ⟨(p + 1) * k, ?_⟩
    calc
      p ^ 2 - 1 = (p + 1) * (p - 1) := hfactor
      _ = (p + 1) * (d * k) := by rw [hk]
      _ = d * ((p + 1) * k) := by ring
  · have hdDvd : d ∣ p + 1 :=
      (Nat.mem_divisors.mp
        (mem_maximalDivisorsBelow_iff.mp hdPlus).1).1
    obtain ⟨k, hk⟩ := hdDvd
    refine ⟨k * (p - 1), ?_⟩
    calc
      p ^ 2 - 1 = (p + 1) * (p - 1) := hfactor
      _ = (d * k) * (p - 1) := by rw [hk]
      _ = d * (k * (p - 1)) := by ring

/-- Divisibility between two nontrivial joint maximal orders forces equality.
The same-side cases use maximality; the cross-side cases use the difference
of the two neighboring torus orders. -/
theorem nontrivialMiddleGameMaximalOrders_eq_of_dvd
    {p bound a b : Nat} (hp : 1 < p)
    (ha : a ∈ nontrivialMiddleGameMaximalOrders p bound)
    (hb : b ∈ nontrivialMiddleGameMaximalOrders p bound)
    (hab : a ∣ b) :
    a = b := by
  have haData := mem_nontrivialMiddleGameMaximalOrders_iff.mp ha
  have hbData := mem_nontrivialMiddleGameMaximalOrders_iff.mp hb
  rcases haData.1 with haMinus | haPlus
  · rcases hbData.1 with hbMinus | hbPlus
    · exact
        ((mem_maximalDivisorsBelow_iff.mp haMinus).2.2 b
          (mem_maximalDivisorsBelow_iff.mp hbMinus).1
          (mem_maximalDivisorsBelow_iff.mp hbMinus).2.1
          hab).symm
    · exfalso
      apply haData.2
      have haDvdMinus : a ∣ p - 1 :=
        (Nat.mem_divisors.mp
          (mem_maximalDivisorsBelow_iff.mp haMinus).1).1
      have hbDvdPlus : b ∣ p + 1 :=
        (Nat.mem_divisors.mp
          (mem_maximalDivisorsBelow_iff.mp hbPlus).1).1
      have haDvdPlus : a ∣ p + 1 := hab.trans hbDvdPlus
      have hsub := Nat.dvd_sub haDvdPlus haDvdMinus
      have hdifference : (p + 1) - (p - 1) = 2 := by omega
      rw [hdifference] at hsub
      exact hsub
  · rcases hbData.1 with hbMinus | hbPlus
    · exfalso
      apply haData.2
      have haDvdPlus : a ∣ p + 1 :=
        (Nat.mem_divisors.mp
          (mem_maximalDivisorsBelow_iff.mp haPlus).1).1
      have hbDvdMinus : b ∣ p - 1 :=
        (Nat.mem_divisors.mp
          (mem_maximalDivisorsBelow_iff.mp hbMinus).1).1
      have haDvdMinus : a ∣ p - 1 := hab.trans hbDvdMinus
      have hsub := Nat.dvd_sub haDvdPlus haDvdMinus
      have hdifference : (p + 1) - (p - 1) = 2 := by omega
      rw [hdifference] at hsub
      exact hsub
    · exact
        ((mem_maximalDivisorsBelow_iff.mp haPlus).2.2 b
          (mem_maximalDivisorsBelow_iff.mp hbPlus).1
          (mem_maximalDivisorsBelow_iff.mp hbPlus).2.1
          hab).symm

/-- The nontrivial maximal candidate orders from both neighboring tori form
one canonical antichain under divisibility. -/
theorem nontrivialMiddleGameMaximalOrders_isAntichain
    {p bound : Nat} (hp : 1 < p) :
    IsAntichain (· ∣ ·)
      (nontrivialMiddleGameMaximalOrders p bound : Set Nat) := by
  intro a ha b hb hab hdiv
  apply hab
  exact nontrivialMiddleGameMaximalOrders_eq_of_dvd hp
    (by simpa using ha) (by simpa using hb) hdiv

/-- Restoring the discarded part costs at most the two exceptional divisors
`1` and `2`. -/
theorem middleGameMaximalOrders_card_le_nontrivial_add_two
    (p bound : Nat) :
    (middleGameMaximalOrders p bound).card <=
      (nontrivialMiddleGameMaximalOrders p bound).card + 2 := by
  classical
  let orders := middleGameMaximalOrders p bound
  let exceptional := orders.filter fun d => d ∣ 2
  have hexceptionalSubset : exceptional ⊆ ({1, 2} : Finset Nat) := by
    intro d hd
    have hdTwo : d ∣ 2 := (Finset.mem_filter.mp hd).2
    rcases Nat.prime_two.eq_one_or_self_of_dvd d hdTwo with rfl | rfl
    · simp
    · simp
  have hexceptionalCard : exceptional.card <= 2 := by
    calc
      exceptional.card <= ({1, 2} : Finset Nat).card :=
        Finset.card_le_card hexceptionalSubset
      _ = 2 := by decide
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := orders) (fun d => ¬ d ∣ 2)
  have hsplit' :
      (nontrivialMiddleGameMaximalOrders p bound).card +
          exceptional.card =
        (middleGameMaximalOrders p bound).card := by
    simpa [orders, exceptional, nontrivialMiddleGameMaximalOrders] using
      hsplit
  omega

/-- Any bound on the one nontrivial antichain gives a bound on all maximal
orders with an additive cost of only two. -/
theorem middleGameMaximalOrders_card_le_of_nontrivialWidth
    {p bound width : Nat}
    (hwidth :
      (nontrivialMiddleGameMaximalOrders p bound).card <= width) :
    (middleGameMaximalOrders p bound).card <= width + 2 := by
  exact (middleGameMaximalOrders_card_le_nontrivial_add_two p bound).trans
    (Nat.add_le_add_right hwidth 2)

/-- The exact-order witness cap can therefore use the width of the single
joint antichain, plus the two exceptional divisors. -/
theorem bound_le_rankinJointAntichainWitnessCap
    {p bound width : Nat}
    (hbound :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (hwidth :
      (nontrivialMiddleGameMaximalOrders p bound).card <= width) :
    bound <= rankinWidthWitnessCap (width + 2) := by
  exact bound_le_rankinWidthWitnessCap hbound
    (middleGameMaximalOrders_card_le_of_nontrivialWidth hwidth)

/-- Width-sensitive Rankin closure fed directly by the single joint
antichain. -/
theorem prime_le_of_matching_rankinNeighborProfile_jointAntichainWidth_leaf
    {p bound width rootCap cutoff : Nat}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hroot :
      8 * p <= (combinedTruncatedOrderTotientSum p bound) ^ 2)
    (hboundWitness :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (hwidth :
      (nontrivialMiddleGameMaximalOrders p bound).card <= width)
    (profile : RankinNeighborProfile)
    (hprofile : profile.Valid)
    (hmatch : profile.Matches p)
    (hrootValid : RankinWidthRootValid (width + 2) rootCap)
    (hleaf :
      RankinWidthClosesCutoff (width + 2) rootCap profile cutoff \/
        RankinWidthExcludesFailure (width + 2) rootCap profile) :
    p <= cutoff := by
  exact prime_le_of_matching_rankinNeighborProfile_rankinWidth_leaf
    hpPrime hpTwo hroot hboundWitness
    (middleGameMaximalOrders_card_le_of_nontrivialWidth hwidth)
    profile hprofile hmatch hrootValid hleaf

end BGS.Markoff
