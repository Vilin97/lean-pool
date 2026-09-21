/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorNonparabolicOrderCover
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.NonparabolicUnionBound
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.PairedCorvajaZannierBound

/-!
# Paired Corvaja--Zannier escape over maximal candidate orders

Right-coordinate inversion halves the unconditional bidegree-`(2,2)`
Corvaja--Zannier estimate on the nonparabolic support.  Combining that factor
with the maximal-divisor cover gives two separate sufficient inequalities:

* `(6 * K)^3 < currentOrder` for the cube-root branch;
* `24 * K * currentOrder < p` for the branch divided by `p`,

where `K` is the number of divisibility-maximal candidate orders.

No Euler-characteristic improvement is used in this module.
-/

namespace BGS.Markoff

noncomputable section

variable {E : Type*} [Field E] [Fintype E]

/-- A common paired Corvaja--Zannier bound for every right order at most the
current left order. -/
def pairedCorvajaZannierCurrentOrderEnvelope
    (p currentOrder : ℕ) : ℝ :=
  max
    (6 * (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)))
    (24 * (((currentOrder * currentOrder : ℕ) : ℝ) / p))

/-- Replacing a candidate right order by the current left order enlarges both
branches of the paired bound. -/
theorem pairedCorvajaZannierTraceUpperBound_le_currentOrderEnvelope
    (p currentOrder d : ℕ) (hd : d ≤ currentOrder) :
    pairedCorvajaZannierTraceUpperBound p currentOrder d ≤
      pairedCorvajaZannierCurrentOrderEnvelope p currentOrder := by
  have hmulNat : currentOrder * d ≤ currentOrder * currentOrder :=
    Nat.mul_le_mul_left currentOrder hd
  have hmul : (((currentOrder * d : ℕ) : ℝ)) ≤
      (((currentOrder * currentOrder : ℕ) : ℝ)) := by
    exact_mod_cast hmulNat
  unfold pairedCorvajaZannierTraceUpperBound
    pairedCorvajaZannierCurrentOrderEnvelope
  exact max_le_max
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hmul (by norm_num))
      (by norm_num))
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hmul (Nat.cast_nonneg p))
      (by norm_num))

/-- The paired bounds over the maximal candidate orders are controlled by the
number of those orders times the common current-order envelope. -/
theorem middleGameMaximalPairedCorvajaZannierSum_le_card_mul_envelope
    (p currentOrder : ℕ) (hp : 1 < p) :
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        pairedCorvajaZannierTraceUpperBound p currentOrder d) ≤
      ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        pairedCorvajaZannierCurrentOrderEnvelope p currentOrder := by
  classical
  calc
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        pairedCorvajaZannierTraceUpperBound p currentOrder d) ≤
        ∑ _d ∈ middleGameMaximalOrders p currentOrder,
          pairedCorvajaZannierCurrentOrderEnvelope p currentOrder := by
      exact Finset.sum_le_sum fun d hd ↦
        pairedCorvajaZannierTraceUpperBound_le_currentOrderEnvelope
          p currentOrder d
          (mem_middleGameCandidateOrders_iff.mp
            (middleGameMaximalOrders_subset_candidateOrders hp hd)).1
    _ = ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        pairedCorvajaZannierCurrentOrderEnvelope p currentOrder := by
      simp

/-- The two coefficient-sensitive natural-number inequalities imply that the
whole paired maximal-order envelope is smaller than the current order. -/
theorem orderCount_mul_pairedCorvajaZannierEnvelope_lt_currentOrder
    (p currentOrder orderCount : ℕ)
    (hcurrentOrder : 0 < currentOrder)
    (hcube : (6 * orderCount) ^ 3 < currentOrder)
    (hlinear : 24 * orderCount * currentOrder < p) :
    (orderCount : ℝ) *
        pairedCorvajaZannierCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let rootCoefficient : ℝ := 6 * orderCount
  let linearCoefficient : ℝ := 24 * orderCount
  have horderPos : (0 : ℝ) < currentOrder := by
    exact_mod_cast hcurrentOrder
  have horderNonneg : (0 : ℝ) ≤ currentOrder := horderPos.le
  have hrootCoefficientNonneg : 0 ≤ rootCoefficient := by
    dsimp [rootCoefficient]
    positivity
  have hlinearCoefficientNonneg : 0 ≤ linearCoefficient := by
    dsimp [linearCoefficient]
    positivity
  have hcubeReal :
      rootCoefficient ^ (3 : ℕ) < (currentOrder : ℝ) := by
    dsimp [rootCoefficient]
    exact_mod_cast hcube
  have hrootCoefficient :
      rootCoefficient < (currentOrder : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := (Real.lt_rpow_inv_iff_of_pos hrootCoefficientNonneg
      horderNonneg (by norm_num : (0 : ℝ) < 3)).2
    have h' :
        rootCoefficient < (currentOrder : ℝ) ^ (3 : ℝ)⁻¹ :=
      h (by simpa [Real.rpow_natCast] using hcubeReal)
    simpa only [one_div] using h'
  have hrootPositive :
      0 < (((currentOrder * currentOrder : ℕ) : ℝ) ^
        ((1 : ℝ) / 3)) := by
    positivity
  have hcubeRootIdentity :
      (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) =
        (currentOrder : ℝ) := by
    rw [Nat.cast_mul]
    rw [← Real.mul_rpow horderNonneg
      (mul_nonneg horderNonneg horderNonneg)]
    convert Real.pow_rpow_inv_natCast horderNonneg
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    all_goals ring_nf
  have hrootTerm :
      rootCoefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) <
        (currentOrder : ℝ) := by
    calc
      rootCoefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) <
          (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^
              ((1 : ℝ) / 3)) :=
        mul_lt_mul_of_pos_right hrootCoefficient hrootPositive
      _ = (currentOrder : ℝ) := hcubeRootIdentity
  have hlinearReal :
      linearCoefficient * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp [linearCoefficient]
    exact_mod_cast hlinear
  have hpPos : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hquotientTerm :
      linearCoefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) <
        (currentOrder : ℝ) := by
    have hratio :
        linearCoefficient * (currentOrder : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hpPos).2 hlinearReal
    calc
      linearCoefficient *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) =
          (linearCoefficient * (currentOrder : ℝ) / (p : ℝ)) *
            (currentOrder : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ < 1 * (currentOrder : ℝ) :=
        mul_lt_mul_of_pos_right hratio horderPos
      _ = (currentOrder : ℝ) := one_mul _
  calc
    (orderCount : ℝ) *
        pairedCorvajaZannierCurrentOrderEnvelope p currentOrder =
        max
          (rootCoefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^
              ((1 : ℝ) / 3)))
          (linearCoefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) := by
      rw [pairedCorvajaZannierCurrentOrderEnvelope,
        mul_max_of_nonneg _ _ (Nat.cast_nonneg orderCount)]
      dsimp [rootCoefficient, linearCoefficient]
      push_cast
      congr 1 <;> ring
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

/-- The finite nonparabolic escape theorem over maximal candidate orders.
The Corvaja--Zannier estimate is supplied by the in-repository general
bidegree-`(2,2)` theorem and right-inversion pairing. -/
theorem exists_left_element_escaping_nonparabolic_maximalOrders
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
    (alpha beta : E) (Hleft : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder :
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        Nat.card (rightSubgroup d) = d)
    (hadmissible :
      WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (hcurrentOrder : 0 < Nat.card Hleft)
    (hp : 1 < p)
    (hcube :
      (6 * (middleGameMaximalOrders p (Nat.card Hleft)).card) ^ 3 <
        Nat.card Hleft)
    (hlinear :
      24 * (middleGameMaximalOrders p (Nat.card Hleft)).card *
        Nat.card Hleft < p) :
    ∃ hleft : Hleft,
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        ∀ hright : rightSubgroup d,
          ((hright : Eˣ) ^ 2) ≠ 1 →
            weightedSplitTorusTrace alpha beta hleft ≠
              splitTorusTrace hright := by
  classical
  let orders := middleGameMaximalOrders p (Nat.card Hleft)
  let bound : ℕ → ℝ :=
    fun d ↦ pairedCorvajaZannierTraceUpperBound p (Nat.card Hleft) d
  have hbound :
      ∀ d ∈ orders,
        ((weightedTraceEquationNonparabolicLeftSupport
          alpha beta Hleft (rightSubgroup d)).card : ℝ) ≤ bound d := by
    intro d hd
    have hd' : d ∈ middleGameMaximalOrders p (Nat.card Hleft) := by
      simpa [orders] using hd
    have h :=
      weightedTraceEquationNonparabolicLeftSupport_card_cast_le_pairedCorvajaZannier
        p E alpha beta Hleft (rightSubgroup d) hadmissible
    rw [hrightOrder d hd'] at h
    simpa [bound] using h
  have hsmall : (∑ d ∈ orders, bound d) < (Nat.card Hleft : ℝ) := by
    calc
      (∑ d ∈ orders, bound d) =
          ∑ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
            pairedCorvajaZannierTraceUpperBound
              p (Nat.card Hleft) d := by
        simp [orders, bound]
      _ ≤ ((middleGameMaximalOrders p (Nat.card Hleft)).card : ℝ) *
          pairedCorvajaZannierCurrentOrderEnvelope
            p (Nat.card Hleft) :=
        middleGameMaximalPairedCorvajaZannierSum_le_card_mul_envelope
          p (Nat.card Hleft) hp
      _ < (Nat.card Hleft : ℝ) :=
        orderCount_mul_pairedCorvajaZannierEnvelope_lt_currentOrder
          p (Nat.card Hleft)
            (middleGameMaximalOrders p (Nat.card Hleft)).card
          hcurrentOrder hcube hlinear
  obtain ⟨hleft, hleftEscapes⟩ :=
    exists_left_element_escaping_nonparabolic_orders_of_sum_bound
      alpha beta Hleft orders rightSubgroup bound hbound hsmall
  refine ⟨hleft, ?_⟩
  intro d hd hright hrightSq
  exact hleftEscapes d (by simpa [orders] using hd) hright hrightSq

end

end BGS.Markoff
