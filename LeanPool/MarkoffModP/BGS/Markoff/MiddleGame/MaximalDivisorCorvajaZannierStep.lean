/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorOrderCover

/-!
# Corvaja--Zannier escape over maximal candidate orders

The published middle-game union runs over every candidate divisor of `p - 1`
or `p + 1`. Divisibility monotonicity of roots-of-unity subgroups shows that
it is enough to run the union over `middleGameMaximalOrders`: every smaller
candidate subgroup is contained in one of these maximal subgroups.

This file performs the finite union and its numerical reduction. The deep
Corvaja--Zannier estimate remains an explicit hypothesis about the actual
weighted trace-equation solution sets.
-/

@[expose] public section

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

/-- The Corvaja--Zannier sum over maximal candidate orders is bounded by the
number of those orders times the common current-order envelope. -/
theorem middleGameMaximalCorvajaZannierSum_le_card_mul_envelope
    (p currentOrder : ℕ) (hp : 1 < p) :
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
      ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder := by
  classical
  calc
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
        ∑ _d ∈ middleGameMaximalOrders p currentOrder,
          corvajaZannierCurrentOrderEnvelope p currentOrder := by
      exact Finset.sum_le_sum fun d hd ↦
        corvajaZannierTraceUpperBound_le_currentOrderEnvelope p currentOrder d
          (mem_middleGameCandidateOrders_iff.mp
            (middleGameMaximalOrders_subset_candidateOrders hp hd)).1
    _ = ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder := by
      simp

/-- A generic version of the two elementary inequalities controlling the
Corvaja--Zannier envelope. It is deliberately parameterized by the number of
orders in the union, so the maximal-divisor cover can use its much smaller
cardinality.

Writing `K` for `orderCount`, the hypotheses are

* `(48 K)^3 < currentOrder`;
* `48 K * currentOrder < p`.
-/
theorem orderCount_mul_corvajaZannierEnvelope_lt_currentOrder
    (p currentOrder orderCount : ℕ)
    (hcurrentOrder : 0 < currentOrder)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient * orderCount) ^ 3 <
        currentOrder)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient * orderCount *
        currentOrder < p) :
    (orderCount : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let coefficient : ℕ :=
    corvajaZannierCorollaryTwoSafeCoefficient * orderCount
  have horderPos : (0 : ℝ) < currentOrder := by
    exact_mod_cast hcurrentOrder
  have horderNonneg : (0 : ℝ) ≤ currentOrder := horderPos.le
  have hcoefficientNonneg : (0 : ℝ) ≤ coefficient := by positivity
  have hcubeReal : (coefficient : ℝ) ^ (3 : ℕ) <
      (currentOrder : ℝ) := by
    dsimp [coefficient]
    exact_mod_cast hcube
  have hcoefficientRoot :
      (coefficient : ℝ) < (currentOrder : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := (Real.lt_rpow_inv_iff_of_pos hcoefficientNonneg horderNonneg
      (by norm_num : (0 : ℝ) < 3)).2
    have h' : (coefficient : ℝ) <
        (currentOrder : ℝ) ^ (3 : ℝ)⁻¹ :=
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
      (coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) <
        (currentOrder : ℝ) := by
    calc
      (coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)) <
          (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^
              ((1 : ℝ) / 3)) :=
        mul_lt_mul_of_pos_right hcoefficientRoot hrootPositive
      _ = (currentOrder : ℝ) := hcubeRootIdentity
  have hlinearReal :
      (coefficient : ℝ) * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp [coefficient]
    exact_mod_cast hlinear
  have hpPos : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hquotientTerm :
      (coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) <
        (currentOrder : ℝ) := by
    have hratio :
        (coefficient : ℝ) * (currentOrder : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hpPos).2 hlinearReal
    calc
      (coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) =
          ((coefficient : ℝ) * (currentOrder : ℝ) / (p : ℝ)) *
            (currentOrder : ℝ) := by
        push_cast
        ring
      _ < 1 * (currentOrder : ℝ) :=
        mul_lt_mul_of_pos_right hratio horderPos
      _ = (currentOrder : ℝ) := one_mul _
  calc
    (orderCount : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder =
        (coefficient : ℝ) * max
          ((((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)))
          ((((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) := by
      simp only [corvajaZannierCurrentOrderEnvelope]
      dsimp [coefficient]
      push_cast
      ring
    _ = max
        ((coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^
            ((1 : ℝ) / 3)))
        ((coefficient : ℝ) *
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) :=
      mul_max_of_nonneg _ _ hcoefficientNonneg
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

/-- The finite weighted Corvaja--Zannier escape step over maximal candidate
orders only. -/
theorem exists_left_element_escaping_of_weightedCorvajaZannierEstimate_maximalOrders
    (p : ℕ) (alpha beta : E) (Hleft : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder :
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        Nat.card (rightSubgroup d) = d)
    (hCZ : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        ((weightedTraceEquationSolutions alpha beta Hleft
          (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card Hleft)
            (Nat.card (rightSubgroup d)))
    (hnondegenerate : alpha * beta ≠ 1)
    (hcurrentOrder : 0 < Nat.card Hleft)
    (hp : 1 < p)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (Nat.card Hleft)).card) ^ 3 <
          Nat.card Hleft)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        (middleGameMaximalOrders p (Nat.card Hleft)).card *
          Nat.card Hleft < p) :
    ∃ hleft : Hleft,
      ∀ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
        ∀ hright : rightSubgroup d,
          weightedSplitTorusTrace alpha beta hleft ≠
            splitTorusTrace hright := by
  classical
  let orders := middleGameMaximalOrders p (Nat.card Hleft)
  let bad :=
    weightedBadOrderTraceSupport alpha beta Hleft orders rightSubgroup
  have hCZIndexed : ∀ d ∈ orders,
      ((weightedTraceEquationSolutions alpha beta Hleft
        (rightSubgroup d)).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card Hleft) d := by
    intro d hd
    have hd' : d ∈ middleGameMaximalOrders p (Nat.card Hleft) := by
      simpa [orders] using hd
    have hEstimate := hCZ hnondegenerate d hd'
    rw [hrightOrder d hd'] at hEstimate
    exact hEstimate
  have hbadReal : (bad.card : ℝ) < (Nat.card Hleft : ℝ) := by
    calc
      (bad.card : ℝ) ≤
          ∑ d ∈ orders,
            corvajaZannierTraceUpperBound p (Nat.card Hleft) d := by
        exact weightedBadOrderTraceSupport_card_cast_le_sum
          alpha beta Hleft orders rightSubgroup _ hCZIndexed
      _ ≤ ((middleGameMaximalOrders p (Nat.card Hleft)).card : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card Hleft) := by
        simpa [orders] using
          middleGameMaximalCorvajaZannierSum_le_card_mul_envelope
            p (Nat.card Hleft) hp
      _ < (Nat.card Hleft : ℝ) :=
        orderCount_mul_corvajaZannierEnvelope_lt_currentOrder
          p (Nat.card Hleft)
            (middleGameMaximalOrders p (Nat.card Hleft)).card
          hcurrentOrder hcube hlinear
  have hbad : bad.card < Nat.card Hleft := by
    exact_mod_cast hbadReal
  have hexists : ∃ hleft : Hleft, hleft ∉ bad := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset Hleft).card ≤ bad.card :=
      Finset.card_le_card fun hleft _ ↦ hall hleft
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hbad) hle
  obtain ⟨hleft, hleftNotBad⟩ := hexists
  refine ⟨hleft, ?_⟩
  intro d hd hright heq
  apply hleftNotBad
  exact mem_weightedBadOrderTraceSupport_iff.mpr
    ⟨d, by simpa [orders] using hd, hright, heq⟩

end BGS.Markoff
