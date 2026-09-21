/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.UnionBound

/-!
# The Corvaja--Zannier middle-game escape step

This module connects the published Corvaja--Zannier estimate to the already formalized
bad-order union.  The deep estimate remains an explicit hypothesis about the actual
trace-equation solution sets.  Two details that are easy to lose in an abstract union bound
are kept in the statement:

* `sigma != 1`, as required in equation (62) of the published paper;
* the subgroup indexed by `d` must actually have cardinality `d`.

The theorem below reduces the paper-specific order-increase step to one visible numerical
inequality.  It does not postulate the Corvaja--Zannier theorem.
-/

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

/-- A common Corvaja--Zannier bound for every candidate order not exceeding the current order. -/
noncomputable def corvajaZannierCurrentOrderEnvelope
    (p currentOrder : ℕ) : ℝ :=
  corvajaZannierCorollaryTwoSafeCoefficient * max
    (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (((currentOrder * currentOrder : ℕ) : ℝ) / p)

/-- Replacing a candidate right order by the current left order only enlarges the quoted
Corvaja--Zannier bound. -/
theorem corvajaZannierTraceUpperBound_le_currentOrderEnvelope
    (p currentOrder d : ℕ) (hd : d ≤ currentOrder) :
    corvajaZannierTraceUpperBound p currentOrder d ≤
      corvajaZannierCurrentOrderEnvelope p currentOrder := by
  have hmulNat : currentOrder * d ≤ currentOrder * currentOrder :=
    Nat.mul_le_mul_left currentOrder hd
  have hmul : (((currentOrder * d : ℕ) : ℝ)) ≤
      (((currentOrder * currentOrder : ℕ) : ℝ)) := by
    exact_mod_cast hmulNat
  unfold corvajaZannierTraceUpperBound corvajaZannierCurrentOrderEnvelope
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le_max
    (Real.rpow_le_rpow (by positivity) hmul (by norm_num))
    (div_le_div_of_nonneg_right hmul (Nat.cast_nonneg p))

/-- The summed Corvaja--Zannier expression is bounded by the divisor count times the common
current-order envelope. -/
theorem middleGameCorvajaZannierSum_le_divisorCount_mul_envelope
    (p currentOrder : ℕ) :
    (∑ d ∈ middleGameCandidateOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder := by
  classical
  calc
    (∑ d ∈ middleGameCandidateOrders p currentOrder,
        corvajaZannierTraceUpperBound p currentOrder d) ≤
        ∑ _d ∈ middleGameCandidateOrders p currentOrder,
          corvajaZannierCurrentOrderEnvelope p currentOrder := by
      exact Finset.sum_le_sum fun d hd ↦
        corvajaZannierTraceUpperBound_le_currentOrderEnvelope p currentOrder d
          (mem_middleGameCandidateOrders_iff.mp hd).1
    _ = ((middleGameCandidateOrders p currentOrder).card : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder := by
      simp
    _ ≤ (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder := by
      apply mul_le_mul_of_nonneg_right _ (by
        unfold corvajaZannierCurrentOrderEnvelope
        positivity)
      exact_mod_cast middleGameCandidateOrders_card_le p currentOrder

/-- Two elementary natural-number inequalities imply that the entire divisor-counted
Corvaja--Zannier envelope is smaller than the current order.  Writing
`D = tau(p - 1) + tau(p + 1)`, these are exactly

* `(48 D)^3 < currentOrder` for the cube-root term, and
* `48 D * currentOrder < p` for the term divided by `p`.

Thus the remaining asymptotic work is reduced to the proved subpolynomial divisor bound and
the chosen middle-game range for `currentOrder`. -/
theorem divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder
    (p currentOrder : ℕ) (hcurrentOrder : 0 < currentOrder)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < currentOrder)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * currentOrder < p) :
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let divisorCount : ℕ := (p - 1).divisors.card + (p + 1).divisors.card
  let coefficient : ℝ := corvajaZannierCorollaryTwoSafeCoefficient * divisorCount
  have horderPos : (0 : ℝ) < currentOrder := by exact_mod_cast hcurrentOrder
  have horderNonneg : (0 : ℝ) ≤ currentOrder := horderPos.le
  have hcoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hcubeReal : coefficient ^ (3 : ℕ) < (currentOrder : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hcube
  have hcoefficientRoot :
      coefficient < (currentOrder : ℝ) ^ ((1 : ℝ) / 3) := by
    have h := (Real.lt_rpow_inv_iff_of_pos hcoefficientNonneg horderNonneg
      (by norm_num : (0 : ℝ) < 3)).2
    have h' : coefficient < (currentOrder : ℝ) ^ (3 : ℝ)⁻¹ :=
      h (by simpa [Real.rpow_natCast] using hcubeReal)
    simpa only [one_div] using h'
  have hrootPositive :
      0 < (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
    positivity
  have hcubeRootIdentity :
      (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) =
        (currentOrder : ℝ) := by
    rw [Nat.cast_mul]
    rw [← Real.mul_rpow horderNonneg (mul_nonneg horderNonneg horderNonneg)]
    convert Real.pow_rpow_inv_natCast horderNonneg
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    all_goals ring_nf
  have hrootTerm :
      coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) <
        (currentOrder : ℝ) := by
    calc
      coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) <
          (currentOrder : ℝ) ^ ((1 : ℝ) / 3) *
            (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) :=
        mul_lt_mul_of_pos_right hcoefficientRoot hrootPositive
      _ = (currentOrder : ℝ) := hcubeRootIdentity
  have hlinearReal : coefficient * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp [coefficient, divisorCount]
    exact_mod_cast hlinear
  have hpPos : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hquotientTerm :
      coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) <
        (currentOrder : ℝ) := by
    have hratio : coefficient * (currentOrder : ℝ) / (p : ℝ) < 1 :=
      (div_lt_one hpPos).2 hlinearReal
    calc
      coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) =
          (coefficient * (currentOrder : ℝ) / (p : ℝ)) * (currentOrder : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ < 1 * (currentOrder : ℝ) := mul_lt_mul_of_pos_right hratio horderPos
      _ = (currentOrder : ℝ) := one_mul _
  calc
    (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p currentOrder =
        coefficient * max
          (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
          (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ)) := by
      simp only [corvajaZannierCurrentOrderEnvelope]
      dsimp [coefficient, divisorCount]
      ring
    _ = max
        (coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3)))
        (coefficient * (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) :=
      mul_max_of_nonneg _ _ hcoefficientNonneg
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

/-- The paper's middle-game pigeonhole step, now fed by the real-valued Corvaja--Zannier
estimate.  The estimate is stated using the actual subgroup cardinality, and `hrightOrder`
performs the indispensable identification of that cardinality with the divisor `d` indexing the
union.

The sole remaining numerical premise is exactly the inequality needed after summing over all
candidate orders. -/
theorem exists_left_element_escaping_of_corvajaZannierEstimate
    (p : ℕ) (sigma : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      Nat.card (rightSubgroup d) = d)
    (hCZ : sigma ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (rightSubgroup d)))
    (hsigma : sigma ≠ 1)
    (hsmall :
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H₁) <
        (Nat.card H₁ : ℝ)) :
    ∃ h₁ : H₁, ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ∀ h₂ : rightSubgroup d,
        twistedUnitTrace sigma h₁ ≠ twistedUnitTrace 1 h₂ := by
  classical
  let orders := middleGameCandidateOrders p (Nat.card H₁)
  let bad := badOrderTraceSupport sigma H₁ orders rightSubgroup
  have hCZIndexed : ∀ d ∈ orders,
      ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card H₁) d := by
    intro d hd
    have hd' : d ∈ middleGameCandidateOrders p (Nat.card H₁) := by
      simpa [orders] using hd
    have hEstimate := hCZ hsigma d hd'
    rw [hrightOrder d hd'] at hEstimate
    exact hEstimate
  have hbadReal : (bad.card : ℝ) < (Nat.card H₁ : ℝ) := by
    calc
      (bad.card : ℝ) ≤
          ∑ d ∈ orders, corvajaZannierTraceUpperBound p (Nat.card H₁) d := by
        exact badOrderTraceSupport_card_cast_le_sum sigma H₁ orders rightSubgroup _ hCZIndexed
      _ ≤ (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
          corvajaZannierCurrentOrderEnvelope p (Nat.card H₁) := by
        simpa [orders] using
          middleGameCorvajaZannierSum_le_divisorCount_mul_envelope p (Nat.card H₁)
      _ < (Nat.card H₁ : ℝ) := hsmall
  have hbad : bad.card < Nat.card H₁ := by exact_mod_cast hbadReal
  have hexists : ∃ h₁ : H₁, h₁ ∉ bad := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset H₁).card ≤ bad.card :=
      Finset.card_le_card fun h₁ _ ↦ hall h₁
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hbad) hle
  obtain ⟨h₁, hh₁⟩ := hexists
  refine ⟨h₁, ?_⟩
  intro d hd h₂ heq
  apply hh₁
  exact mem_badOrderTraceSupport_iff.mpr ⟨d, by simpa [orders] using hd, h₂, heq⟩

/-- A fully finite version of the paper's Corvaja--Zannier order-escape step.  Apart from the
deep estimate itself, its hypotheses are natural-number cardinality and size inequalities. -/
theorem exists_left_element_escaping_of_corvajaZannierEstimate_and_sizeBounds
    (p : ℕ) (sigma : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      Nat.card (rightSubgroup d) = d)
    (hCZ : sigma ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (rightSubgroup d)))
    (hsigma : sigma ≠ 1)
    (hcurrentOrder : 0 < Nat.card H₁)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < Nat.card H₁)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * Nat.card H₁ < p) :
    ∃ h₁ : H₁, ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ∀ h₂ : rightSubgroup d,
        twistedUnitTrace sigma h₁ ≠ twistedUnitTrace 1 h₂ := by
  exact exists_left_element_escaping_of_corvajaZannierEstimate p sigma H₁ rightSubgroup
    hrightOrder hCZ hsigma
      (divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder p (Nat.card H₁)
        hcurrentOrder hcube hlinear)

end BGS.Markoff
