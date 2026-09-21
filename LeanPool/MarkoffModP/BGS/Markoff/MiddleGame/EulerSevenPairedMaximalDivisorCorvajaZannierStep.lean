/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.MaximalDivisorNonparabolicOrderCover
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.NonparabolicUnionBound
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.EulerSevenPairedCorvajaZannierBound
import Mathlib.Tactic

/-!
# Euler-seven paired escape over maximal candidate orders

The exact χ≤7 paired bound gives two sufficient inequalities:

* `189 * K^3 < currentOrder`;
* `24 * K * currentOrder < p`.

Here `K` is the number of divisibility-maximal candidate orders. The first
coefficient is exact: it is the cube of the paired χ≤7 root coefficient.
-/

namespace BGS.Markoff

noncomputable section

variable {E : Type*} [Field E] [Fintype E]

private theorem rpow_one_third_cube_eulerSeven {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

/-- A common χ≤7 paired bound for every candidate right order at most the
current left order. -/
def pairedEulerSevenCurrentOrderEnvelope
    (p currentOrder : ℕ) : ℝ :=
  max
    ((3 / 2 : ℝ) *
      (56 * ((currentOrder * currentOrder : ℕ) : ℝ)) ^
        ((1 : ℝ) / 3))
    (24 * (((currentOrder * currentOrder : ℕ) : ℝ) / p))

theorem pairedEulerSevenTraceUpperBound_le_currentOrderEnvelope
    (p currentOrder d : ℕ) (hd : d ≤ currentOrder) :
    pairedEulerSevenCorvajaZannierTraceUpperBound p currentOrder d ≤
      pairedEulerSevenCurrentOrderEnvelope p currentOrder := by
  have hmulNat : currentOrder * d ≤ currentOrder * currentOrder :=
    Nat.mul_le_mul_left currentOrder hd
  have hmul : (((currentOrder * d : ℕ) : ℝ)) ≤
      (((currentOrder * currentOrder : ℕ) : ℝ)) := by
    exact_mod_cast hmulNat
  unfold pairedEulerSevenCorvajaZannierTraceUpperBound
    pairedEulerSevenCurrentOrderEnvelope
  exact max_le_max
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow
        (by positivity : (0 : ℝ) ≤ 56 * ((currentOrder * d : ℕ) : ℝ))
        (mul_le_mul_of_nonneg_left hmul (by norm_num))
        (by norm_num))
      (by norm_num))
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hmul (Nat.cast_nonneg p))
      (by norm_num))

theorem
    middleGameMaximalPairedEulerSevenSum_le_card_mul_envelope
    (p currentOrder : ℕ) (hp : 1 < p) :
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        pairedEulerSevenCorvajaZannierTraceUpperBound
          p currentOrder d) ≤
      ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        pairedEulerSevenCurrentOrderEnvelope p currentOrder := by
  classical
  calc
    (∑ d ∈ middleGameMaximalOrders p currentOrder,
        pairedEulerSevenCorvajaZannierTraceUpperBound
          p currentOrder d) ≤
        ∑ _d ∈ middleGameMaximalOrders p currentOrder,
          pairedEulerSevenCurrentOrderEnvelope p currentOrder := by
      exact Finset.sum_le_sum fun d hd ↦
        pairedEulerSevenTraceUpperBound_le_currentOrderEnvelope
          p currentOrder d
          (mem_middleGameCandidateOrders_iff.mp
            (middleGameMaximalOrders_subset_candidateOrders hp hd)).1
    _ = ((middleGameMaximalOrders p currentOrder).card : ℝ) *
        pairedEulerSevenCurrentOrderEnvelope p currentOrder := by
      simp

/-- The exact coefficient-`189` cube condition and the coefficient-`24`
linear condition make the whole maximal-order envelope smaller than the
current order. -/
theorem orderCount_mul_pairedEulerSevenEnvelope_lt_currentOrder
    (p currentOrder orderCount : ℕ)
    (hcurrentOrder : 0 < currentOrder)
    (hcube : 189 * orderCount ^ 3 < currentOrder)
    (hlinear : 24 * orderCount * currentOrder < p) :
    (orderCount : ℝ) *
        pairedEulerSevenCurrentOrderEnvelope p currentOrder <
      (currentOrder : ℝ) := by
  let rootTerm : ℝ :=
    (orderCount : ℝ) * ((3 / 2 : ℝ) *
      (56 * ((currentOrder * currentOrder : ℕ) : ℝ)) ^
        ((1 : ℝ) / 3))
  let linearCoefficient : ℝ := 24 * orderCount
  have horderPos : (0 : ℝ) < currentOrder := by
    exact_mod_cast hcurrentOrder
  have hradicand :
      (0 : ℝ) ≤
        56 * ((currentOrder * currentOrder : ℕ) : ℝ) := by
    positivity
  have hrootCube :
      ((56 * ((currentOrder * currentOrder : ℕ) : ℝ)) ^
        ((1 : ℝ) / 3)) ^ (3 : ℕ) =
          56 * ((currentOrder * currentOrder : ℕ) : ℝ) :=
    rpow_one_third_cube_eulerSeven hradicand
  have hrootTermCube :
      rootTerm ^ 3 =
        189 * (orderCount : ℝ) ^ 3 * (currentOrder : ℝ) ^ 2 := by
    dsimp only [rootTerm]
    rw [mul_pow, mul_pow, hrootCube]
    push_cast
    ring
  have hcubeScaledNat :
      189 * orderCount ^ 3 * currentOrder ^ 2 <
        currentOrder ^ 3 := by
    have h :=
      Nat.mul_lt_mul_of_pos_right hcube
        (show 0 < currentOrder ^ 2 from Nat.pow_pos hcurrentOrder)
    simpa [pow_succ, mul_assoc] using h
  have hcubeScaled :
      189 * (orderCount : ℝ) ^ 3 * (currentOrder : ℝ) ^ 2 <
        (currentOrder : ℝ) ^ 3 := by
    exact_mod_cast hcubeScaledNat
  have hrootTerm : rootTerm < (currentOrder : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (Nat.cast_nonneg currentOrder)
    rw [hrootTermCube]
    exact hcubeScaled
  have hlinearReal :
      linearCoefficient * (currentOrder : ℝ) < (p : ℝ) := by
    dsimp only [linearCoefficient]
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
        pairedEulerSevenCurrentOrderEnvelope p currentOrder =
        max rootTerm
          (linearCoefficient *
            (((currentOrder * currentOrder : ℕ) : ℝ) / (p : ℝ))) := by
      rw [pairedEulerSevenCurrentOrderEnvelope,
        mul_max_of_nonneg _ _ (Nat.cast_nonneg orderCount)]
      dsimp only [rootTerm, linearCoefficient]
      push_cast
      congr 1 <;> ring
    _ < (currentOrder : ℝ) := max_lt hrootTerm hquotientTerm

/-- Finite nonparabolic escape over maximal candidate orders with the exact
χ≤7 cube coefficient `189`. -/
theorem exists_left_element_escaping_nonparabolic_maximalOrders_eulerSeven
    (p : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [CharP E p]
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
      189 * (middleGameMaximalOrders p (Nat.card Hleft)).card ^ 3 <
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
    fun d ↦ pairedEulerSevenCorvajaZannierTraceUpperBound
      p (Nat.card Hleft) d
  have hbound :
      ∀ d ∈ orders,
        ((weightedTraceEquationNonparabolicLeftSupport
          alpha beta Hleft (rightSubgroup d)).card : ℝ) ≤ bound d := by
    intro d hd
    have hd' : d ∈ middleGameMaximalOrders p (Nat.card Hleft) := by
      simpa [orders] using hd
    have h :=
      weightedTraceEquationNonparabolicLeftSupport_card_cast_le_pairedEulerSeven
        p E alpha beta Hleft (rightSubgroup d) hadmissible
    rw [hrightOrder d hd'] at h
    simpa [bound] using h
  have hsmall : (∑ d ∈ orders, bound d) < (Nat.card Hleft : ℝ) := by
    calc
      (∑ d ∈ orders, bound d) =
          ∑ d ∈ middleGameMaximalOrders p (Nat.card Hleft),
            pairedEulerSevenCorvajaZannierTraceUpperBound
              p (Nat.card Hleft) d := by
        simp [orders, bound]
      _ ≤ ((middleGameMaximalOrders p (Nat.card Hleft)).card : ℝ) *
          pairedEulerSevenCurrentOrderEnvelope
            p (Nat.card Hleft) :=
        middleGameMaximalPairedEulerSevenSum_le_card_mul_envelope
          p (Nat.card Hleft) hp
      _ < (Nat.card Hleft : ℝ) :=
        orderCount_mul_pairedEulerSevenEnvelope_lt_currentOrder
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
