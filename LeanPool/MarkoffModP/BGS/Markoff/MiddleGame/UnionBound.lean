/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.TraceEquation
public import LeanPool.MarkoffModP.BGS.NumberTheory.DivisorBound

/-!
# The middle-game bad-order union

The published middle game considers, for a left rotation group `H₁`, every possible right
rotation order `d ≤ |H₁|` dividing `p - 1` or `p + 1`.  A power-saving estimate for the
trace equation bounds the left elements that can meet a right subgroup of each such order.  The
divisor bound then makes the union of all those exceptional left elements smaller than `H₁`.

This file formalizes that finite combinatorial wiring.  It deliberately does not postulate the
Corvaja--Zannier estimate: the estimate appears below as an ordinary theorem hypothesis on the
actual trace-equation solution finsets.
-/

@[expose] public section

namespace BGS.Markoff

/-- Candidate right rotation orders in the middle game: divisors of `p - 1` or `p + 1` that do
not exceed the current left rotation order. -/
def middleGameCandidateOrders (p currentOrder : ℕ) : Finset ℕ :=
  ((p - 1).divisors ∪ (p + 1).divisors).filter fun d ↦ d ≤ currentOrder

theorem mem_middleGameCandidateOrders_iff {p currentOrder d : ℕ} :
    d ∈ middleGameCandidateOrders p currentOrder ↔
      d ≤ currentOrder ∧ (d ∣ p - 1 ∧ p - 1 ≠ 0 ∨ d ∣ p + 1) := by
  simp only [middleGameCandidateOrders, Finset.mem_filter, Finset.mem_union,
    Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hle⟩
    refine ⟨hle, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr hd.1
  · rintro ⟨hle, hd⟩
    refine ⟨?_, hle⟩
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨hd, by omega⟩

/-- There are no more candidate orders than the sum of the two divisor counts. -/
theorem middleGameCandidateOrders_card_le (p currentOrder : ℕ) :
    (middleGameCandidateOrders p currentOrder).card ≤
      (p - 1).divisors.card + (p + 1).divisors.card := by
  calc
    (middleGameCandidateOrders p currentOrder).card ≤
        ((p - 1).divisors ∪ (p + 1).divisors).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (p - 1).divisors.card + (p + 1).divisors.card := Finset.card_union_le _ _

/-- The proved subpolynomial divisor estimate controls both possible torus orders at once.  This
is the analytic input needed after taking the finite union over candidate right rotation orders. -/
theorem exists_threshold_middleGameCandidateOrders_card_le_two_mul_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold : ℕ, ∀ p currentOrder : ℕ, threshold ≤ p →
      ((middleGameCandidateOrders p currentOrder).card : ℝ) ≤
        2 * ((p + 1 : ℕ) : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := BGS.NumberTheory.exists_threshold_card_divisors_le_rpow hε
  refine ⟨N + 1, ?_⟩
  intro p currentOrder hp
  have hpMinus : N ≤ p - 1 := by omega
  have hpPlus : N ≤ p + 1 := by omega
  have hMinus := hN (p - 1) hpMinus
  have hPlus := hN (p + 1) hpPlus
  have hCandidate :
      ((middleGameCandidateOrders p currentOrder).card : ℝ) ≤
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast middleGameCandidateOrders_card_le p currentOrder
  have hBase : (((p - 1 : ℕ) : ℝ)) ≤ (((p + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show p - 1 ≤ p + 1 by omega)
  have hPower : (((p - 1 : ℕ) : ℝ)) ^ ε ≤ (((p + 1 : ℕ) : ℝ)) ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hBase hε.le
  calc
    ((middleGameCandidateOrders p currentOrder).card : ℝ) ≤
        (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) := hCandidate
    _ = ((p - 1).divisors.card : ℝ) + ((p + 1).divisors.card : ℝ) := by
      norm_num
    _ ≤ (((p - 1 : ℕ) : ℝ)) ^ ε + (((p + 1 : ℕ) : ℝ)) ^ ε :=
      add_le_add hMinus hPlus
    _ ≤ (((p + 1 : ℕ) : ℝ)) ^ ε + (((p + 1 : ℕ) : ℝ)) ^ ε :=
      add_le_add hPower (le_refl _)
    _ = 2 * (((p + 1 : ℕ) : ℝ)) ^ ε := by ring

variable {E : Type*} [Field E] [Fintype E]

/-- Left elements of `H₁` occurring in the trace equation with some element of `H₂`. -/
noncomputable def traceEquationLeftSupport
    (sigma : E) (H₁ H₂ : Subgroup Eˣ) : Finset H₁ := by
  classical
  exact (traceEquationSolutions sigma H₁ H₂).image Prod.fst

@[simp]
theorem mem_traceEquationLeftSupport_iff
    {sigma : E} {H₁ H₂ : Subgroup Eˣ} {h₁ : H₁} :
    h₁ ∈ traceEquationLeftSupport sigma H₁ H₂ ↔
      ∃ h₂ : H₂, twistedUnitTrace sigma h₁ = twistedUnitTrace 1 h₂ := by
  classical
  simp only [traceEquationLeftSupport, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, (mem_traceEquationSolutions_iff.mp hh)⟩
  · rintro ⟨h₂, heq⟩
    exact ⟨(h₁, h₂), mem_traceEquationSolutions_iff.mpr heq, rfl⟩

/-- Projection to the left coordinate cannot increase the number of trace-equation solutions. -/
theorem traceEquationLeftSupport_card_le_solutions
    (sigma : E) (H₁ H₂ : Subgroup Eˣ) :
    (traceEquationLeftSupport sigma H₁ H₂).card ≤
      (traceEquationSolutions sigma H₁ H₂).card := by
  classical
  exact Finset.card_image_le

/-- The safe coefficient obtained from Corvaja--Zannier, Corollary 2, after specializing its
explicit constants to the middle-game trace curve. -/
def corvajaZannierCorollaryTwoSafeCoefficient : ℕ := 48

/-- The numerical right-hand side of the Corvaja--Zannier trace estimate used in the published
paper, with the source-justified safe coefficient from Corollary 2 kept explicit. -/
noncomputable def corvajaZannierTraceUpperBound
    (p leftOrder rightOrder : ℕ) : ℝ :=
  corvajaZannierCorollaryTwoSafeCoefficient * max
    (((leftOrder * rightOrder : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (((leftOrder * rightOrder : ℕ) : ℝ) / p)

/-- All left elements that meet at least one member of a supplied family of right subgroups. -/
noncomputable def badOrderTraceSupport
    (sigma : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) : Finset H₁ := by
  classical
  exact orders.biUnion fun d ↦ traceEquationLeftSupport sigma H₁ (rightSubgroup d)

@[simp]
theorem mem_badOrderTraceSupport_iff
    {sigma : E} {H₁ : Subgroup Eˣ} {orders : Finset ℕ}
    {rightSubgroup : ℕ → Subgroup Eˣ} {h₁ : H₁} :
    h₁ ∈ badOrderTraceSupport sigma H₁ orders rightSubgroup ↔
      ∃ d ∈ orders, ∃ h₂ : rightSubgroup d,
        twistedUnitTrace sigma h₁ = twistedUnitTrace 1 h₂ := by
  classical
  simp [badOrderTraceSupport]

/-- A uniform bound for each trace-equation solution set gives the expected finite-union bound. -/
theorem badOrderTraceSupport_card_le
    (sigma : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ orders,
      (traceEquationSolutions sigma H₁ (rightSubgroup d)).card ≤ bound) :
    (badOrderTraceSupport sigma H₁ orders rightSubgroup).card ≤ orders.card * bound := by
  classical
  unfold badOrderTraceSupport
  apply Finset.card_biUnion_le_card_mul
  intro d hd
  exact (traceEquationLeftSupport_card_le_solutions sigma H₁ (rightSubgroup d)).trans
    (hbound d hd)

/-- A nonuniform real-valued estimate for the individual trace equations sums over the candidate
orders.  This form accepts the quoted Corvaja--Zannier bound without rounding it to a natural
number. -/
theorem badOrderTraceSupport_card_cast_le_sum
    (sigma : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ → ℝ)
    (hbound : ∀ d ∈ orders,
      ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) ≤ bound d) :
    ((badOrderTraceSupport sigma H₁ orders rightSubgroup).card : ℝ) ≤
      ∑ d ∈ orders, bound d := by
  classical
  calc
    ((badOrderTraceSupport sigma H₁ orders rightSubgroup).card : ℝ) ≤
        ∑ d ∈ orders, ((traceEquationLeftSupport sigma H₁ (rightSubgroup d)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (badOrderTraceSupport sigma H₁ orders rightSubgroup).card ≤
          ∑ d ∈ orders, (traceEquationLeftSupport sigma H₁ (rightSubgroup d)).card)
    _ ≤ ∑ d ∈ orders,
        ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) := by
      exact Finset.sum_le_sum fun d _ ↦ by
        exact_mod_cast traceEquationLeftSupport_card_le_solutions sigma H₁ (rightSubgroup d)
    _ ≤ ∑ d ∈ orders, bound d := Finset.sum_le_sum hbound

/-- Direct wiring of the quoted Corvaja--Zannier estimate into the finite bad-order union.  The
deep estimate is the explicit hypothesis `hCZ`; this theorem proves only its combinatorial use. -/
theorem middleGameBadOrderTraceSupport_card_cast_le_corvajaZannierSum
    (p : ℕ) (sigma : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hCZ : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ((traceEquationSolutions sigma H₁ (rightSubgroup d)).card : ℝ) ≤
        corvajaZannierTraceUpperBound p (Nat.card H₁) d) :
    ((badOrderTraceSupport sigma H₁ (middleGameCandidateOrders p (Nat.card H₁))
      rightSubgroup).card : ℝ) ≤
        ∑ d ∈ middleGameCandidateOrders p (Nat.card H₁),
          corvajaZannierTraceUpperBound p (Nat.card H₁) d :=
  badOrderTraceSupport_card_cast_le_sum sigma H₁ _ rightSubgroup _ hCZ

/-- The published bad-order union bound, with the deep estimate exposed as a bound on each actual
trace-equation solution set. -/
theorem middleGameBadOrderTraceSupport_card_le
    (p : ℕ) (sigma : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      (traceEquationSolutions sigma H₁ (rightSubgroup d)).card ≤ bound) :
    (badOrderTraceSupport sigma H₁ (middleGameCandidateOrders p (Nat.card H₁))
      rightSubgroup).card ≤
        ((p - 1).divisors.card + (p + 1).divisors.card) * bound := by
  calc
    (badOrderTraceSupport sigma H₁ (middleGameCandidateOrders p (Nat.card H₁))
        rightSubgroup).card ≤
        (middleGameCandidateOrders p (Nat.card H₁)).card * bound :=
      badOrderTraceSupport_card_le sigma H₁ _ rightSubgroup bound hbound
    _ ≤ ((p - 1).divisors.card + (p + 1).divisors.card) * bound :=
      Nat.mul_le_mul_right bound (middleGameCandidateOrders_card_le p (Nat.card H₁))

/-- If the divisor-counted union is strictly smaller than `H₁`, some left rotation element
cannot meet any right subgroup of candidate order.  This is the exact pigeonhole step used to
increase the maximal rotation order in the published middle game. -/
theorem exists_left_element_escaping_middleGameCandidateOrders
    (p : ℕ) (sigma : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      (traceEquationSolutions sigma H₁ (rightSubgroup d)).card ≤ bound)
    (hsmall : ((p - 1).divisors.card + (p + 1).divisors.card) * bound < Nat.card H₁) :
    ∃ h₁ : H₁, ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ∀ h₂ : rightSubgroup d,
        twistedUnitTrace sigma h₁ ≠ twistedUnitTrace 1 h₂ := by
  classical
  let bad := badOrderTraceSupport sigma H₁
    (middleGameCandidateOrders p (Nat.card H₁)) rightSubgroup
  have hbad : bad.card < Nat.card H₁ :=
    (middleGameBadOrderTraceSupport_card_le p sigma H₁ rightSubgroup bound hbound).trans_lt
      hsmall
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
  exact mem_badOrderTraceSupport_iff.mpr ⟨d, hd, h₂, heq⟩

end BGS.Markoff
