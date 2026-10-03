/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierStep
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry

/-!
# The weighted middle-game trace equation

An arbitrary Markoff rotation orbit produces the equation

`alpha * h₁ + beta / h₁ = h₂ + 1 / h₂`,

with `h₁` in the cyclic rotation subgroup.  This module formalizes its finite solution sets,
the elementary quadratic-fiber bound, and the complete bad-order union and pigeonhole reduction.
The deep weighted Corvaja--Zannier estimate is an explicit theorem hypothesis; it is not encoded
as an axiom, class, or structure field.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

variable {E : Type*} [Field E] [Fintype E]

/-- The possible left subgroup elements above one fixed right trace in the weighted equation. -/
noncomputable def weightedTraceEquationLeftFiber
    (alpha beta : E) (H₁ : Subgroup Eˣ) (h₂ : Eˣ) : Finset H₁ := by
  classical
  exact Finset.univ.filter fun h₁ ↦
    weightedSplitTorusTrace alpha beta h₁ = splitTorusTrace h₂

/-- Solutions of the weighted middle-game trace equation inside two finite subgroups. -/
noncomputable def weightedTraceEquationSolutions
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) : Finset (H₁ × H₂) := by
  classical
  exact Finset.univ.biUnion fun h₂ : H₂ ↦
    (weightedTraceEquationLeftFiber alpha beta H₁ h₂).image fun h₁ ↦ (h₁, h₂)

@[simp]
theorem mem_weightedTraceEquationSolutions_iff
    {alpha beta : E} {H₁ H₂ : Subgroup Eˣ} {h : H₁ × H₂} :
    h ∈ weightedTraceEquationSolutions alpha beta H₁ H₂ ↔
      weightedSplitTorusTrace alpha beta h.1 = splitTorusTrace h.2 := by
  classical
  constructor
  · intro hh
    rw [weightedTraceEquationSolutions, Finset.mem_biUnion] at hh
    obtain ⟨h₂, _, hh⟩ := hh
    obtain ⟨h₁, hh₁, heq⟩ := Finset.mem_image.mp hh
    have hfirst : h₁ = h.1 := congrArg Prod.fst heq
    have hsecond : h₂ = h.2 := congrArg Prod.snd heq
    simpa [weightedTraceEquationLeftFiber, hfirst, hsecond] using hh₁
  · intro hh
    rw [weightedTraceEquationSolutions, Finset.mem_biUnion]
    refine ⟨h.2, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr
      ⟨h.1, by simpa [weightedTraceEquationLeftFiber] using hh, rfl⟩

omit [Fintype E] in
/-- Dividing the weighted equation by its nonzero leading weight gives the monic twisted-trace
equation used by the existing quadratic polynomial API. -/
theorem weightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
    (alpha beta trace : E) (h : Eˣ) (halpha : alpha ≠ 0) :
    weightedSplitTorusTrace alpha beta h = trace ↔
      twistedUnitTrace (beta / alpha) h = trace / alpha := by
  simp only [weightedSplitTorusTrace, twistedUnitTrace]
  have hh : (h : E) ≠ 0 := Units.ne_zero h
  field_simp [halpha, hh]

/-- For a fixed right-hand trace, at most two left subgroup elements solve the weighted
equation when the leading weight is nonzero. -/
theorem weightedTraceEquationLeftFiber_card_le_two
    (alpha beta : E) (H₁ : Subgroup Eˣ) (h₂ : Eˣ) (halpha : alpha ≠ 0) :
    (weightedTraceEquationLeftFiber alpha beta H₁ h₂).card ≤ 2 := by
  classical
  let f := twistedTracePolynomial (beta / alpha) (splitTorusTrace h₂ / alpha)
  have hf : f ≠ 0 := (twistedTracePolynomial_monic (beta / alpha) _).ne_zero
  let rootEmbedding : ↥(weightedTraceEquationLeftFiber alpha beta H₁ h₂) ↪
      ↥f.roots.toFinset :=
    { toFun := fun h₁ ↦ ⟨((h₁.1 : Eˣ) : E), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
        apply (eval_twistedTracePolynomial_eq_zero_iff (beta / alpha) _ h₁.1).2
        apply (weightedSplitTorusTrace_eq_iff_twistedUnitTrace_eq
          alpha beta (splitTorusTrace h₂) h₁.1 halpha).mp
        simpa only [weightedTraceEquationLeftFiber, Finset.mem_filter,
          Finset.mem_univ, true_and] using h₁.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        exact congrArg Subtype.val hxy }
  have hcard :
      (weightedTraceEquationLeftFiber alpha beta H₁ h₂).card ≤ f.roots.toFinset.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rootEmbedding rootEmbedding.injective
  calc
    (weightedTraceEquationLeftFiber alpha beta H₁ h₂).card ≤ f.roots.toFinset.card := hcard
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := twistedTracePolynomial_natDegree (beta / alpha) _

/-- The elementary weighted estimate: every right subgroup element has at most two lifts. -/
theorem weightedTraceEquationSolutions_card_le_two_mul_right
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) (halpha : alpha ≠ 0) :
    (weightedTraceEquationSolutions alpha beta H₁ H₂).card ≤ 2 * Nat.card H₂ := by
  classical
  unfold weightedTraceEquationSolutions
  calc
    (Finset.univ.biUnion fun h₂ : H₂ ↦
        (weightedTraceEquationLeftFiber alpha beta H₁ h₂).image fun h₁ ↦ (h₁, h₂)).card ≤
        Finset.univ.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro h₂ _
      exact Finset.card_image_le.trans
        (weightedTraceEquationLeftFiber_card_le_two alpha beta H₁ h₂ halpha)
    _ = 2 * Nat.card H₂ := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card]
      omega

/-- Left elements occurring in the weighted trace equation with some right subgroup element. -/
noncomputable def weightedTraceEquationLeftSupport
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) : Finset H₁ := by
  classical
  exact (weightedTraceEquationSolutions alpha beta H₁ H₂).image Prod.fst

@[simp]
theorem mem_weightedTraceEquationLeftSupport_iff
    {alpha beta : E} {H₁ H₂ : Subgroup Eˣ} {h₁ : H₁} :
    h₁ ∈ weightedTraceEquationLeftSupport alpha beta H₁ H₂ ↔
      ∃ h₂ : H₂,
        weightedSplitTorusTrace alpha beta h₁ = splitTorusTrace h₂ := by
  classical
  simp only [weightedTraceEquationLeftSupport, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, mem_weightedTraceEquationSolutions_iff.mp hh⟩
  · rintro ⟨h₂, heq⟩
    exact ⟨(h₁, h₂), mem_weightedTraceEquationSolutions_iff.mpr heq, rfl⟩

/-- Projection to the left coordinate cannot increase the weighted solution count. -/
theorem weightedTraceEquationLeftSupport_card_le_solutions
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) :
    (weightedTraceEquationLeftSupport alpha beta H₁ H₂).card ≤
      (weightedTraceEquationSolutions alpha beta H₁ H₂).card := by
  classical
  exact Finset.card_image_le

/-- Left elements meeting at least one member of an indexed family of right subgroups. -/
noncomputable def weightedBadOrderTraceSupport
    (alpha beta : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) : Finset H₁ := by
  classical
  exact orders.biUnion fun d ↦
    weightedTraceEquationLeftSupport alpha beta H₁ (rightSubgroup d)

@[simp]
theorem mem_weightedBadOrderTraceSupport_iff
    {alpha beta : E} {H₁ : Subgroup Eˣ} {orders : Finset ℕ}
    {rightSubgroup : ℕ → Subgroup Eˣ} {h₁ : H₁} :
    h₁ ∈ weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup ↔
      ∃ d ∈ orders, ∃ h₂ : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h₁ = splitTorusTrace h₂ := by
  classical
  simp [weightedBadOrderTraceSupport]

/-- A real-valued estimate for each weighted solution set sums over an arbitrary finite family
of candidate right orders. -/
theorem weightedBadOrderTraceSupport_card_cast_le_sum
    (alpha beta : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ → ℝ)
    (hbound : ∀ d ∈ orders,
      ((weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card : ℝ) ≤
        bound d) :
    ((weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup).card : ℝ) ≤
      ∑ d ∈ orders, bound d := by
  classical
  calc
    ((weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup).card : ℝ) ≤
        ∑ d ∈ orders,
          ((weightedTraceEquationLeftSupport alpha beta H₁ (rightSubgroup d)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup).card ≤
          ∑ d ∈ orders,
            (weightedTraceEquationLeftSupport alpha beta H₁ (rightSubgroup d)).card)
    _ ≤ ∑ d ∈ orders,
        ((weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card : ℝ) := by
      exact Finset.sum_le_sum fun d _ ↦ by
        exact_mod_cast weightedTraceEquationLeftSupport_card_le_solutions
          alpha beta H₁ (rightSubgroup d)
    _ ≤ ∑ d ∈ orders, bound d := Finset.sum_le_sum hbound

/-- A uniform natural-valued bound gives the corresponding weighted finite-union bound. -/
theorem weightedBadOrderTraceSupport_card_le
    (alpha beta : E) (H₁ : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ orders,
      (weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card ≤ bound) :
    (weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup).card ≤
      orders.card * bound := by
  classical
  unfold weightedBadOrderTraceSupport
  apply Finset.card_biUnion_le_card_mul
  intro d hd
  exact (weightedTraceEquationLeftSupport_card_le_solutions
    alpha beta H₁ (rightSubgroup d)).trans (hbound d hd)

/-- The published divisor-counted natural-valued weighted bad-order bound. -/
theorem middleGameWeightedBadOrderTraceSupport_card_le
    (p : ℕ) (alpha beta : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      (weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card ≤ bound) :
    (weightedBadOrderTraceSupport alpha beta H₁
      (middleGameCandidateOrders p (Nat.card H₁)) rightSubgroup).card ≤
        ((p - 1).divisors.card + (p + 1).divisors.card) * bound := by
  calc
    (weightedBadOrderTraceSupport alpha beta H₁
        (middleGameCandidateOrders p (Nat.card H₁)) rightSubgroup).card ≤
        (middleGameCandidateOrders p (Nat.card H₁)).card * bound :=
      weightedBadOrderTraceSupport_card_le alpha beta H₁ _ rightSubgroup bound hbound
    _ ≤ ((p - 1).divisors.card + (p + 1).divisors.card) * bound :=
      Nat.mul_le_mul_right bound (middleGameCandidateOrders_card_le p (Nat.card H₁))

/-- The weighted Corvaja--Zannier estimate, when supplied for each actual right subgroup,
sums to the same numerical expression as in the normalized equation.  The essential
nondegeneracy `alpha * beta != 1` is an explicit premise of the estimate. -/
theorem middleGameWeightedBadOrderTraceSupport_card_cast_le_corvajaZannierSum
    (p : ℕ) (alpha beta : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      Nat.card (rightSubgroup d) = d)
    (hCZ : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (rightSubgroup d)))
    (hnondegenerate : alpha * beta ≠ 1) :
    ((weightedBadOrderTraceSupport alpha beta H₁
      (middleGameCandidateOrders p (Nat.card H₁)) rightSubgroup).card : ℝ) ≤
        ∑ d ∈ middleGameCandidateOrders p (Nat.card H₁),
          corvajaZannierTraceUpperBound p (Nat.card H₁) d := by
  apply weightedBadOrderTraceSupport_card_cast_le_sum
  intro d hd
  have hEstimate := hCZ hnondegenerate d hd
  rw [hrightOrder d hd] at hEstimate
  exact hEstimate

/-- Combining the weighted Corvaja--Zannier estimate with the common current-order envelope. -/
theorem middleGameWeightedBadOrderTraceSupport_card_cast_le_divisorEnvelope
    (p : ℕ) (alpha beta : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      Nat.card (rightSubgroup d) = d)
    (hCZ : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (rightSubgroup d)))
    (hnondegenerate : alpha * beta ≠ 1) :
    ((weightedBadOrderTraceSupport alpha beta H₁
      (middleGameCandidateOrders p (Nat.card H₁)) rightSubgroup).card : ℝ) ≤
      (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
        corvajaZannierCurrentOrderEnvelope p (Nat.card H₁) := by
  exact (middleGameWeightedBadOrderTraceSupport_card_cast_le_corvajaZannierSum
    p alpha beta H₁ rightSubgroup hrightOrder hCZ hnondegenerate).trans
      (middleGameCorvajaZannierSum_le_divisorCount_mul_envelope p (Nat.card H₁))

/-- If the divisor-counted weighted bad set is smaller than the left subgroup, one left element
avoids every candidate right-order trace. -/
theorem exists_left_element_escaping_weightedCandidateOrders
    (p : ℕ) (alpha beta : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ)
    (hbound : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      (weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card ≤ bound)
    (hsmall : ((p - 1).divisors.card + (p + 1).divisors.card) * bound < Nat.card H₁) :
    ∃ h₁ : H₁, ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ∀ h₂ : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h₁ ≠ splitTorusTrace h₂ := by
  classical
  let orders := middleGameCandidateOrders p (Nat.card H₁)
  let bad := weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup
  have hbad : bad.card < Nat.card H₁ :=
    (middleGameWeightedBadOrderTraceSupport_card_le
      p alpha beta H₁ rightSubgroup bound hbound).trans_lt hsmall
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
  exact mem_weightedBadOrderTraceSupport_iff.mpr
    ⟨d, by simpa [orders] using hd, h₂, heq⟩

/-- The complete finite weighted Corvaja--Zannier escape reduction.  The only deep premise is
`hCZ`; the remaining hypotheses are actual subgroup cardinalities and the two explicit size
inequalities controlling the cube-root and `1 / p` terms. -/
theorem exists_left_element_escaping_of_weightedCorvajaZannierEstimate_and_sizeBounds
    (p : ℕ) (alpha beta : E) (H₁ : Subgroup Eˣ)
    (rightSubgroup : ℕ → Subgroup Eˣ)
    (hrightOrder : ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      Nat.card (rightSubgroup d) = d)
    (hCZ : alpha * beta ≠ 1 →
      ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
        ((weightedTraceEquationSolutions alpha beta H₁ (rightSubgroup d)).card : ℝ) ≤
          corvajaZannierTraceUpperBound p (Nat.card H₁)
            (Nat.card (rightSubgroup d)))
    (hnondegenerate : alpha * beta ≠ 1)
    (hcurrentOrder : 0 < Nat.card H₁)
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < Nat.card H₁)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * Nat.card H₁ < p) :
    ∃ h₁ : H₁, ∀ d ∈ middleGameCandidateOrders p (Nat.card H₁),
      ∀ h₂ : rightSubgroup d,
        weightedSplitTorusTrace alpha beta h₁ ≠ splitTorusTrace h₂ := by
  classical
  let orders := middleGameCandidateOrders p (Nat.card H₁)
  let bad := weightedBadOrderTraceSupport alpha beta H₁ orders rightSubgroup
  have hbadReal : (bad.card : ℝ) < (Nat.card H₁ : ℝ) := by
    calc
      (bad.card : ℝ) ≤
          (((p - 1).divisors.card + (p + 1).divisors.card : ℕ) : ℝ) *
            corvajaZannierCurrentOrderEnvelope p (Nat.card H₁) := by
        simpa [orders, bad] using
          middleGameWeightedBadOrderTraceSupport_card_cast_le_divisorEnvelope
            p alpha beta H₁ rightSubgroup hrightOrder hCZ hnondegenerate
      _ < (Nat.card H₁ : ℝ) :=
        divisorCount_mul_corvajaZannierEnvelope_lt_currentOrder p (Nat.card H₁)
          hcurrentOrder hcube hlinear
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
  exact mem_weightedBadOrderTraceSupport_iff.mpr
    ⟨d, by simpa [orders] using hd, h₂, heq⟩

end BGS.Markoff
