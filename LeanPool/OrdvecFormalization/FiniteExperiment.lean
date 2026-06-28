/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteDecision

/-!
# Finite statistical experiments and quotient sufficiency

This file contains the finite quotient decision layer. The observation
space is an arbitrary finite type.  A quotient map can safely replace the full
observation exactly when the pointwise Bayes evidence is constant on quotient
fibers; likelihood-ratio factorization is one sufficient condition.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- A strictly positive probability law on a finite observation space. -/
structure FiniteLaw (Ω : Type) [Fintype Ω] where
  /-- The probability mass at each observation. -/
  mass : Ω → ℝ≥0
  /-- Every observation has strictly positive mass. -/
  pos : ∀ ω, 0 < mass ω
  /-- The mass function is normalized. -/
  sum_one : Finset.univ.sum mass = 1

/-- View the ordered-support `PosPMF` API as an arbitrary finite law. -/
def finiteLawOfPosPMF {n : ℕ} (p : PosPMF n) : FiniteLaw (Support n) where
  mass := p.mass
  pos := p.pos
  sum_one := p.sum_one

/-- Pointwise weighted Bayes admission on an arbitrary finite observation space. -/
def finiteWeightedBayesAdmit {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (w0 w1 : ℝ≥0) (ω : Ω) : Prop :=
  w0 * p0.mass ω ≤ w1 * p1.mass ω

/-- The full pointwise Bayes admit set for an arbitrary finite experiment. -/
def finiteWeightedBayesAdmitSet {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (w0 w1 : ℝ≥0) : Set Ω :=
  {ω | finiteWeightedBayesAdmit p0 p1 w0 w1 ω}

/-- Finite weighted Bayes risk for an arbitrary deterministic admit set. -/
noncomputable def finiteWeightedRisk {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (w0 w1 : ℝ≥0) (R : Set Ω) : ℝ≥0 :=
  by
    classical
    exact Finset.univ.sum fun ω : Ω =>
      if ω ∈ R then w0 * p0.mass ω else w1 * p1.mass ω

/-- Probability mass assigned by a finite law to an event. -/
noncomputable def finiteLawProb {Ω : Type} [Fintype Ω] (p : FiniteLaw Ω)
    (R : Set Ω) : ℝ≥0 :=
  by
    classical
    exact Finset.univ.sum fun ω : Ω => if ω ∈ R then p.mass ω else 0

/-- The pointwise weighted Bayes admit set minimizes finite weighted risk. -/
theorem finiteWeightedBayesAdmitSet_optimal {Ω : Type} [Fintype Ω]
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) :
    ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (finiteWeightedBayesAdmitSet p0 p1 w0 w1) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  intro R
  dsimp [finiteWeightedRisk]
  refine Finset.sum_le_sum ?_
  intro ω _hω
  by_cases hA : finiteWeightedBayesAdmit p0 p1 w0 w1 ω
  · by_cases hR : ω ∈ R
    · simp [finiteWeightedBayesAdmitSet, hA, hR]
    · rw [if_pos (show ω ∈ finiteWeightedBayesAdmitSet p0 p1 w0 w1 from hA), if_neg hR]
      exact hA
  · by_cases hR : ω ∈ R
    · have hReject : w1 * p1.mass ω ≤ w0 * p0.mass ω :=
        le_of_lt (lt_of_not_ge hA)
      rw [if_neg (show ω ∉ finiteWeightedBayesAdmitSet p0 p1 w0 w1 from hA), if_pos hR]
      exact hReject
    · simp [finiteWeightedBayesAdmitSet, hA, hR]

/-- Pull an admit set on a quotient observation space back to the full space. -/
def quotientPullback {Ω Ωq : Type} (Q : Ω → Ωq) (Rq : Set Ωq) : Set Ω :=
  {ω | Q ω ∈ Rq}

/-- A deterministic rule or target factors through a quotient map. -/
def RuleFactorsThrough {Ω Ωq A : Type} (Q : Ω → Ωq) (δ : Ω → A) : Prop :=
  ∃ δq : Ωq → A, ∀ ω : Ω, δ ω = δq (Q ω)

/-- A deterministic rule exactly predicts a target. -/
def RulePredicts {Ω A : Type} (δ target : Ω → A) : Prop :=
  ∀ ω : Ω, δ ω = target ω

/-- Quotient-form rules are invariant under transformations preserving the quotient. -/
theorem mem_quotientPullback_of_quotient_preserving {Ω Ωq : Type}
    (Q : Ω → Ωq) (Rq : Set Ωq) (g : Ω → Ω)
    (hg : ∀ ω, Q (g ω) = Q ω) (ω : Ω) :
    g ω ∈ quotientPullback Q Rq ↔ ω ∈ quotientPullback Q Rq := by
  simp [quotientPullback, hg ω]

/--
The weighted Bayes evidence factors through a quotient when Bayes admission is
constant on every quotient fiber.
-/
def FiniteBayesAdmitFactorsThrough {Ω Ωq : Type} [Fintype Ω]
    (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄,
    Q ω₁ = Q ω₂ →
      (finiteWeightedBayesAdmit p0 p1 w0 w1 ω₁ ↔
        finiteWeightedBayesAdmit p0 p1 w0 w1 ω₂)

/-- The quotient admit set induced by a fiber-constant Bayes admit predicate. -/
def quotientBayesAdmitSet {Ω Ωq : Type} [Fintype Ω] (Q : Ω → Ωq)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) : Set Ωq :=
  {z | ∃ ω : Ω, Q ω = z ∧ finiteWeightedBayesAdmit p0 p1 w0 w1 ω}

/-- Under fiber-constant evidence, the quotient Bayes set pulls back to the full Bayes set. -/
theorem quotientBayesAdmitSet_pullback_eq {Ω Ωq : Type} [Fintype Ω]
    (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0)
    (hfactor : FiniteBayesAdmitFactorsThrough Q p0 p1 w0 w1) :
    quotientPullback Q (quotientBayesAdmitSet Q p0 p1 w0 w1) =
      finiteWeightedBayesAdmitSet p0 p1 w0 w1 := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨η, hηQ, hηA⟩
    exact (hfactor hηQ).mp hηA
  · intro hω
    exact ⟨ω, rfl, hω⟩

/--
Bayes-optimal quotient decision rule.

If the pointwise weighted Bayes evidence is constant on quotient fibers, then a
quotient-form rule is globally Bayes-optimal against all full-space rules.
-/
theorem exists_quotientPullback_finiteWeightedRisk_le {Ω Ωq : Type} [Fintype Ω]
    (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0)
    (hfactor : FiniteBayesAdmitFactorsThrough Q p0 p1 w0 w1) :
    ∃ Rq : Set Ωq, ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (quotientPullback Q Rq) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  refine ⟨quotientBayesAdmitSet Q p0 p1 w0 w1, ?_⟩
  intro R
  rw [quotientBayesAdmitSet_pullback_eq Q p0 p1 w0 w1 hfactor]
  exact finiteWeightedBayesAdmitSet_optimal p0 p1 w0 w1 R

/-- Likelihood ratio on an arbitrary finite positive experiment. -/
noncomputable def finiteLikelihoodRatio {Ω : Type} [Fintype Ω]
    (p0 p1 : FiniteLaw Ω) (ω : Ω) : ℝ≥0 :=
  p1.mass ω / p0.mass ω

/-- Likelihood-ratio factorization through a quotient map. -/
def FiniteLikelihoodRatioFactorsThrough {Ω Ωq : Type} [Fintype Ω]
    (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) : Prop :=
  ∃ φ : Ωq → ℝ≥0, ∀ ω : Ω, finiteLikelihoodRatio p0 p1 ω = φ (Q ω)

/-- Weighted Bayes admission is thresholding the finite likelihood ratio. -/
theorem finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio {Ω : Type}
    [Fintype Ω] (p0 p1 : FiniteLaw Ω) {w0 w1 : ℝ≥0} (hw1 : 0 < w1) (ω : Ω) :
    finiteWeightedBayesAdmit p0 p1 w0 w1 ω ↔
      w0 / w1 ≤ finiteLikelihoodRatio p0 p1 ω := by
  unfold finiteWeightedBayesAdmit finiteLikelihoodRatio
  rw [div_le_div_iff₀ hw1 (p0.pos ω)]
  simp [mul_comm]

/-- Likelihood-ratio factorization implies quotient-constant Bayes evidence. -/
theorem finiteBayesAdmitFactorsThrough_of_likelihoodRatioFactorsThrough {Ω Ωq : Type}
    [Fintype Ω] (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) {w0 w1 : ℝ≥0}
    (hw1 : 0 < w1) (hlr : FiniteLikelihoodRatioFactorsThrough Q p0 p1) :
    FiniteBayesAdmitFactorsThrough Q p0 p1 w0 w1 := by
  rcases hlr with ⟨φ, hφ⟩
  intro ω₁ ω₂ hQ
  rw [finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio p0 p1 hw1 ω₁,
    finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio p0 p1 hw1 ω₂,
    hφ ω₁, hφ ω₂, hQ]

/-- Likelihood-ratio factorization gives a Bayes-optimal quotient-form rule. -/
theorem exists_quotientPullback_finiteWeightedRisk_le_of_likelihoodRatioFactorsThrough {Ω Ωq : Type}
    [Fintype Ω] (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0)
    (hw1 : 0 < w1) (hlr : FiniteLikelihoodRatioFactorsThrough Q p0 p1) :
    ∃ Rq : Set Ωq, ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (quotientPullback Q Rq) ≤
        finiteWeightedRisk p0 p1 w0 w1 R :=
  exists_quotientPullback_finiteWeightedRisk_le Q p0 p1 w0 w1
    (finiteBayesAdmitFactorsThrough_of_likelihoodRatioFactorsThrough Q p0 p1 hw1 hlr)

/-!
## Quotient sufficiency is not fiber completeness

The following finite observation separates an ordinal coordinate from a
magnitude/degeneracy coordinate.  The ordinal quotient is sufficient for the
quotient target, but it cannot predict a second target that varies inside an
ordinal quotient fiber.
-/

/-- Example observation with an ordinal coordinate and a fiber coordinate. -/
abbrev QuotientFiberExampleObs := Bool × Bool

/-- The ordinal quotient keeps only the first coordinate. -/
def quotientFiberExampleQuotient (z : QuotientFiberExampleObs) : Bool :=
  z.1

/-- Quotient target: depends only on ordinal identity. -/
def quotientFiberExampleQuotientTarget (z : QuotientFiberExampleObs) : Bool :=
  z.1

/-- Fiber target: depends on the discarded coordinate. -/
def quotientFiberExampleFiberTarget (z : QuotientFiberExampleObs) : Bool :=
  z.2

/-- The quotient target factors through the ordinal quotient. -/
theorem quotientFiberExample_quotientTarget_factorsThrough :
    RuleFactorsThrough quotientFiberExampleQuotient quotientFiberExampleQuotientTarget := by
  refine ⟨id, ?_⟩
  intro z
  rfl

/-- The quotient target is perfectly predictable from the ordinal quotient. -/
theorem quotientFiberExample_quotientTarget_predictable_by_quotient :
    ∃ δq : Bool → Bool, ∀ z : QuotientFiberExampleObs,
      δq (quotientFiberExampleQuotient z) = quotientFiberExampleQuotientTarget z := by
  refine ⟨id, ?_⟩
  intro z
  rfl

/-- The discarded coordinate is perfectly predictable from the full observation. -/
theorem quotientFiberExample_fiberTarget_predictable_by_fullObservation :
    ∃ δ : QuotientFiberExampleObs → Bool, RulePredicts δ quotientFiberExampleFiberTarget := by
  exact ⟨quotientFiberExampleFiberTarget, fun _ => rfl⟩

/-- The fiber target does not factor through the ordinal quotient. -/
theorem quotientFiberExample_fiberTarget_not_factorsThrough :
    ¬ RuleFactorsThrough quotientFiberExampleQuotient quotientFiberExampleFiberTarget := by
  rintro ⟨δq, hδ⟩
  have h0 : δq false = false := by
    simpa [quotientFiberExampleQuotient, quotientFiberExampleFiberTarget] using
      (hδ (false, false)).symm
  have h1 : δq false = true := by
    simpa [quotientFiberExampleQuotient, quotientFiberExampleFiberTarget] using
      (hδ (false, true)).symm
  rw [h0] at h1
  cases h1

/-- Finite witness separating quotient-factorable and non-quotient-factorable targets. -/
theorem quotientFiberExample_quotientTarget_factorsThrough_not_fiberTarget :
    (RuleFactorsThrough quotientFiberExampleQuotient quotientFiberExampleQuotientTarget) ∧
      (¬ RuleFactorsThrough quotientFiberExampleQuotient quotientFiberExampleFiberTarget) ∧
        (∃ δ : QuotientFiberExampleObs → Bool, RulePredicts δ quotientFiberExampleFiberTarget) := by
  exact ⟨quotientFiberExample_quotientTarget_factorsThrough,
    quotientFiberExample_fiberTarget_not_factorsThrough,
    quotientFiberExample_fiberTarget_predictable_by_fullObservation⟩

end OrdvecFormalization
