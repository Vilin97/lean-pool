/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment

/-!
# Generic quotient constraints

This file records structural consequences of an assumed quotient/factorization
contract.  It proves that rules factoring through a quotient are constant on
quotient fibers, and that nontrivial quotient fibers necessarily leave some
other full-space distinctions unidentified.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- A rule is constant on every fiber of a quotient map. -/
def FiberInvariant {Ω Ωq A : Type} (Q : Ω → Ωq) (δ : Ω → A) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, Q ω₁ = Q ω₂ → δ ω₁ = δ ω₂

/-- A quotient has at least one fiber containing two distinct full observations. -/
def HasNontrivialFiber {Ω Ωq : Type} (Q : Ω → Ωq) : Prop :=
  ∃ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ ∧ Q ω₁ = Q ω₂

/-- A rule separates two observations lying in the same quotient fiber. -/
def SeparatesSameFiber {Ω Ωq A : Type} (Q : Ω → Ωq) (δ : Ω → A) : Prop :=
  ∃ ω₁ ω₂ : Ω, Q ω₁ = Q ω₂ ∧ δ ω₁ ≠ δ ω₂

/-- If a rule factors through a quotient, it is constant on quotient fibers. -/
theorem ruleFactorsThrough_fiberInvariant {Ω Ωq A : Type}
    (Q : Ω → Ωq) (δ : Ω → A)
    (h : RuleFactorsThrough Q δ) :
    FiberInvariant Q δ := by
  rcases h with ⟨δq, hδ⟩
  intro ω₁ ω₂ hQ
  rw [hδ ω₁, hδ ω₂, hQ]

/-- Bool-valued admission rules that factor through a quotient agree on fibers. -/
theorem ruleFactorsThrough_same_admission_on_fibers {Ω Ωq : Type}
    (Q : Ω → Ωq) (admission : Ω → Bool)
    (h : RuleFactorsThrough Q admission)
    {ω₁ ω₂ : Ω} (hQ : Q ω₁ = Q ω₂) :
    admission ω₁ = admission ω₂ :=
  ruleFactorsThrough_fiberInvariant Q admission h hQ

/-- Evidence values that factor through a quotient agree on quotient fibers. -/
theorem ruleFactorsThrough_same_evidence_on_fibers {Ω Ωq E : Type}
    (Q : Ω → Ωq) (evidence : Ω → E)
    (h : RuleFactorsThrough Q evidence)
    {ω₁ ω₂ : Ω} (hQ : Q ω₁ = Q ω₂) :
    evidence ω₁ = evidence ω₂ :=
  ruleFactorsThrough_fiberInvariant Q evidence h hQ

/-- A quotient-factorized finite likelihood ratio is constant on quotient fibers. -/
theorem finiteLikelihoodRatioFactorsThrough_fiberInvariant {Ω Ωq : Type}
    [Fintype Ω] (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω)
    (h : FiniteLikelihoodRatioFactorsThrough Q p0 p1) :
    FiberInvariant Q (finiteLikelihoodRatio p0 p1) :=
  ruleFactorsThrough_fiberInvariant Q (finiteLikelihoodRatio p0 p1) h

/-- Bayes-admit factorization says admission truth is invariant on quotient fibers. -/
theorem finiteBayesAdmitFactorsThrough_same_on_fibers {Ω Ωq : Type}
    [Fintype Ω] (Q : Ω → Ωq) (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0)
    (h : FiniteBayesAdmitFactorsThrough Q p0 p1 w0 w1)
    {ω₁ ω₂ : Ω} (hQ : Q ω₁ = Q ω₂) :
    finiteWeightedBayesAdmit p0 p1 w0 w1 ω₁ ↔
      finiteWeightedBayesAdmit p0 p1 w0 w1 ω₂ :=
  h hQ

/-- For a surjective quotient, fiber invariance is enough to build a quotient rule. -/
theorem fiberInvariant_ruleFactorsThrough_of_surjective {Ω Ωq A : Type}
    (Q : Ω → Ωq) (δ : Ω → A)
    (hQsurj : Function.Surjective Q)
    (hinv : FiberInvariant Q δ) :
    RuleFactorsThrough Q δ := by
  refine ⟨fun z => δ (Classical.choose (hQsurj z)), ?_⟩
  intro ω
  have hrep : Q (Classical.choose (hQsurj (Q ω))) = Q ω :=
    Classical.choose_spec (hQsurj (Q ω))
  exact (hinv hrep).symm

/-- A rule that separates two observations in the same fiber cannot factor through the quotient. -/
theorem not_ruleFactorsThrough_of_separatesSameFiber {Ω Ωq A : Type}
    (Q : Ω → Ωq) (δ : Ω → A)
    (hsep : SeparatesSameFiber Q δ) :
    ¬ RuleFactorsThrough Q δ := by
  intro hfac
  rcases hsep with ⟨ω₁, ω₂, hQ, hne⟩
  exact hne (ruleFactorsThrough_fiberInvariant Q δ hfac hQ)

/-- A quotient with a nontrivial fiber cannot be injective. -/
theorem not_injective_of_hasNontrivialFiber {Ω Ωq : Type}
    (Q : Ω → Ωq) (h : HasNontrivialFiber Q) :
    ¬ Function.Injective Q := by
  intro hinj
  rcases h with ⟨ω₁, ω₂, hne, hQ⟩
  exact hne (hinj hQ)

/-- If no quotient fiber contains two distinct observations, the quotient map is injective. -/
theorem injective_of_not_hasNontrivialFiber {Ω Ωq : Type}
    (Q : Ω → Ωq) (h : ¬ HasNontrivialFiber Q) :
    Function.Injective Q := by
  classical
  intro ω₁ ω₂ hQ
  by_contra hne
  exact h ⟨ω₁, ω₂, hne, hQ⟩

/-- A quotient has a nontrivial fiber exactly when it is not injective. -/
theorem hasNontrivialFiber_iff_not_injective {Ω Ωq : Type}
    (Q : Ω → Ωq) :
    HasNontrivialFiber Q ↔ ¬ Function.Injective Q := by
  constructor
  · exact not_injective_of_hasNontrivialFiber Q
  · intro hnotinj
    classical
    by_contra hnf
    exact hnotinj (injective_of_not_hasNontrivialFiber Q hnf)

/-- Every non-injective quotient fails to preserve some Bool-valued full-space target. -/
theorem exists_boolTarget_not_ruleFactorsThrough_of_hasNontrivialFiber {Ω Ωq : Type}
    (Q : Ω → Ωq) (h : HasNontrivialFiber Q) :
    ∃ target : Ω → Bool, ¬ RuleFactorsThrough Q target := by
  classical
  rcases h with ⟨ω₁, ω₂, hne, hQ⟩
  let target : Ω → Bool := fun ω => if ω = ω₁ then true else false
  refine ⟨target, ?_⟩
  apply not_ruleFactorsThrough_of_separatesSameFiber Q target
  refine ⟨ω₁, ω₂, hQ, ?_⟩
  simp [target, hne.symm]

/-- A nontrivial quotient can be sufficient for one target while insufficient for another. -/
theorem exists_pair_quotientTarget_factorsThrough_and_otherTarget_not {Ω Ωq : Type}
    (Q : Ω → Ωq) (h : HasNontrivialFiber Q) :
    (∃ target : Ω → Ωq, RuleFactorsThrough Q target) ∧
      (∃ other : Ω → Bool, ¬ RuleFactorsThrough Q other) := by
  constructor
  · exact ⟨Q, ⟨id, fun _ => rfl⟩⟩
  · exact exists_boolTarget_not_ruleFactorsThrough_of_hasNontrivialFiber Q h

/-- The positive region of a Bool rule that factors through a quotient is a quotient pullback. -/
theorem boolRuleFactorsThrough_positiveSet_eq_quotientPullback {Ω Ωq : Type}
    (Q : Ω → Ωq) (target : Ω → Bool)
    (h : RuleFactorsThrough Q target) :
    ∃ Rq : Set Ωq, {ω : Ω | target ω = true} = quotientPullback Q Rq := by
  rcases h with ⟨targetQ, htarget⟩
  refine ⟨{z | targetQ z = true}, ?_⟩
  ext ω
  simp [quotientPullback, htarget ω]

end OrdvecFormalization
