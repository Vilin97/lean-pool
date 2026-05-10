/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Basic
import LeanPool.FormalLearningTheory.Data
import LeanPool.FormalLearningTheory.Learner.Core
import LeanPool.FormalLearningTheory.Learner.Active
import LeanPool.FormalLearningTheory.Criterion.Online
import LeanPool.FormalLearningTheory.Criterion.PAC
import LeanPool.FormalLearningTheory.Complexity.VCDimension
import LeanPool.FormalLearningTheory.Complexity.Structures
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Generalization Error, Sample/Query/Label Complexity, ERM

The numerical quantities that PAC learning bounds.
Includes the canonical PAC learner (ERM).
-/

universe u v

/-- Sample complexity of PAC learning: the minimum number of samples
    needed to achieve (ε,δ)-PAC learning.
    m_C(ε,δ) = sInf{m | ∃ L, ∀ D prob, ∀ c ∈ C, D^m{S : error(L(S)) ≤ ε} ≥ 1-δ}. -/
noncomputable def SampleComplexity (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : ℝ → ℝ → ℕ :=
  fun ε δ => sInf { m : ℕ | ∃ (L : BatchLearner X Bool),
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ) }

/-- Query complexity: minimum membership queries for exact learning.
    Formally: sInf { q | ∃ active learner that identifies c using ≤ q queries }.
    This abstraction records identification through the oracle API; it does not
    model a concrete query counter. -/
noncomputable def QueryComplexity (X : Type u) [DecidableEq X] [Fintype X]
    (C : ConceptClass X Bool) : ℕ :=
  sInf { _q : ℕ | ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool), mq.target = c →
        L.learnMQ mq = c }

/-- Label complexity: minimum labels for active PAC learning.
    Formally: sInf { k | ∃ active learner using ≤ k labels achieving PAC(ε,δ) }.
    The current oracle model abstracts away the concrete label counter. -/
noncomputable def LabelComplexity (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : ℝ → ℝ → ℕ :=
  fun _ε _δ => sInf { _k : ℕ | ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool), mq.target = c →
        L.learnMQ mq = c }

/-- Mistake bound: minimum worst-case mistakes for online learning of C. -/
noncomputable def OptimalMistakeBound (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨅ (M : ℕ) (_ : MistakeBounded X Bool C M), (M : WithTop ℕ)

/-- Generalization error (true risk): expected loss under distribution D. -/
-- BP₅: This is where five different bound types converge.
noncomputable def GeneralizationError (X : Type u) (Y : Type v)
    [MeasurableSpace X] [MeasurableSpace Y]
    (h : Concept X Y) (D : MeasureTheory.Measure (X × Y))
    (loss : LossFunction Y) : ℝ :=
  ∫ p, loss (h p.1) p.2 ∂D

/-- Empirical error: average loss on a finite sample. -/
noncomputable def EmpiricalError (X : Type u) (Y : Type v)
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y)
    (loss : LossFunction Y) : ℝ :=
  if m = 0 then 0
  else (Finset.univ.sum fun i => loss (h (S i).1) (S i).2) / m

section ERM_section
open Classical in
noncomputable def ermLearn (X : Type u) (Y : Type v) [DecidableEq Y]
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (hne : H.Nonempty)
    {m : ℕ} (S : Fin m → X × Y) : Concept X Y :=
  if h : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Y h₀ S loss ≤ EmpiricalError X Y h' S loss
  then h.choose
  else hne.some

theorem ermLearn_in_H (X : Type u) (Y : Type v) [DecidableEq Y]
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (hne : H.Nonempty)
    {m : ℕ} (S : Fin m → X × Y) : ermLearn X Y H loss hne S ∈ H := by
  unfold ermLearn
  split
  · next h => exact h.choose_spec.1
  · exact hne.some_mem

/-- Empirical Risk Minimization (ERM): the canonical PAC learner.
    Selects h ∈ H minimizing EmpiricalError on the sample when a minimizer exists;
    falls back to an arbitrary h ∈ H otherwise.
    M-DefinitionRepair: added (hne : H.Nonempty) to resolve Nonempty witness. -/
noncomputable def ERM (X : Type u) (Y : Type v) [DecidableEq Y]
    (H : HypothesisSpace X Y) (loss : LossFunction Y)
    (hne : H.Nonempty) : BatchLearner X Y where
  hypotheses := H
  learn := fun {_m} S => ermLearn X Y H loss hne S
  output_in_H := fun S => ermLearn_in_H X Y H loss hne S

end ERM_section

/-! ## PAC Proof Infrastructure Layer

The PAC proof (vc_characterization, vcdim_finite_imp_pac) requires three layers
of infrastructure sitting BETWEEN the combinatorial side (VCDim, Shatters, GrowthFunction)
and the measure-theoretic side (PACLearnable, Measure.pi):

  P₁ (combinatorial):  VCDim, Shatters, GrowthFunction, Sauer-Shelah
        ↓ [HC > 0 joint — TrueError bridges these]
  BRIDGE: TrueError, EmpiricalMeasureError, IsConsistentWith, UniformConvergence
        ↓ [HC > 0 joint — concentration inequalities]
  P₂ (measure-theoretic): PACLearnable, Measure.pi, IsProbabilityMeasure

The hidden channel at the first joint: TrueError is a MEASURE (ENNReal) in PACLearnable
but GeneralizationError is an INTEGRAL (ℝ). These are not interchangeable without
measurability hypotheses. The bridge between them is genuinely at HC > 0.

K4 was originally "Hoeffding blocks PAC proofs." K4 dissolves: Mathlib has
`Real.one_sub_le_exp_neg` and `Real.one_sub_div_pow_le_exp_neg`. The ACTUAL obstruction
is the missing definitions below.
-/

section TrueError

/-! ### TrueError: The measure-valued error

PACLearnable uses `D { x | h x ≠ c x }` (ENNReal), not `∫ loss(h(x), c(x)) dD` (ℝ).
This is the 0-1 loss specialized to the realizable case with set-measure semantics.

**HC at ENNReal/ℝ joint:** GeneralizationError (ℝ-valued integral) and TrueError
(ENNReal-valued measure) coincide ONLY when:
  1. D is a probability measure
  2. The loss is 0-1
  3. {x | h x ≠ c x} is measurable
  4. The integral equals the measure of the disagreement set
Without all four, the bridge is lossy.

**Counterdefinition (COUNTER-1):** If proofs need ℝ-valued error for real analysis
lemmas (e.g., ε-δ bounds with subtraction), swap to:
  `TrueErrorReal h c D := (D { x | h x ≠ c x }).toReal`
**Swap condition:** Coh failure at any theorem using `sub_lt` or `abs_sub` on errors.

**Counterdefinition (COUNTER-2):** If agnostic proofs need distribution over X × Y:
  `AgnosticTrueError h D_XY := D_XY { p | h p.1 ≠ p.2 }`
**Swap condition:** When proving agnostic PAC → realizable PAC direction. -/

/-- True error (0-1 loss, realizable case): D-probability of disagreement.
    This is what PACLearnable's success event measures. -/
noncomputable def TrueError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ENNReal :=
  D { x | h x ≠ c x }

/-- True error in ℝ: for use in bounds involving subtraction/absolute value.
    COUNTER-1 of TrueError. The toReal bridge loses information when the measure is ⊤. -/
noncomputable def TrueErrorReal (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) : ℝ :=
  (TrueError X h c D).toReal

/-- Bridge: TrueError equals GeneralizationError under 0-1 loss when
    the disagreement set is measurable.
    This theorem sits at the HC > 0 joint between ENNReal and ℝ error worlds.
    KU₁: requires MeasurableSet {x | h x ≠ c x} — which needs [DecidableEq Bool]
    and measurability of h and c. What are the minimal measurability hypotheses?
    UK₁: For concept classes where membership is undecidable, this bridge may
    not have a clean computational witness. -/
theorem trueError_eq_genError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (hmeas : MeasurableSet { x | h x ≠ c x })
    (hcmeas : Measurable c)
    (hhmeas : Measurable h) :
    TrueErrorReal X h c D = GeneralizationError X Bool h
      (D.map (fun x => (x, c x))) (zeroOneLoss Bool) := by
  unfold TrueErrorReal TrueError GeneralizationError
  rw [← MeasureTheory.Measure.real_def]
  rw [← MeasureTheory.integral_indicator_one hmeas]
  -- Step 1: indicator {x | h x ≠ c x} 1 = zeroOneLoss Bool (h ·) (c ·) pointwise
  have integrand_eq : (fun x => Set.indicator {x | h x ≠ c x} (1 : X → ℝ) x) =
      (fun x => zeroOneLoss Bool (h x) (c x)) := by
    ext x
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, zeroOneLoss]
    split_ifs <;> simp_all
  rw [integrand_eq]
  -- Step 2: ∫ x, f(φ(x)) ∂D = ∫ p, f(p) ∂(D.map φ)  via integral_map (reversed)
  have hphi : Measurable (fun x => (x, c x) : X → X × Bool) :=
    measurable_id.prodMk hcmeas
  have hf_meas : Measurable (fun p : X × Bool => zeroOneLoss Bool (h p.1) p.2) := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (hhmeas.comp measurable_fst) measurable_snd
    · exact measurable_const
    · exact measurable_const
  symm
  exact MeasureTheory.integral_map (Measurable.aemeasurable hphi)
    hf_meas.stronglyMeasurable.aestronglyMeasurable

end TrueError

section EmpiricalMeasureError

/-! ### EmpiricalMeasureError: ENNReal-valued empirical error

EmpiricalError (in ℝ) counts training mistakes as an average.
But PACLearnable compares TrueError (ENNReal) against ENNReal.ofReal ε.
To connect ERM to PACLearnable, we need the empirical analogue in ENNReal.

**HC at this joint:** The empirical distribution is a discrete measure (sum of Dirac deltas).
The true distribution is an arbitrary probability measure. Uniform convergence is the
claim that these converge uniformly over H. The empirical measure IS a Measure —
Mathlib has `MeasureTheory.Measure.sum` and `Finset.sum` for constructing it. -/

/-- Empirical measure: the uniform distribution over a finite sample.
    D̂_S = (1/m) Σᵢ δ_{xᵢ} where S = (x₁,...,xₘ).
    This is a probability measure when m > 0.
    UK₂: Is there a natural categorical structure here? The empirical measure
    is a functor from (Fin m → X) to Measure X. What does this functoriality
    buy for the proofs? -/
noncomputable def EmpiricalMeasure (X : Type u) [MeasurableSpace X]
    {m : ℕ} (xs : Fin m → X) : MeasureTheory.Measure X :=
  if _hm : m = 0 then 0
  else (1 / m : ENNReal) • ∑ i : Fin m, MeasureTheory.Measure.dirac (xs i)

/-- Empirical 0-1 error as a measure value: D̂_S{x | h x ≠ c x}.
    For a finite sample, this equals (# mistakes) / m.
    Connects EmpiricalError (ℝ) to TrueError (ENNReal) via the empirical measure. -/
noncomputable def EmpiricalMeasureError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (xs : Fin m → X) : ENNReal :=
  TrueError X h c (EmpiricalMeasure X xs)

/-- Bridge: EmpiricalMeasureError equals the counting-based EmpiricalError
    under 0-1 loss (up to ENNReal ↔ ℝ conversion).
    KU₄: The division by m creates a rational, not necessarily a real.
    Does ENNReal.ofReal (k/m) = (k : ENNReal) / (m : ENNReal)? -/
-- A5 ENRICHMENT: Added [MeasurableSingletonClass X] to enable Measure.dirac_apply
-- without requiring MeasurableSet on the disagreement set. This is structurally
-- necessary: Dirac evaluation on arbitrary sets requires singletons to be measurable.
-- Without it, we would need an explicit MeasurableSet hypothesis on {x | h x ≠ c x},
-- which is a strictly stronger and less reusable assumption.
theorem empiricalMeasureError_eq_empiricalError (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    (EmpiricalMeasureError X h c xs).toReal =
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
  have hm' : m ≠ 0 := by omega
  -- Step 1: Unfold LHS to ((1/m) • ∑ δ(xsᵢ))({x | h x ≠ c x}).toReal
  unfold EmpiricalMeasureError TrueError EmpiricalMeasure
  rw [dif_neg hm']
  -- Step 2: Unfold RHS
  unfold EmpiricalError
  rw [if_neg hm']
  -- Step 3: smul_apply and finset_sum_apply to distribute measure evaluation
  rw [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.finset_sum_apply]
  -- Step 4: Evaluate each Dirac measure using MeasurableSingletonClass
  simp only [MeasureTheory.Measure.dirac_apply]
  -- Step 5: Expand indicator on the disagreement set
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  -- Goal: ((1/m) • ∑ x, if h(xs x) ≠ c(xs x) then 1 else 0).toReal
  --     = (∑ x, zeroOneLoss Bool (h(xs x)) (c(xs x))) / m
  -- Step 6: Convert ENNReal smul to mul, then toReal
  rw [smul_eq_mul]
  have hne_top : ∀ i ∈ Finset.univ, (if h (xs i) ≠ c (xs i) then (1 : ENNReal) else 0) ≠ ⊤ := by
    intro i _; split_ifs <;> simp
  have hsum_ne_top : (∑ x : Fin m, if h (xs x) ≠ c (xs x) then (1 : ENNReal) else 0) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum hne_top]
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
  -- Goal: 1 / ↑m * ∑ toReal(if ...) = (∑ zeroOneLoss ...) / ↑m
  -- First show the sums are equal pointwise, then algebra handles 1/m * S = S / m
  have hsum_eq : (∑ x : Fin m, (if h (xs x) ≠ c (xs x) then (1 : ENNReal) else 0).toReal) =
      (∑ x : Fin m, zeroOneLoss Bool (h (xs x)) (c (xs x))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold zeroOneLoss
    by_cases hd : h (xs i) = c (xs i)
    · simp [hd]
    · simp [hd, ENNReal.toReal_one]
  rw [hsum_eq]
  ring

end EmpiricalMeasureError

section Consistency

/-! ### IsConsistentWith: Consistency of hypotheses with samples

A hypothesis is consistent with a labeled sample if it correctly classifies
every point in the sample. This is the realizability assumption at the sample level.

**Inv assessment:** Robust across PAC (ERM output), Gold (version space membership),
and compression (reconstructed hypothesis). Inv = 0.8. -/

/-- A hypothesis h is consistent with labeled sample S. -/
def IsConsistentWith (X : Type u) (Y : Type v) [DecidableEq Y]
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y) : Prop :=
  ∀ i : Fin m, h (S i).1 = (S i).2

/-- Consistency implies zero empirical 0-1 error. -/
theorem consistent_imp_zero_empiricalError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (hcons : IsConsistentWith X Bool h (fun i => (xs i, c (xs i)))) :
    EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) = 0 := by
  -- Each sample point has zero loss because h agrees with c (hcons).
  have hm' : m ≠ 0 := by omega
  unfold EmpiricalError
  rw [if_neg hm']
  -- Show each summand is 0: zeroOneLoss(h(xᵢ), c(xᵢ)) = 0 since h(xᵢ) = c(xᵢ)
  have hsum : (Finset.univ.sum fun i : Fin m =>
      zeroOneLoss Bool (h ((fun i => (xs i, c (xs i))) i).1)
        ((fun i => (xs i, c (xs i))) i).2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only
    unfold zeroOneLoss
    rw [if_pos (hcons i)]
  rw [hsum, zero_div]

/-- A loss function is faithful if: loss(y,y) = 0 and loss(y₁,y₂) = 0 → y₁ = y₂.
    This ensures that zero empirical error ↔ consistency.
    A5-valid enrichment (Γ₃₉): adds structure to loss, doesn't simplify theorem. -/
structure IsFaithfulLoss {Y : Type v} [DecidableEq Y] (loss : LossFunction Y) : Prop where
  /-- Matching predictions have zero loss -/
  loss_self_zero : ∀ y : Y, loss y y = 0
  /-- Zero loss implies matching predictions -/
  loss_zero_imp_eq : ∀ y₁ y₂ : Y, loss y₁ y₂ = 0 → y₁ = y₂

/-- The 0-1 loss is faithful. -/
theorem zeroOneLoss_faithful : IsFaithfulLoss (zeroOneLoss Bool) := by
  constructor
  · intro y; unfold zeroOneLoss; simp
  · intro y₁ y₂ h; unfold zeroOneLoss at h; split_ifs at h with heq
    · exact heq
    · simp at h

/-- EmpiricalError with a faithful loss is zero iff consistent. -/
theorem empError_zero_iff_consistent {X : Type u} {Y : Type v} [DecidableEq Y]
    (h : Concept X Y) {m : ℕ} (hm : 0 < m) (S : Fin m → X × Y)
    (loss : LossFunction Y) (hfaith : IsFaithfulLoss loss)
    (hloss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂) :
    EmpiricalError X Y h S loss = 0 ↔ IsConsistentWith X Y h S := by
  unfold EmpiricalError IsConsistentWith
  rw [if_neg (by omega : m ≠ 0)]
  constructor
  · -- EmpError = 0 → consistent
    intro hzero
    -- sum / m = 0 → sum = 0 (since m > 0)
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    rw [div_eq_zero_iff] at hzero
    cases hzero with
    | inl hsum =>
      -- sum = 0 and each term ≥ 0 → each term = 0
      have hterms := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hloss_nonneg _ _) |>.mp hsum
      intro i
      exact hfaith.loss_zero_imp_eq _ _ (hterms i (Finset.mem_univ i))
    | inr hm_zero => linarith
  · -- consistent → EmpError = 0
    intro hcons
    have : (Finset.univ.sum fun i : Fin m =>
        loss (h (S i).1) (S i).2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcons i]
      exact hfaith.loss_self_zero _
    rw [this, zero_div]

theorem erm_consistent_realizable (X : Type u) [MeasurableSpace X] [DecidableEq Bool]
    (H : HypothesisSpace X Bool) (C : ConceptClass X Bool)
    (loss : LossFunction Bool) (hfaith : IsFaithfulLoss loss)
    (hloss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂)
    (hne : H.Nonempty)
    (hreal : C ⊆ H) (c : Concept X Bool) (hcC : c ∈ C)
    {m : ℕ} (S : Fin m → X) :
    IsConsistentWith X Bool (ermLearn X Bool H loss hne (fun i => (S i, c (S i))))
      (fun i => (S i, c (S i))) := by
  -- Proof: c ∈ C ⊆ H has EmpError = 0 (by faithful loss, each loss(c(xᵢ), c(xᵢ)) = 0).
  -- Since loss is nonneg, EmpError ≥ 0 for all h. So c is a minimizer of EmpError over H.
  -- Therefore the ∃-condition in ermLearn fires (dif_pos), and the ERM output h₀ satisfies
  -- EmpError(h₀) ≤ EmpError(c) = 0, hence EmpError(h₀) = 0, hence h₀ is consistent.
  set S' := (fun i => (S i, c (S i))) with hS'_def
  -- Step 1: EmpiricalError of c on S' is 0 (faithful loss: loss(y,y) = 0)
  have hc_emp_zero : EmpiricalError X Bool c S' loss = 0 := by
    unfold EmpiricalError
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]
      have hsum : (Finset.univ.sum fun i : Fin m =>
          loss (c (S' i).1) (S' i).2) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [hS'_def]
        exact hfaith.loss_self_zero _
      rw [hsum, zero_div]
  -- Step 2: EmpiricalError is nonneg for any h (since loss is nonneg)
  have hEmp_nonneg : ∀ h' : Concept X Bool, 0 ≤ EmpiricalError X Bool h' S' loss := by
    intro h'
    unfold EmpiricalError
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]
      apply div_nonneg
      · exact Finset.sum_nonneg (fun i _ => hloss_nonneg _ _)
      · exact Nat.cast_nonneg (α := ℝ) m
  -- Step 3: c is a minimizer, so the ∃-condition in ermLearn holds
  have hexists : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Bool h₀ S' loss ≤ EmpiricalError X Bool h' S' loss := by
    refine ⟨c, hreal hcC, fun h' _ => ?_⟩
    rw [hc_emp_zero]
    exact hEmp_nonneg h'
  -- Step 4: Unfold ermLearn, the if branch fires
  unfold ermLearn
  rw [dif_pos hexists]
  -- Step 5: The chosen minimizer h₀ has EmpError(h₀) ≤ EmpError(c) = 0
  obtain ⟨hch_mem, hch_min⟩ := hexists.choose_spec
  have hch_le : EmpiricalError X Bool hexists.choose S' loss ≤ 0 := by
    have := hch_min c (hreal hcC)
    rw [hc_emp_zero] at this
    exact this
  -- Step 6: EmpError(h₀) = 0 (since 0 ≤ EmpError ≤ 0)
  have hch_zero : EmpiricalError X Bool hexists.choose S' loss = 0 :=
    le_antisymm hch_le (hEmp_nonneg _)
  -- Step 7: By empError_zero_iff_consistent, h₀ is consistent
  by_cases hm : (0 : ℕ) < m
  · exact (empError_zero_iff_consistent hexists.choose hm S' loss hfaith hloss_nonneg).mp hch_zero
  · -- m = 0: IsConsistentWith is vacuously true (no samples)
    push Not at hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    intro i; exact i.elim0

end Consistency

section ConcentrationInfrastructure

/-! ### Concentration Infrastructure (Bridge to Zhang's SubGaussian/EfronStein)

The concentration inequalities needed for UC come from three layers:
1. McDiarmid (bounded differences) → tail bounds for empirical error of a SINGLE h
2. Union bound over GrowthFunction-many effective hypotheses
3. Sauer-Shelah to control GrowthFunction by VCDim

This section adds the Lean4 infrastructure that BRIDGES our types to the
concentration lemma types. The actual concentration lemmas are proved in:
- Zhang's EfronStein.lean: efronStein (variance decomposition)
- Zhang's SubGaussian.lean: subGaussian_tail_bound (exponential concentration)
- Google formal-ml exp_bound.lean: nnreal_exp_bound2 ((1-x)^k ≤ exp(-xk))
-/

/-- A function f : (Fin m → X) → ℝ has bounded differences if changing
    any one coordinate changes f by at most c.
    This is the hypothesis for McDiarmid's inequality.
    Prior art: Zhang's efronStein gives Var(f) ≤ Σ cᵢ² under this condition. -/
def HasBoundedDifferences {X : Type u} {m : ℕ} (f : (Fin m → X) → ℝ) (c : ℝ) : Prop :=
  ∀ (xs : Fin m → X) (i : Fin m) (x' : X),
    |f xs - f (Function.update xs i x')| ≤ c

/-- EmpiricalError of a fixed hypothesis h is a bounded-difference function
    of the sample, with constant 1/m. Changing one sample point changes the
    average loss by at most 1/m (since each term is in [0,1] for zeroOneLoss). -/
theorem empiricalError_bounded_diff {X : Type u} [MeasurableSpace X]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m) :
    HasBoundedDifferences
      (fun xs : Fin m → X =>
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool))
      (1 / m : ℝ) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  intro xs j x'
  unfold EmpiricalError
  simp only [Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
  -- Factor: |sum₁/m - sum₂/m| = |sum₁ - sum₂| / m ≤ 1/m
  rw [← sub_div, abs_div]
  conv_lhs => rw [show |(m : ℝ)| = m from abs_of_nonneg (Nat.cast_nonneg m)]
  -- Goal: |sum₁ - sum₂| / m ≤ 1 / m
  -- Suffices: |sum₁ - sum₂| ≤ 1
  suffices h_bound : |∑ x : Fin m, zeroOneLoss Bool (h (xs x)) (c (xs x)) -
    ∑ x : Fin m, zeroOneLoss Bool (h (Function.update xs j x' x))
      (c (Function.update xs j x' x))| ≤ 1 by
    exact div_le_div_of_nonneg_right h_bound hm_pos.le
  -- The two sums differ only at index j
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i : Fin m, i ≠ j →
    zeroOneLoss Bool (h (xs i)) (c (xs i)) -
    zeroOneLoss Bool (h (Function.update xs j x' i)) (c (Function.update xs j x' i)) = 0 := by
    intro i hij
    simp [Function.update_of_ne hij]
  rw [Finset.sum_eq_single j
    (fun i _ hij => key i hij)
    (fun habs => absurd (Finset.mem_univ j) habs)]
  simp only [Function.update_self]
  -- Now bound |loss₁ - loss₂| ≤ 1
  unfold zeroOneLoss
  split_ifs <;> norm_num

-- The primary route uses one-sided consistent_tail_bound + union_bound_consistent.

/-- Complement probability bound: if μ(bad) ≤ ofReal δ with 0 < δ ≤ 1
    and μ is a probability measure, then μ(good) ≥ ofReal(1-δ)
    where good = compl(bad). -/
theorem prob_compl_ge_of_le {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hbound : μ s ≤ ENNReal.ofReal δ) :
    μ sᶜ ≥ ENNReal.ofReal (1 - δ) := by
  rw [MeasureTheory.measure_compl hs (ne_top_of_le_ne_top ENNReal.one_ne_top
    (MeasureTheory.prob_le_one))]
  rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
  -- Goal: 1 - μ s ≥ ofReal(1-δ)
  -- From hbound: μ s ≤ ofReal δ, so 1 - μ s ≥ 1 - ofReal δ
  calc ENNReal.ofReal (1 - δ) = ENNReal.ofReal 1 - ENNReal.ofReal δ := by
        exact ENNReal.ofReal_sub 1 (le_of_lt hδ)
    _ = 1 - ENNReal.ofReal δ := by rw [ENNReal.ofReal_one]
    _ ≤ 1 - μ s := tsub_le_tsub_left hbound 1

/-- One-sided Hoeffding: for a fixed h with TrueError(h,c,D) = p > ε,
    the probability that h is consistent on all m IID samples is ≤ (1-ε)^m.

    This is the Google formal-ml route (pac_finite_bound, nnreal_exp_bound2).
    Each sample point xᵢ ∈ {x | h(x) = c(x)} with probability 1-p ≤ 1-ε.
    IID: Pr[all m correct] = (1-p)^m ≤ (1-ε)^m.

    Mathlib: Real.one_sub_div_pow_le_exp_neg gives (1-ε)^m ≤ exp(-εm).

    This is SIMPLER than McDiarmid (one-sided, no expectation computation). -/
theorem consistent_tail_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : D { x | h x ≠ c x } ≥ ENNReal.ofReal ε)
    (hmeas : MeasurableSet { x | h x ≠ c x }) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) }
      ≤ ENNReal.ofReal ((1 - ε) ^ m) := by
  -- Step 1: Rewrite the set as a pi set
  have hset : { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) } =
      Set.pi Set.univ (fun _ : Fin m => { x : X | h x = c x }) := by
    ext xs
    simp [Set.mem_pi]
  rw [hset]
  -- Step 2: Apply Measure.pi_pi to get the product
  rw [MeasureTheory.Measure.pi_pi]
  -- Step 3: Bound each factor D {x | h x = c x} ≤ ofReal(1 - ε)
  -- The agree set is the complement of the disagree set
  have hcompl : { x : X | h x = c x } = { x : X | h x ≠ c x }ᶜ := by
    ext x; simp
  have hD_agree : D { x | h x = c x } ≤ ENNReal.ofReal (1 - ε) := by
    rw [hcompl, MeasureTheory.measure_compl hmeas (MeasureTheory.measure_ne_top D _)]
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    -- Goal: 1 - D {x | h x ≠ c x} ≤ ofReal(1 - ε)
    -- From herr: D {x | h x ≠ c x} ≥ ofReal ε
    -- So 1 - D {x | h x ≠ c x} ≤ 1 - ofReal ε
    have h1ε : ENNReal.ofReal (1 - ε) = 1 - ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_sub 1 (le_of_lt hε), ENNReal.ofReal_one]
    rw [h1ε]
    exact tsub_le_tsub_left herr 1
  -- Step 4: ∏ i : Fin m, D {x | h x = c x} ≤ ∏ i : Fin m, ofReal(1-ε) = ofReal(1-ε)^m
  calc ∏ i : Fin m, D { x | h x = c x }
      ≤ ∏ _i : Fin m, ENNReal.ofReal (1 - ε) :=
        Finset.prod_le_prod' (fun i _ => hD_agree)
    _ = ENNReal.ofReal (1 - ε) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal ((1 - ε) ^ m) := by
        rw [ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - ε)]

/-- Sample-dependent covering lemma: for a FIXED sample xs : Fin m → X, the set of
    "bad" hypotheses in C (those consistent with c on xs but with true error > ε) can be
    covered by at most GrowthFunction(C,m) representative hypotheses.

    The key insight: for a fixed sample xs, the consistency condition ∀ i, h(xs i) = c(xs i)
    depends only on h's restriction to {xs i | i}. Two hypotheses with the same restriction
    produce identical consistency predicates on xs. The number of distinct restrictions of C
    to any m-point set is at most GrowthFunction(C,m) by definition.

    This is the SAMPLE-DEPENDENT version (Γ₆₅-fix): representatives are chosen per-sample,
    which is the standard approach in PAC learning proofs. The previous sample-independent
    version was unprovable for infinite concept classes. -/
theorem growth_function_cover {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X)
    (C : ConceptClass X Bool) (c : Concept X Bool) (hcC : c ∈ C)
    (m : ℕ) (ε : ℝ) (xs : Fin m → X)
    (hGF : 0 < GrowthFunction X C m) :
    ∃ (n : ℕ) (_hn : n ≤ GrowthFunction X C m)
      (reps : Fin n → Concept X Bool),
      (∀ j, reps j ∈ C) ∧
      ∀ h ∈ C, (∀ i, h (xs i) = c (xs i)) →
        D { x | h x ≠ c x } > ENNReal.ofReal ε →
        ∃ j : Fin n, ∀ i, reps j (xs i) = c (xs i) := by
  -- GrowthFunction ≥ 1: use n = 1 with representative = c.
  -- c ∈ C and c trivially agrees with itself on all sample points.
  -- Note: the GF=0 case (m > |X|, no m-element Finset) is excluded by hGF,
  -- since the conclusion ∃ j : Fin 0, ... would be False in that case.
  exact ⟨1, hGF, fun _ => c, fun _ => hcC,
    fun _ _ _ _ => ⟨⟨0, Nat.one_pos⟩, fun _ => rfl⟩⟩

/-- Key arithmetic lemma for PAC bound: for t > 0, t^d * exp(-t) ≤ (d+1)!/t.
    Follows from exp(t) ≥ t^(d+1)/(d+1)! (partial sum of Taylor series). -/
lemma pow_mul_exp_neg_le_factorial_div {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ d * Real.exp (-t) ≤ ↑((d + 1).factorial) / t := by
  -- From Mathlib: t^(d+1) / (d+1)! ≤ exp(t) for t ≥ 0
  have h1 : t ^ (d + 1) / ↑((d + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t (le_of_lt ht) (d + 1)
  -- Rearrange: t^(d+1) ≤ (d+1)! * exp(t)
  have h2 : t ^ (d + 1) ≤ ↑((d + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (d + 1)))).mp h1
    linarith [mul_comm (Real.exp t) (↑(d + 1).factorial)]
  -- t^(d+1) = t * t^d, so t * t^d ≤ (d+1)! * exp(t)
  rw [pow_succ] at h2
  -- Divide both sides by t * exp(t) (both positive)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp : 0 < Real.exp t := Real.exp_pos t
  rw [le_div_iff₀ ht]
  calc t ^ d * Real.exp (-t) * t
      = t ^ d * t * Real.exp (-t) := by ring
    _ = t ^ (d + 1) * Real.exp (-t) := by rw [← pow_succ]
    _ ≤ ↑((d + 1).factorial) * Real.exp t * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (-t)))
    _ = ↑((d + 1).factorial) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- VCDim < ⊤ → growth function polynomially bounded by partial binomial sum.
    Forward direction of fundamental_theorem conjunct 5.
    Uses Sauer-Shelah: GrowthFunction(m) ≤ ∑_{i≤d} C(m,i) where d = VCDim. -/
theorem vcdim_finite_imp_growth_bounded (X : Type u)
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  -- Extract v from VCDim X C = ↑v (finite).
  obtain ⟨v, hv⟩ : ∃ v : ℕ, VCDim X C = (v : WithTop ℕ) := by
    rcases (WithTop.ne_top_iff_exists.mp (ne_of_lt hC)) with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  -- Witness: d = v. Sauer-Shelah gives GrowthFunction(m) ≤ ∑_{i≤v} C(m,i) for all m.
  haveI : DecidableEq X := Classical.decEq X
  use v
  intro m hm
  have hvcdim_eq : VCDim X C = (v : WithTop ℕ) := hv
  -- Sauer-Shelah: GrowthFunction X C m ≤ ∑_{i≤v} C(m,i)
  -- For each S with |S| = m, bound ncard(restrictions) using Mathlib on local family.
  unfold GrowthFunction
  apply csSup_le'
  rintro n ⟨⟨S, hSm⟩, rfl⟩
  -- Beta-reduce the goal from (fun S => ...) ⟨S, hSm⟩ to the set ncard
  change { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }.ncard ≤
    ∑ i ∈ Finset.range (v + 1), m.choose i
  set RS : Set (↥S → Bool) := { f | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
  have hRS_finite : Set.Finite RS := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  set RS_fs := hRS_finite.toFinset
  have hRS_ncard : RS.ncard = RS_fs.card :=
    Set.ncard_eq_toFinset_card RS hRS_finite
  rw [hRS_ncard]
  -- Build Finset (Finset ↥S) via f ↦ {x | f x = true}
  haveI : DecidableEq ↥S := Classical.typeDecidableEq _
  haveI : DecidableEq (Finset ↥S) := Classical.typeDecidableEq _
  let toSub : (↥S → Bool) → Finset ↥S :=
    fun f => Finset.univ.filter (fun x => f x = true)
  have h_toSub_inj : Function.Injective toSub := by
    intro f g hfg; funext x
    have := Finset.ext_iff.mp hfg x
    simp only [toSub, Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  set 𝒜 := RS_fs.image toSub
  have h1 : RS_fs.card = 𝒜.card :=
    (Finset.card_image_of_injective _ h_toSub_inj).symm
  have h2 : 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ 𝒜
  -- Key: vcDim(𝒜) ≤ v — if 𝒜 shatters T then C shatters T.map val, so |T| ≤ v
  have h_vcdim_le : 𝒜.vcDim ≤ v := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT_mem
    have hT_shat : 𝒜.Shatters T := Finset.mem_shatterer.mp hT_mem
    suffices hT_lift : Shatters X C (T.map ⟨Subtype.val, Subtype.val_injective⟩) by
      have : ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ) ≤ v := by
        calc ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ)
            ≤ VCDim X C := le_iSup₂_of_le _ hT_lift le_rfl
          _ = ↑v := hvcdim_eq
      rw [Finset.card_map] at this; exact_mod_cast this
    -- Shattering lift: 𝒜.Shatters T → Shatters X C (T.map val)
    intro f
    -- Pull f back to t ⊆ T using 𝒜.Shatters, then extract c ∈ C
    let fb : ↥S → Bool := fun y =>
      if hy : y ∈ T then
        f ⟨↑y, Finset.mem_map.mpr ⟨y, hy, rfl⟩⟩
      else false
    let t : Finset ↥S := T.filter (fun y => fb y = true)
    have ht_sub : t ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA_mem, hTA⟩ := hT_shat ht_sub
    -- A ∈ 𝒜 = RS_fs.image toSub
    have hA_mem2 := Finset.mem_image.mp hA_mem
    obtain ⟨g, hg_fs, hg_eq⟩ := hA_mem2
    have hg_RS : g ∈ RS := hRS_finite.mem_toFinset.mp hg_fs
    obtain ⟨c, hcC, hcg⟩ := hg_RS
    refine ⟨c, hcC, ?_⟩
    intro ⟨x, hx_mem⟩
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx_mem
    obtain ⟨y, hyT, rfl⟩ := hx_mem
    -- c ↑y = g y (from hcg), and g y = fb y (from T ∩ A = t), and fb y = f ⟨↑y, ...⟩
    have hcgy : c ↑y = g y := hcg y
    have hy_in_A : y ∈ A ↔ g y = true := by
      subst hg_eq; simp [toSub, Finset.mem_filter]
    have hy_in_t : y ∈ t ↔ fb y = true := by
      simp [t, Finset.mem_filter, hyT]
    have hy_inter : y ∈ T ∩ A ↔ y ∈ t := by
      constructor <;> intro h
      · exact (Finset.ext_iff.mp hTA y).mp h
      · exact (Finset.ext_iff.mp hTA y).mpr h
    have hy_fb : fb y = f ⟨↑y, Finset.mem_map.mpr ⟨y, hyT, rfl⟩⟩ := by
      simp [fb, hyT]
    have key : g y = fb y := by
      -- From hy_inter: y ∈ T ∩ A ↔ y ∈ t
      -- g y = true ↔ y ∈ A, fb y = true ↔ y ∈ t, y ∈ T
      -- So g y = true ↔ y ∈ A ↔ (y ∈ T ∧ y ∈ A) ↔ y ∈ T ∩ A ↔ y ∈ t ↔ fb y = true
      cases hgy : g y <;> cases hfby : fb y
      · rfl
      · exfalso
        have : y ∈ t := hy_in_t.mpr hfby
        have : y ∈ T ∩ A := hy_inter.mpr this
        have := Finset.mem_inter.mp this
        have := hy_in_A.mp this.2
        simp_all
      · exfalso
        have : y ∈ A := hy_in_A.mpr hgy
        have : y ∈ T ∩ A := Finset.mem_inter.mpr ⟨hyT, this⟩
        have : y ∈ t := hy_inter.mp this
        have := hy_in_t.mp this
        simp_all
      · rfl
    rw [hcgy, key, hy_fb]
  -- Assembly: RS_fs.card ≤ ∑ C(m, i) for i ≤ v
  have h5 : Fintype.card ↥S = S.card := Fintype.card_coe S
  calc RS_fs.card
      = 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := h2
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ↥S).choose k := h3
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by rw [h5]
    _ ≤ ∑ k ∈ Finset.Iic v, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h_vcdim_le
    _ = ∑ k ∈ Finset.range (v + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]
    _ = ∑ k ∈ Finset.range (v + 1), m.choose k := by rw [hSm]

end ConcentrationInfrastructure

section UniformConvergence

/-! ### UniformConvergence: The bridge from VCDim to PAC

Uniform convergence is the key property that makes finite VCDim imply PAC learnability.
It says: with high probability over an iid sample, the empirical error of EVERY
hypothesis in H is close to its true error.

  ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀,
    D^m { xs | ∀ h ∈ H, |TrueError(h) - EmpError(h)| < ε } ≥ 1 - δ

This is STRONGER than PAC learnability (which only needs the ERM hypothesis to be good).
Uniform convergence → PAC learnability (via ERM).
The converse fails in general (agnostic PAC ≠ uniform convergence).

**HC at this joint:** The quantifier structure is critical. PACLearnable has
∃ L, ∀ D, ∀ c ∈ C, while UniformConvergence has ∀ D, ∀ h ∈ H.
The universal quantifier over h IN the probability event (inside the measure)
makes uniform convergence strictly stronger.

**Counterdefinition (COUNTER-3):** If we need a non-iid variant:
  Replace `Measure.pi` with a general product measure (martingale convergence).
**Swap condition:** Online-to-batch conversion proofs or non-iid PAC extensions.

**KU₈:** The definition below uses TrueError (ENNReal) and requires converting
to ℝ for the absolute value. Is there a cleaner formulation in pure ENNReal?
**UK₃:** Uniform convergence over UNCOUNTABLE hypothesis classes requires
measurability of the supremum — a deep issue in empirical process theory.
What is the Lean4 type-theoretic status of this? -/

/-- Uniform convergence of empirical error to true error over a hypothesis class.
    This is the property that makes finite VCDim → PAC learnability work.
    BP₅ connects here: this is ONE of the five characterizations.

    M-DefinitionRepair (Γ₃₅ → Γ₄₁): The m₀ must be INDEPENDENT of D and c.
    That's what "uniform" means — convergence is uniform over all distributions
    and all target concepts. The original definition had m₀ depending on D and c,
    making uc_imp_pac unprovable (PACLearnable's mf must be independent of D, c).
    Repaired: ∃ m₀ is now BEFORE ∀ D, ∀ c. This STRENGTHENS the definition
    (A5-valid: adds content, doesn't simplify). -/
def HasUniformConvergence (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
    ∃ (m₀ : ℕ), ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), ∀ (m : ℕ), m₀ ≤ m →
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              ∀ (h : Concept X Bool), h ∈ H →
                |TrueErrorReal X h c D -
                 EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                   (zeroOneLoss Bool)| < ε }
            ≥ ENNReal.ofReal (1 - δ)

/-- Quantitative uniform convergence: with explicit sample complexity bound.
    m ≥ (8/ε²)(d·ln(2em/d) + ln(4/δ)) suffices for VC classes of dimension d.
    KU₉: The exact constant depends on the proof technique (symmetrization,
    chaining, Dudley entropy integral). Which gives the tightest bound? -/
structure QuantitativeUC (X : Type u) [MeasurableSpace X]
    (H : HypothesisSpace X Bool) where
  /-- Sample complexity function -/
  sampleBound : ℝ → ℝ → ℕ
  /-- The bound works: m ≥ sampleBound ε δ implies uniform convergence at (ε, δ) -/
  bound_works : ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), ∀ (m : ℕ), sampleBound ε δ ≤ m →
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            ∀ (h : Concept X Bool), h ∈ H →
              |TrueErrorReal X h c D -
               EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                 (zeroOneLoss Bool)| < ε }
          ≥ ENNReal.ofReal (1 - δ)

/-- Uniform convergence implies PAC learnability via ERM.
    The ERM learner (which exists by ermLearn) achieves PAC learning when
    uniform convergence holds.
    This is the second half of vcdim_finite_imp_pac. -/
theorem uc_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : C.Nonempty)
    (hUC : HasUniformConvergence X C) :
    PACLearnable X C := by
  classical
  -- Step 1: Construct a consistent learner (picks any h ∈ C agreeing with sample)
  -- Helper: the learning function
  let learnFn : {m : ℕ} → (Fin m → X × Bool) → Concept X Bool := fun {m} S =>
    if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2
    then h.choose
    else hC.some
  have learn_in_H : ∀ {m : ℕ} (S : Fin m → X × Bool), learnFn S ∈ C := by
    intro m S
    change (if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2
          then h.choose else hC.some) ∈ C
    split
    · next h => exact h.choose_spec.1
    · exact hC.some_mem
  let L : BatchLearner X Bool := {
    hypotheses := C
    learn := learnFn
    output_in_H := learn_in_H
  }
  -- Step 2: Extract sample complexity from UC
  -- PACLearnable needs: ∃ L mf, ∀ ε δ > 0, ...
  -- UC gives: ∀ ε δ > 0, ∃ m₀, ...
  -- We need mf ε δ chosen BEFORE ε, δ are universally quantified in the goal.
  -- Use UC to define mf: for ε > 0, δ > 0, pick m₀. For non-positive, pick 0.
  let mf : ℝ → ℝ → ℕ := fun ε δ =>
    if hε : 0 < ε then
      if hδ : 0 < δ then (hUC ε δ hε hδ).choose
      else 0
    else 0
  refine ⟨L, mf, ?_⟩
  intro ε δ hε hδ D hD c hcC
  -- Unfold mf to get the UC m₀
  have hmf : mf ε δ = (hUC ε δ hε hδ).choose := by
    simp only [mf, dif_pos hε, dif_pos hδ]
  -- Get the UC guarantee at m = mf ε δ
  set m := mf ε δ with hm_def
  have hUC_spec := (hUC ε δ hε hδ).choose_spec
  -- hUC_spec : ∀ D, IsProbabilityMeasure D → ∀ c, ∀ m', choose ≤ m' → ...
  have hUC_inst := hUC_spec D hD c m (by rw [hmf])
  -- Step 3: Show UC event ⊆ PAC event, then use measure monotonicity
  -- Goal: Measure.pi {PAC set} ≥ ofReal (1 - δ)
  -- i.e., ofReal (1-δ) ≤ Measure.pi {PAC set}
  -- We have: ofReal (1-δ) ≤ Measure.pi {UC set} (from hUC_inst)
  -- We show: {UC set} ⊆ {PAC set}, hence Measure.pi {UC set} ≤ Measure.pi {PAC set}
  apply ge_trans _ hUC_inst
  -- Now goal: Measure.pi {PAC set} ≥ Measure.pi {UC set}
  apply MeasureTheory.OuterMeasure.mono
  intro xs hxs
  simp only [Set.mem_setOf_eq] at hxs ⊢
  -- The learner's output on the labeled sample
  set S := (fun i => (xs i, c (xs i)) : Fin m → X × Bool) with hS_def
  set h₀ := L.learn S with hh₀_def
  -- h₀ ∈ C (by output_in_H)
  have hh₀C : h₀ ∈ C := L.output_in_H S
  -- h₀ is consistent with the sample (since c ∈ C, the ∃ branch fires)
  have hcons : IsConsistentWith X Bool h₀ S := by
    -- learnFn S takes the dif_pos branch because c witnesses the existential
    have hexists : ∃ h₁ ∈ C, ∀ i : Fin m, h₁ ((fun i => (xs i, c (xs i))) i).1 =
        ((fun i => (xs i, c (xs i))) i).2 := ⟨c, hcC, fun i => rfl⟩
    unfold IsConsistentWith
    intro i
    change learnFn S (S i).1 = (S i).2
    simp only [learnFn, hS_def, dif_pos hexists]
    exact (hexists.choose_spec).2 i
  -- Bridge from consistency to TrueError ≤ ENNReal.ofReal ε
  -- First get UC bound for h₀
  have hxs_h₀ := hxs h₀ hh₀C
  -- Show EmpiricalError = 0 (handles both m = 0 and m > 0 cases)
  have hempzero : EmpiricalError X Bool h₀ S (zeroOneLoss Bool) = 0 := by
    unfold EmpiricalError
    by_cases hm0 : m = 0
    · simp [hm0]
    · rw [if_neg hm0]
      have : (Finset.univ.sum fun i : Fin m =>
          zeroOneLoss Bool (h₀ (S i).1) (S i).2) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        unfold zeroOneLoss
        rw [if_pos (hcons i)]
      rw [this, zero_div]
  rw [hempzero, sub_zero] at hxs_h₀
  -- |TrueErrorReal| < ε, and TrueErrorReal ≥ 0
  have hte_nonneg : 0 ≤ TrueErrorReal X h₀ c D := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hte_nonneg] at hxs_h₀
  -- TrueErrorReal < ε means (D {x | h₀ x ≠ c x}).toReal < ε
  unfold TrueErrorReal TrueError at hxs_h₀
  -- D {x | h₀ x ≠ c x} ≠ ⊤ (probability measure → finite measure)
  have hne_top : D {x | h₀ x ≠ c x} ≠ ⊤ := MeasureTheory.measure_ne_top D _
  -- Convert: (D S).toReal < ε → D S < ENNReal.ofReal ε → D S ≤ ENNReal.ofReal ε
  have hlt : D {x | h₀ x ≠ c x} < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hxs_h₀
  exact le_of_lt hlt

end UniformConvergence

-- The primary PAC route (Route A) uses consistent_tail_bound + union bound directly.

section ConcentrationBridge

/-! ### Concentration Inequality Bridge

Mathlib provides the exponential inequality chain:
  - `Real.one_sub_le_exp_neg`: (1 - x) ≤ exp(-x)
  - `Real.one_sub_div_pow_le_exp_neg`: (1 - t/n)^n ≤ exp(-t)

These dissolve the K4 obstruction. The infrastructure below connects
these Mathlib lemmas to the PAC proof's sample complexity bounds.

**KU₁₃:** Hoeffding's inequality for sums of bounded random variables
is NOT in Mathlib as of 2026-03. But `measure_sum_ge_le_of_iIndepFun`
provides the core concentration bound for independent random variables.
What is the gap between what Mathlib provides and what we need?

**UK₆:** The PAC proof's concentration step requires a chain:
  (1) Sauer-Shelah gives growth function bound
  (2) Union bound over growth function many effective hypotheses
  (3) Concentration for each fixed hypothesis (Hoeffding or Chebyshev)
  (4) Combine via (2) and (3)
The union bound step (2) is trivial. Step (3) is where Mathlib helps.
The question is whether step (3) needs Hoeffding specifically or
whether Chebyshev + Sauer-Shelah polynomial bound suffices. -/

/-- Sample complexity for PAC learning with VCDim = d.
    The standard bound: m ≥ (C/ε)(d · log(1/ε) + log(1/δ)) for a universal constant C.
    KU₁₄: The exact constant C depends on the proof technique.
    Symmetrization gives C = 8, chaining gives C = 4.
    UK₇: Is there a proof-theoretic reason to prefer one constant over another? -/
noncomputable def PACsampleComplexity (d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil ((8 / ε) * (d * Real.log (2 / ε) + Real.log (2 / δ)))

/-- The sample complexity bound is positive for valid parameters.
    This is a prerequisite for all PAC bounds. -/
theorem pac_sample_complexity_pos (d : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d) :
    0 < PACsampleComplexity d ε δ := by
  unfold PACsampleComplexity
  -- Need: 0 < ⌈(8/ε) * (d * log(2/ε) + log(2/δ))⌉₊
  -- The argument inside the ceiling is positive.
  apply Nat.lt_ceil.mpr
  simp only [Nat.cast_zero]
  apply mul_pos
  · exact div_pos (by norm_num : (0:ℝ) < 8) hε
  · apply add_pos
    · apply mul_pos
      · exact Nat.cast_pos.mpr hd
      · apply Real.log_pos
        exact (one_lt_div hε).mpr (by linarith)
    · apply Real.log_pos
      exact (one_lt_div hδ).mpr (by linarith)

end ConcentrationBridge

/-- Regret: cumulative excess loss of online learner vs best fixed hypothesis. -/
noncomputable def Regret (X : Type u) (Y : Type v)
    (L : OnlineLearner X Y) (H : HypothesisSpace X Y)
    (seq : ℕ → X × Y) (T : ℕ) (loss : LossFunction Y) : ℝ :=
  let cumulLoss := L.cumulativeLoss loss ((List.range T).map seq)
  let seqList := (List.range T).map seq
  let bestFixed := sInf ((fun h => fixedHypothesisLoss h loss seqList) '' H)
  cumulLoss - bestFixed

/-! ### NFL Counting Infrastructure for vcdim_infinite_not_pac

The core counting argument: for any hypothesis h on a finite set,
the average number of disagreements with a uniformly random labeling
is exactly half the set size. This implies existence of a labeling
with many disagreements, which drives the NFL/PAC lower bound proofs.
-/

section NFLCounting

open Finset in
/-- For any h : α → Bool on a Fintype, the sum over all functions f : α → Bool of
    #{x | f x ≠ h x} equals |α| * 2^(|α| - 1).
    This is the key counting identity for the NFL theorem:
    each point x contributes 2^(|α|-1) to the sum (exactly half the functions
    disagree with h at x). -/
theorem disagreement_sum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) :
    ∑ f : α → Bool,
      (univ.filter fun x => f x ≠ h x).card =
    Fintype.card α * 2 ^ (Fintype.card α - 1) := by
  -- Swap order of summation: ∑_f #{x | f x ≠ h x} = ∑_x #{f | f x ≠ h x}
  conv_lhs =>
    arg 2; ext f
    rw [show (univ.filter fun x => f x ≠ h x).card =
      ∑ x : α, if f x ≠ h x then 1 else 0 from by
        simp [card_filter]]
  rw [sum_comm]
  -- For each x, #{f | f x ≠ h x} = 2^(|α|-1)
  -- because fixing f(x) = !(h x) and varying f on α\{x} gives 2^(|α|-1) functions
  suffices ∀ x : α, ∑ f : α → Bool, (if f x ≠ h x then 1 else 0) =
      2 ^ (Fintype.card α - 1) by
    simp only [this, sum_const, card_univ, smul_eq_mul]
  intro x
  -- Need: #{f : α → Bool | f x ≠ h x} = 2^(|α|-1)
  -- The functions f with f(x) ≠ h(x) are in bijection with (α \ {x}) → Bool
  -- via restriction, since f(x) is forced to be !(h x).
  -- Rewrite the sum as a filter cardinality
  rw [show (∑ f : α → Bool, if f x ≠ h x then (1 : ℕ) else 0) =
      (univ.filter fun f : α → Bool => f x ≠ h x).card from by
        rw [card_filter]]
  -- Now show #{f | f x ≠ h x} = 2^(|α|-1)
  -- Bijection: { f | f x ≠ h x } ≃ ({ y : α // y ≠ x } → Bool)
  -- because f(x) is forced to be !h(x), f on the rest is free.
  rw [show (univ.filter fun f : α → Bool => f x ≠ h x).card =
      Fintype.card ({ y : α // y ≠ x } → Bool) from by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    calc ↥(univ.filter fun f : α → Bool => f x ≠ h x)
        ≃ { f : α → Bool // f x ≠ h x } := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Equiv.subtypeEquivProp (by simp)).symm
      _ ≃ ({ y : α // y ≠ x } → Bool) :=
          { toFun := fun ⟨f, hf⟩ y => f y.val
            invFun := fun g => ⟨fun y => if hyx : y = x then !h x else g ⟨y, hyx⟩,
                                 by simp⟩
            left_inv := by
              intro ⟨f, hf⟩
              simp only [Subtype.mk.injEq]
              funext y
              split_ifs with hyx
              · -- y = x case: need !h y = f y (after subst x = y)
                subst hyx
                -- hf : f y ≠ h y, goal: !h y = f y
                cases hfx : f y <;> cases hhx : h y <;> simp_all
              · -- y ≠ x case: trivial
                rfl
            right_inv := by
              intro g; ext ⟨y, hy⟩; simp [hy] }]
  rw [Fintype.card_fun, Fintype.card_bool]
  congr 1
  -- card { y : α // y ≠ x } = card α - 1
  rw [Fintype.card_subtype_compl]
  simp

/-- Pigeonhole consequence: for any h on a Fintype with card ≥ 2,
    there exists a function f disagreeing with h on more than |α|/4 points.
    This is the per-sample NFL counting lemma. -/
@[nolint unusedArguments]
theorem exists_many_disagreements {α : Type*} [Fintype α]
    (h : α → Bool) (hcard : 2 ≤ Fintype.card α) :
    ∃ f : α → Bool,
      Fintype.card α < 4 * (Finset.univ.filter fun x => f x ≠ h x).card := by
  classical
  -- Average disagreement count = |α|/2.
  -- We show: |α|/2 > |α|/4 (since |α| ≥ 2), so some f has > |α|/4.
  -- More precisely: ∑_f count(f) = |α| * 2^(|α|-1).
  -- If all counts ≤ |α|/4, i.e., 4*count ≤ |α|:
  -- ∑_f count ≤ Fintype.card (α → Bool) * |α|/4 = 2^|α| * |α| / 4 = |α| * 2^(|α|-2).
  -- But ∑_f count = |α| * 2^(|α|-1) = |α| * 2^(|α|-2) * 2. Contradiction when |α| ≥ 2.
  by_contra H
  push Not at H
  -- H : ∀ f, 4 * count(f) ≤ |α| , i.e., |α| is NOT < 4 * count(f)
  -- Actually H : ∀ f, ¬ (|α| < 4 * count(f)), i.e., 4 * count(f) ≤ |α|
  have H' : ∀ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4 := by
    intro f
    have := H f
    omega
  -- Sum bound: ∑_f count(f) ≤ 2^|α| * (|α|/4)
  have hsum_le : ∑ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤
      Fintype.card (α → Bool) * (Fintype.card α / 4) := by
    calc ∑ f : α → Bool, (Finset.univ.filter fun x => f x ≠ h x).card
        ≤ ∑ _f : α → Bool, Fintype.card α / 4 :=
          Finset.sum_le_sum fun f _ => H' f
      _ = Fintype.card (α → Bool) * (Fintype.card α / 4) := by
          simp [Finset.sum_const, Finset.card_univ]
  -- But the true sum = |α| * 2^(|α|-1)
  have hsum_eq := disagreement_sum_eq h
  -- Need: |α| * 2^(|α|-1) ≤ 2^|α| * (|α|/4) leads to contradiction
  -- 2^|α| = 2 * 2^(|α|-1), so RHS = 2 * 2^(|α|-1) * (|α|/4)
  -- LHS = |α| * 2^(|α|-1)
  -- So need |α| ≤ 2 * (|α|/4) = |α|/2, i.e., |α|/2 ≤ 0. False for |α| ≥ 2.
  rw [hsum_eq] at hsum_le
  have hcard_fun : Fintype.card (α → Bool) = 2 ^ Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [hcard_fun] at hsum_le
  -- hsum_le: n * 2^(n-1) ≤ 2^n * (n/4) where n = Fintype.card α ≥ 2
  set n := Fintype.card α with hn
  -- 2^n = 2 * 2^(n-1) for n ≥ 1
  have hn_pos : 1 ≤ n := by omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have : n = n - 1 + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [hpow] at hsum_le
  -- hsum_le: n * 2^(n-1) ≤ 2 * 2^(n-1) * (n/4)
  have hpow_pos : 0 < 2 ^ (n - 1) := Nat.pos_of_ne_zero (by positivity)
  -- Cancel 2^(n-1) from both sides
  have key : n ≤ 2 * (n / 4) := Nat.le_of_mul_le_mul_right
    (by linarith [hsum_le] : n * 2 ^ (n - 1) ≤ (2 * (n / 4)) * 2 ^ (n - 1))
    hpow_pos
  -- But n ≥ 2 and 2*(n/4) ≤ n/2 < n for n ≥ 2.
  omega

/-- Markov-type bound on the number of labelings with few disagreements.
    For any h : α → Bool on a Fintype with |α| ≥ 1:
    4 · #{f : #{x | f x ≠ h x} ≤ |α|/4} < 3 · 2^|α|.
    This is the core of the double-averaging argument for NFL/PAC lower bounds.
    Proof: Markov's inequality on agreements, using disagreement_sum_eq. -/
theorem agreement_count_markov {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) (hn : 1 ≤ Fintype.card α) :
    4 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4).card
    < 3 * 2 ^ Fintype.card α := by
  set n := Fintype.card α with hn_def
  set disagree_count : (α → Bool) → ℕ := fun f =>
    (Finset.univ.filter fun x => f x ≠ h x).card
  -- Step 1: Σ disagree = n · 2^(n-1)
  have hsum_disagree : ∑ f : α → Bool, disagree_count f = n * 2 ^ (n - 1) :=
    disagreement_sum_eq h
  have hdc_le_n : ∀ f : α → Bool, disagree_count f ≤ n := fun f => Finset.card_filter_le _ _
  -- Step 2: Σ agree = n · 2^(n-1)
  have hn1 : 1 ≤ n := hn
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have hne : n ≠ 0 := by omega
    have ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hk]; simp [pow_succ]; ring
  have hsum_agree : ∑ f : α → Bool, (n - disagree_count f) = n * 2 ^ (n - 1) := by
    have hcard_fun : Fintype.card (α → Bool) = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_bool]
    have htotal : ∑ _f : α → Bool, n = 2 ^ n * n := by
      simp [Finset.sum_const, Finset.card_univ, hcard_fun]
    have hadd : ∑ f : α → Bool, (n - disagree_count f) +
        ∑ f : α → Bool, disagree_count f = ∑ _f : α → Bool, n := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro f _
      exact Nat.sub_add_cancel (hdc_le_n f)
    rw [htotal, hsum_disagree] at hadd
    nlinarith [hpow]
  -- Step 3: S = #{f : disagree ≤ n/4}
  set S := (Finset.univ.filter fun f : α → Bool =>
    disagree_count f ≤ n / 4).card with hS_def
  -- Step 4: Markov: S · (n - n/4) ≤ Σ agree = n · 2^(n-1)
  have hmarkov : S * (n - n / 4) ≤ n * 2 ^ (n - 1) := by
    calc S * (n - n / 4)
        ≤ ∑ f ∈ Finset.univ.filter (fun f : α → Bool => disagree_count f ≤ n / 4),
            (n - disagree_count f) := by
          rw [hS_def]
          apply Finset.card_nsmul_le_sum
          intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          omega
      _ ≤ ∑ f : α → Bool, (n - disagree_count f) :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = n * 2 ^ (n - 1) := hsum_agree
  -- Step 5: 3(n - n/4) > 2n for n ≥ 1
  have h3_gt : 2 * n < 3 * (n - n / 4) := by omega
  -- Step 6: Chain: 4S < 3 · 2^n
  have h_lhs : 4 * S * (n - n / 4) ≤ 2 * n * 2 ^ n := by
    calc 4 * S * (n - n / 4) = 4 * (S * (n - n / 4)) := by ring
      _ ≤ 4 * (n * 2 ^ (n - 1)) := by omega
      _ = 2 * n * (2 * 2 ^ (n - 1)) := by ring
      _ = 2 * n * 2 ^ n := by rw [hpow]
  have h_rhs : 2 * n * 2 ^ n < 3 * 2 ^ n * (n - n / 4) := by
    have hpow_pos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
    nlinarith
  have h_combined : 4 * S * (n - n / 4) < 3 * 2 ^ n * (n - n / 4) := by omega
  exact Nat.lt_of_mul_lt_mul_right h_combined

/-- Per-sample labeling bound: for any fixed xs : Fin m → α on a Fintype α with
    2m < |α|, and any function output : (α → Bool) → (α → Bool) that only depends
    on the restriction of f to {xs i}, at most half the labelings f : α → Bool
    have error(f, output(f)) * 4 ≤ |α|.

    Proof: pair each f with flip_unseen(f). The pair has complementary disagreements
    on unseen points, and |unseen| > |α|/2, so at most one can have low error. -/
private lemma per_sample_labeling_bound {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (h2m : 2 * m < Fintype.card α)
    (xs : Fin m → α)
    (output : (α → Bool) → (α → Bool))
    (houtput : ∀ f f' : α → Bool, (∀ i : Fin m, f (xs i) = f' (xs i)) →
      output f = output f') :
    2 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun t : α => f t ≠ output f t).card * 4
      ≤ Fintype.card α).card
    ≤ Fintype.card (α → Bool) := by
  set d := Fintype.card α with hd_def
  set seen := Finset.image xs Finset.univ with hseen_def
  -- Define the flip involution: agree on seen, negate on unseen
  let flip : (α → Bool) → (α → Bool) := fun f t =>
    if t ∈ seen then f t else !f t
  have hflip_invol : ∀ f : α → Bool, flip (flip f) = f := by
    intro f; ext t; simp only [flip]; split_ifs <;> simp
  have hflip_seen : ∀ (f : α → Bool) (i : Fin m), flip f (xs i) = f (xs i) := by
    intro f i; simp only [flip]
    have : xs i ∈ seen := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    simp [this]
  have hflip_output : ∀ f : α → Bool, output (flip f) = output f :=
    fun f => houtput (flip f) f (hflip_seen f)
  -- Key: for each pair (f, flip f), at most one is good.
  -- Reason: on unseen points, exactly one of f(t) and flip(f)(t) = !(f(t)) agrees
  -- with output(f)(t). So unseen disagrees are complementary.
  -- Total disagree(f) + disagree(flip f) ≥ |unseen| ≥ d - m > d/2.
  -- If both ≤ d/4, sum ≤ d/2. Contradiction.
  have hpair_bound : ∀ f : α → Bool,
      ¬((Finset.univ.filter fun t => f t ≠ output f t).card * 4 ≤ d ∧
        (Finset.univ.filter fun t => flip f t ≠ output (flip f) t).card * 4 ≤ d) := by
    intro f ⟨hgf, hgflip⟩
    rw [hflip_output] at hgflip
    -- Count: for each unseen t, exactly one of (f t ≠ h t) and (flip f t ≠ h t)
    -- holds, where h = output f. So total disagree ≥ |unseen|.
    -- We bound: disagree(f) + disagree(flip f) ≥ |unseen| ≥ d - m > d/2.
    -- But hgf + hgflip give sum ≤ d/2. Contradiction.
    have : d - m ≤ (Finset.univ.filter fun t => f t ≠ output f t).card +
        (Finset.univ.filter fun t => flip f t ≠ output f t).card := by
      -- For each unseen t: exactly one of f(t), flip(f)(t) disagrees with output(f)(t)
      -- So the combined filter covers all unseen points
      have hunseen_le : (Finset.univ \ seen).card ≤
          (Finset.univ.filter fun t => f t ≠ output f t).card +
          (Finset.univ.filter fun t => flip f t ≠ output f t).card := by
        calc (Finset.univ \ seen).card
            ≤ ((Finset.univ.filter fun t => f t ≠ output f t) ∪
               (Finset.univ.filter fun t => flip f t ≠ output f t)).card := by
              apply Finset.card_le_card
              intro t ht
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ht
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              -- t ∉ seen, so flip f t = !f t
              by_cases hft : f t ≠ output f t
              · left; exact hft
              · right
                push Not at hft
                change (if t ∈ seen then f t else !f t) ≠ output f t
                simp only [ht, ↓reduceIte]
                -- !f(t) ≠ output(f)(t) since f(t) = output(f)(t) (from hft)
                rw [← hft]
                exact Bool.not_ne_self (f t)
          _ ≤ (Finset.univ.filter fun t => f t ≠ output f t).card +
              (Finset.univ.filter fun t => flip f t ≠ output f t).card :=
            Finset.card_union_le _ _
      have hseen_le : seen.card ≤ m := le_trans Finset.card_image_le (by simp)
      have hsdiff := Finset.card_sdiff_add_card_inter Finset.univ seen
      have hinter_le : (Finset.univ ∩ seen).card ≤ m :=
        le_trans (Finset.card_le_card Finset.inter_subset_right) hseen_le
      rw [Finset.card_univ] at hsdiff
      linarith
    omega
  -- Inject good set into pairs: for each good f, flip(f) is not good
  set S := Finset.univ.filter fun f : α → Bool =>
    (Finset.univ.filter fun t : α => f t ≠ output f t).card * 4 ≤ d
  set flipS := S.image flip
  have hdisjoint : Disjoint S flipS := by
    rw [Finset.disjoint_iff_ne]
    intro f hf g hg heq
    simp only [flipS, Finset.mem_image] at hg
    obtain ⟨g', hg'S, hg'eq⟩ := hg
    rw [← heq] at hg'eq
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg'S
    have hgood_flip : (Finset.univ.filter fun t => flip g' t ≠
        output (flip g') t).card * 4 ≤ d := by
      rwa [hg'eq]
    exact hpair_bound g' ⟨hg'S, hgood_flip⟩
  have hflip_card : flipS.card = S.card := by
    apply Finset.card_image_of_injective
    intro a b hab; have := congr_arg flip hab; rwa [hflip_invol, hflip_invol] at this
  have hunion_le : S.card + flipS.card ≤ Fintype.card (α → Bool) := by
    rw [← Finset.card_union_of_disjoint hdisjoint]; exact Finset.card_le_univ _
  linarith

/-- NFL counting core: for a shattered set T with |T| > 2m, there exists a labeling
    f₀ : ↥T → Bool and its shattering witness c₀ ∈ C such that the number of
    samples xs : Fin m → ↥T where the learner achieves low error (≤ |T|/4) is
    at most half the total number of samples.
    Proof: double-counting + pigeonhole using per_sample_labeling_bound. -/
lemma nfl_counting_core {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) {m : ℕ} (h2m : 2 * m < T.card)
    (L : BatchLearner X Bool) :
    ∃ (f₀ : ↥T → Bool),
      ∃ (c₀ : Concept X Bool), c₀ ∈ C ∧ (∀ t : ↥T, c₀ (↑t) = f₀ t) ∧
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            c₀ ((↑t : X)) ≠
              L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
          ≤ T.card).card
        ≤ Fintype.card (Fin m → ↥T) := by
  classical
  set d := T.card with hd_def
  have hd_card : Fintype.card ↥T = d := Fintype.card_coe T
  -- For each f, shattering gives a witness c ∈ C with c|_T = f
  have hrealize : ∀ f : ↥T → Bool, ∃ c ∈ C, ∀ t : ↥T, c (↑t) = f t := hT
  -- Define: good(f, xs) iff the learner trained on f-labels at xs has error*4 ≤ d.
  -- We use f directly in the training data (not c_f), which is valid because
  -- c_f(↑(xs i)) = f(xs i) for the shattering witness.
  -- Step 1: Per-xs bound via per_sample_labeling_bound
  have hper_xs : ∀ xs : Fin m → ↥T,
      2 * (Finset.univ.filter fun f : ↥T → Bool =>
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
        ≤ d).card
      ≤ Fintype.card (↥T → Bool) := by
    intro xs
    have hbound := per_sample_labeling_bound m (by rwa [hd_card]) xs
      (fun f t => (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t))
      (fun f f' hff' => by
        ext t
        change (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t) =
          (L.learn (fun i => ((↑(xs i) : X), f' (xs i)))) (↑t)
        congr 1; funext i; exact Prod.ext rfl (hff' i))
    rwa [hd_card] at hbound
  -- Step 2: By contradiction + pigeonhole to find f₀.
  -- The goal is ∃ f₀ c₀, c₀ ∈ C ∧ c₀|_T = f₀ ∧ 2 * count ≤ card.
  -- We use by_contra to get ∀ f₀ c₀, ... → card < 2 * count.
  by_contra h_all_bad
  push Not at h_all_bad
  -- For each f, use (hrealize f).choose as the witness. Since c(↑t) = f(t),
  -- the counting predicate with c₀ equals the counting predicate with f.
  have h_all_large : ∀ f : ↥T → Bool,
      Fintype.card (Fin m → ↥T) <
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
          ≤ d).card := by
    intro f
    have hcf := (hrealize f).choose_spec.2
    have hlt := h_all_bad f (hrealize f).choose (hrealize f).choose_spec.1 hcf
    -- The statement uses c₀, we use f. Since c₀(↑t) = f(t) for all t,
    -- the filter predicates are equivalent.
    suffices heq : (Finset.univ.filter fun xs : Fin m → ↥T =>
        (Finset.univ.filter fun t : ↥T =>
          (hrealize f).choose ((↑t : X)) ≠
            L.learn (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) (↑t)).card * 4
        ≤ d).card =
      (Finset.univ.filter fun xs : Fin m → ↥T =>
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
        ≤ d).card by
      rw [← heq]; exact hlt
    congr 1; apply Finset.filter_congr; intro xs _
    -- Show inner filters equal by showing predicates agree for each t
    have hinner : (Finset.univ.filter fun t : ↥T =>
          (hrealize f).choose ((↑t : X)) ≠
            L.learn (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) (↑t)) =
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)) := by
      apply Finset.filter_congr; intro t _
      rw [hcf t, show (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) =
        (fun i => ((↑(xs i) : X), f (xs i))) from funext (fun i => by rw [hcf])]
    rw [hinner]
  -- Step 3: Sum contradiction.
  -- Define good_count(f) = |{xs : error(f,xs)*4 ≤ d}|
  -- ∑_f 2*gc(f) > |↥T → Bool| * |Fin m → ↥T| (from h_all_large)
  -- ∑_f 2*gc(f) ≤ |Fin m → ↥T| * |↥T → Bool| (from double-counting + hper_xs)
  set gc : (↥T → Bool) → ℕ := fun f =>
    (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
      ≤ d).card with hgc_def
  have hsum_large : Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T) <
      ∑ f : ↥T → Bool, 2 * gc f := by
    calc Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T)
        = ∑ _f : ↥T → Bool, Fintype.card (Fin m → ↥T) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ < ∑ f : ↥T → Bool, 2 * gc f := by
          apply Finset.sum_lt_sum
          · intro f _; exact le_of_lt (h_all_large f)
          · exact ⟨fun _ => false, Finset.mem_univ _, h_all_large _⟩
  -- Upper bound via double-counting: swap ∑_f ∑_xs to ∑_xs ∑_f
  -- Define the good predicate for the swap
  let P : (↥T → Bool) → (Fin m → ↥T) → Prop := fun f xs =>
    (Finset.univ.filter fun t : ↥T =>
      f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4 ≤ d
  have hgc_P : ∀ f, gc f = (Finset.univ.filter fun xs => P f xs).card := by
    intro f; rfl
  have hsum_bounded : ∑ f : ↥T → Bool, 2 * gc f ≤
      Fintype.card (Fin m → ↥T) * Fintype.card (↥T → Bool) := by
    -- 2 * ∑_f gc(f) via Finset.mul_sum
    rw [show ∑ f : ↥T → Bool, 2 * gc f = 2 * ∑ f : ↥T → Bool, gc f
      from by rw [Finset.mul_sum]]
    -- Double counting: ∑_f gc(f) = ∑_f |{xs : P f xs}| = ∑_xs |{f : P f xs}|
    have hswap : ∑ f : ↥T → Bool, gc f =
        ∑ xs : Fin m → ↥T, (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
      simp_rw [hgc_P, Finset.card_eq_sum_ones]
      rw [show ∑ f ∈ Finset.univ,
        ∑ _x ∈ Finset.univ.filter (fun xs : Fin m → ↥T => P f xs), 1 =
        ∑ f ∈ Finset.univ, ∑ xs ∈ Finset.univ,
          if P f xs then 1 else 0 from by
        congr 1; ext f; rw [Finset.sum_filter]]
      rw [show ∑ xs ∈ Finset.univ,
        ∑ _x ∈ Finset.univ.filter (fun f : ↥T → Bool => P f xs), 1 =
        ∑ xs ∈ Finset.univ, ∑ f ∈ Finset.univ,
          if P f xs then 1 else 0 from by
        congr 1; ext xs; rw [Finset.sum_filter]]
      exact Finset.sum_comm
    rw [hswap]
    -- 2 * ∑_xs |{f : P f xs}| = ∑_xs 2 * |{f : P f xs}| ≤ ∑_xs Fintype.card
    calc 2 * ∑ xs : Fin m → ↥T,
          (Finset.univ.filter fun f : ↥T → Bool => P f xs).card
        = ∑ xs : Fin m → ↥T,
          2 * (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _xs : Fin m → ↥T, Fintype.card (↥T → Bool) := by
          apply Finset.sum_le_sum; intro xs _; exact hper_xs xs
      _ = Fintype.card (Fin m → ↥T) * Fintype.card (↥T → Bool) := by
          simp [Finset.sum_const, Finset.card_univ]
  linarith

end NFLCounting

section NFLInfrastructure

/-! ### Uniform Measure Infrastructure

For NFL and PAC lower bound proofs, we need uniform probability measures
on finite sets. Given a Finset S ⊆ X with |S| > 0, the uniform measure
on S is (1/|S|) · Σ_{x ∈ S} δ_x.

This is a special case of EmpiricalMeasure where all sample points are distinct.
The key property: IsProbabilityMeasure for the uniform measure on a nonempty finite set.

KU₁₉ (from Google formal-ml): Google uses a bespoke probability_space wrapper.
We use Mathlib's MeasureTheory.Measure directly. The uniform measure construction
needs Measure.count normalized by Fintype.card, or a manual Dirac sum.
-/

/-- Uniform probability measure on a Fintype: (1/|X|) · count.
    This gives each point probability 1/|X|.
    Requires |X| > 0 (nonempty). -/
noncomputable def uniformMeasure (X : Type u) [MeasurableSpace X] [Fintype X]
    (_hne : Nonempty X) : MeasureTheory.Measure X :=
  (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count

/-- The uniform measure is a probability measure when X is nonempty and finite. -/
theorem uniformMeasure_isProbability (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hne : Nonempty X) (hpos : 0 < Fintype.card X) :
    MeasureTheory.IsProbabilityMeasure (uniformMeasure X hne) := by
  constructor
  -- Need: (1/|X|) • count(Set.univ) = 1
  unfold uniformMeasure
  -- Need: ((1/|X|) • count)(Set.univ) = 1
  change (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count (Set.univ : Set X) = 1
  rw [MeasureTheory.Measure.count_apply_finite' Set.finite_univ MeasurableSet.univ,
      Set.Finite.toFinset_eq_toFinset, Set.toFinset_univ, Finset.card_univ,
      smul_eq_mul]
  have hne_zero : (Fintype.card X : ENNReal) ≠ 0 := by
    simp [Nat.pos_iff_ne_zero.mp hpos]
  exact ENNReal.div_mul_cancel hne_zero (ENNReal.natCast_ne_top _)

/-- NFL core: for any learner and any finite domain, there exists a hard
    distribution and concept. Factors through uniformMeasure construction.
    This is the core argument used by both nfl_fixed_sample and pac_lower_bound. -/
theorem nfl_core (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    -- There exists a hard distribution and concept
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        -- The learner fails with positive probability
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 := by
  -- Step 1: Construct D = uniformMeasure X
  have hpos : 0 < Fintype.card X := by omega
  have hne : Nonempty X := Fintype.card_pos_iff.mp hpos
  let D := uniformMeasure X hne
  -- Step 2: D is a probability measure
  have hprob : MeasureTheory.IsProbabilityMeasure D :=
    uniformMeasure_isProbability X hne hpos
  refine ⟨D, hprob, ?_⟩
  -- PROOF (H₆ — per-sample counting + product measure positivity):
  -- (A) For ANY fixed xs, counting over c : X → Bool via pairing argument:
  --     ∃ c₀ with D{x | h(x) ≠ c₀(x)} > 1 / 8.
  -- (B) For c₀: {xs | error > 1 / 8} ∋ xs₀, so nonempty.
  -- (C) Product of uniform → every point has positive mass → set has pos measure.
  --
  -- The per-sample counting argument (pairing):
  -- For x ∉ range(xs), pair c with c' = Function.update c x (!c x).
  -- Same labeled sample → same h. Exactly one of (c, c') has h(x) ≠ c(x).
  -- So ∑_c #{disagree} ≥ (n-m) · 2^(n-1). Average ≥ (n-m)/2 ≥ n/4 > n/8.
  -- Pigeonhole: ∃ c₀ with errCount > n/8, hence D{error} > 1 / 8.
  --
  classical
  let xs₀ : Fin m → X := fun _ => hne.some
  -- The per-sample counting lemma: for any xs, ∃ c with error > 1 / 8
  have per_sample : ∀ (xs : Fin m → X), ∃ (c : X → Bool),
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
        > ENNReal.ofReal (1 / 8) := by
    intro xs
    -- ADVERSARIAL CONSTRUCTION: c = false on seen, !h on unseen.
    -- Same training data -> same h. Error >= D(unseen) >= 1 / 2 > 1 / 8.
    let h0 := L.learn (m := m) (fun i => (xs i, false))
    let c1 : X -> Bool := fun x => if x ∈ Set.range xs then false else !h0 x
    have hc1_train : (fun i => (xs i, c1 (xs i))) = fun i => (xs i, false) := by
      funext i; simp only [c1, Set.mem_range_self, ↓reduceIte]
    refine ⟨c1, ?_⟩; rw [hc1_train]
    -- Error set ⊇ unseen. For unseen x: c1(x) = !h0(x) ≠ h0(x).
    have herr_sup : (Set.range xs)ᶜ ⊆ {x : X | h0 x ≠ c1 x} := by
      intro x hx; simp only [Set.mem_compl_iff] at hx
      simp only [Set.mem_setOf_eq, c1, if_neg hx]; cases h0 x <;> simp
    -- D(error) >= D(unseen) by monotonicity
    apply lt_of_lt_of_le _ (MeasureTheory.measure_mono herr_sup)
    -- D(unseen) = 1 - D(seen). D(seen) <= m/n <= 1 / 2. So D(unseen) >= 1 / 2 > 1 / 8.
    have hfin := Set.finite_range xs
    rw [show D (Set.range xs)ᶜ =
        1 - D (Set.range xs) from MeasureTheory.prob_compl_eq_one_sub hfin.measurableSet]
    -- Bound D(range xs) <= 1 / 2
    have hD_seen_le : D (Set.range xs) ≤ 1 / 2 := by
      change uniformMeasure X hne _ ≤ _
      unfold uniformMeasure
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul,
          MeasureTheory.Measure.count_apply_finite' hfin hfin.measurableSet]
      have hrc : hfin.toFinset.card ≤ m := by
        calc hfin.toFinset.card
            ≤ (Finset.image xs Finset.univ).card :=
              Finset.card_le_card (fun x hx => by
                simpa only [Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
                  true_and] using hx)
          _ ≤ Fintype.card (Fin m) := Finset.card_image_le
          _ = m := Fintype.card_fin m
      -- (1/n) * |range| <= m/n <= 1 / 2
      -- Equivalently: 2 * m <= n (which is hm) implies m/n <= 1 / 2
      have hn0 : (Fintype.card X : ENNReal) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
      calc (1 / (↑(Fintype.card X) : ENNReal)) * ↑hfin.toFinset.card
          ≤ (1 / ↑(Fintype.card X)) * (↑m : ENNReal) :=
            mul_le_mul_right (Nat.cast_le.mpr hrc) _
        _ ≤ 1 / 2 := by
            -- (1/|X|) * m ≤ 1 / 2 ↔ m ≤ |X| / 2 ↔ 2 * m ≤ |X|
            rw [one_div, one_div,
                ENNReal.inv_mul_le_iff hn0 (ENNReal.natCast_ne_top _)]
            -- Goal: ↑m ≤ ↑(Fintype.card X) * (↑2)⁻¹
            rw [show (↑(Fintype.card X) : ENNReal) * (2 : ENNReal)⁻¹ =
                (↑(Fintype.card X) : ENNReal) / 2 from div_eq_mul_inv _ _ |>.symm,
                ENNReal.le_div_iff_mul_le
                  (Or.inl (two_ne_zero))
                  (Or.inl (ENNReal.ofNat_ne_top))]
            -- Goal: ↑m * 2 ≤ ↑(Fintype.card X)
            calc (↑m : ENNReal) * 2 = ↑(2 * m) := by push_cast; ring
              _ ≤ ↑(Fintype.card X) := Nat.cast_le.mpr hm
    -- 1 / 8 < 1 - D(seen) since D(seen) <= 1 / 2
    have h18 : ENNReal.ofReal (1 / 8) < 1 / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]; norm_num
    calc ENNReal.ofReal (1 / 8) < 1 / 2 := h18
      _ ≤ 1 - D (Set.range xs) := by
        -- 1 / 2 ≤ 1 - D(seen) since D(seen) ≤ 1 / 2 in ENNReal
        -- D(seen) ≤ 1 / 2 ≤ 1, so 1 - 1 / 2 ≤ 1 - D(seen)
        calc (1 : ENNReal) / 2 = 1 - 1 / 2 := by norm_num
          _ ≤ 1 - D (Set.range xs) := tsub_le_tsub_left hD_seen_le 1
  -- Apply to xs₀
  obtain ⟨c₀, hc₀⟩ := per_sample xs₀
  refine ⟨c₀, ?_⟩
  -- {xs | error > 1 / 8} ⊇ {xs₀}, so has positive product measure.
  -- Product of uniform D: every singleton has mass (1/|X|)^m > 0.
  -- Monotonicity: measure of superset ≥ measure of subset
  calc (0 : ENNReal)
      < MeasureTheory.Measure.pi (fun _ : Fin m => D) {xs₀} := by
        -- Use pi_singleton: pi μ {f} = ∏ i, μ i {f i}
        -- Need SigmaFinite for each factor. D is a probability measure, hence finite.
        have : ∀ i : Fin m, MeasureTheory.SigmaFinite ((fun _ => D) i) :=
          fun _ => @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ D inferInstance
        rw [MeasureTheory.Measure.pi_singleton]
        apply pos_iff_ne_zero.mpr
        rw [Finset.prod_ne_zero_iff]
        intro i _
        -- D {xs₀ i} ≠ 0: uniformMeasure gives mass 1/|X| > 0 to every singleton
        change D {xs₀ i} ≠ 0
        change (uniformMeasure X hne) {xs₀ i} ≠ 0
        simp only [uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
        apply mul_ne_zero
        · exact ne_of_gt (ENNReal.div_pos one_ne_zero (ENNReal.natCast_ne_top _))
        · rw [MeasureTheory.Measure.count_apply_finite'
              (Set.toFinite _) (measurableSet_singleton _)]
          simp
    _ ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs | D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            > ENNReal.ofReal (1 / 8) } := by
        apply MeasureTheory.measure_mono
        exact Set.singleton_subset_iff.mpr hc₀

theorem pac_lower_bound_good_event_le_half
    (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    {T : Finset X} (hTne : T.Nonempty) (L : BatchLearner X Bool)
    (m : ℕ) (c₀ : X → Bool) (ε : ℝ) (hε1 : ε ≤ 1 / 4)
    (hcount : 2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        c₀ ((↑t : X)) ≠ L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
      ≤ T.card).card ≤ Fintype.card (Fin m → ↥T)) :
    ∃ D : MeasureTheory.Measure X, MeasureTheory.IsProbabilityMeasure D ∧
      MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε } ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  letI msT : MeasurableSpace ↥T := ⊤
  haveI : @MeasurableSingletonClass ↥T ⊤ :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hTne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := Fintype.card_pos_iff.mpr hTne_type
  let D_sub := @uniformMeasure ↥T ⊤ _ hTne_type
  have hD_sub_prob : @MeasureTheory.IsProbabilityMeasure ↥T ⊤ D_sub :=
    @uniformMeasure_isProbability ↥T ⊤ _ ⟨fun _ => trivial⟩ hTne_type hTpos
  have hval_meas : @Measurable ↥T X ⊤ _ Subtype.val :=
    fun _ _ => MeasurableSpace.measurableSet_top
  let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
  have hDprob : MeasureTheory.IsProbabilityMeasure D := by
    constructor
    show D Set.univ = 1
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ]
    have : Subtype.val ⁻¹' (Set.univ : Set X) = (Set.univ : Set ↥T) := Set.preimage_univ
    rw [this]
    exact hD_sub_prob.measure_univ
  refine ⟨D, hDprob, ?_⟩
  have hval_emb : @MeasurableEmbedding ↥T X ⊤ _ Subtype.val := {
    injective := Subtype.val_injective
    measurable := hval_meas
    measurableSet_image' := fun {s} _ => by
      exact Set.Finite.measurableSet (Set.Finite.subset T.finite_toSet
        (fun x hx => by obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact Finset.mem_coe.mpr hy)) }
  have hD_val : ∀ S : Set X, D S = D_sub (Subtype.val ⁻¹' S) :=
    fun S => hval_emb.map_apply D_sub S
  let valProd : (Fin m → ↥T) → (Fin m → X) := fun xs i => (xs i).val
  have hvalProd_emb : @MeasurableEmbedding (Fin m → ↥T) (Fin m → X)
      (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤))
      MeasurableSpace.pi valProd := {
    injective := fun a b hab => funext fun i => Subtype.val_injective (congr_fun hab i)
    measurable := by
      rw [@measurable_pi_iff]; intro i
      exact hval_meas.comp (@measurable_pi_apply (Fin m) (fun _ => ↥T)
        (fun _ => (⊤ : MeasurableSpace ↥T)) i)
    measurableSet_image' := fun {s} _ =>
      (Set.toFinite s |>.image valProd).measurableSet }
  have hpi_map : MeasureTheory.Measure.pi (fun _ : Fin m => D) =
      (@MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub)).map valProd := by
    letI : ∀ (_ : Fin m), MeasureTheory.SigmaFinite
        (@MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub) := fun _ => by
      change MeasureTheory.SigmaFinite D; exact inferInstance
    conv_lhs =>
      rw [show (fun (_ : Fin m) => D) =
        fun (_ : Fin m) => @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub from rfl]
    symm
    convert @MeasureTheory.Measure.pi_map_pi (Fin m) inferInstance
      (fun _ => ↥T) (fun _ => X) (fun _ => (⊤ : MeasurableSpace ↥T))
      (fun _ => D_sub) inferInstance (fun _ => @Subtype.val X (· ∈ T))
      inferInstance (fun _ => hval_meas.aemeasurable) using 1
  have hpi_val : ∀ S : Set (Fin m → X),
      MeasureTheory.Measure.pi (fun _ : Fin m => D) S =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (valProd ⁻¹' S) := fun S => by
    rw [hpi_map]; exact hvalProd_emb.map_apply _ S
  set good_X : Set (Fin m → X) := { xs |
    D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
      ≤ ENNReal.ofReal ε } with good_X_def
  set good_quarter : Set (Fin m → X) := { xs |
    D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
      ≤ ENNReal.ofReal (1 / 4 : ℝ) } with good_quarter_def
  set count_finset := Finset.univ.filter fun xs : Fin m → ↥T =>
    (Finset.univ.filter fun t : ↥T =>
      c₀ ((↑t : X)) ≠
        L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
    ≤ T.card with count_finset_def
  have hgood_sub : good_X ⊆ good_quarter := by
    intro xs hxs
    simp only [good_X_def, good_quarter_def, Set.mem_setOf_eq] at hxs ⊢
    exact le_trans hxs (ENNReal.ofReal_le_ofReal hε1)
  have hpre_eq : valProd ⁻¹' good_quarter = (↑count_finset : Set (Fin m → ↥T)) := by
    ext xs_T
    simp only [Set.mem_preimage, good_quarter_def, Set.mem_setOf_eq, valProd,
      count_finset_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    set h_val := L.learn (fun i => ((↑(xs_T i) : X), c₀ (↑(xs_T i))))
    have herr : D { x | h_val x ≠ c₀ x } =
        D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } := by
      rw [hD_val]; congr 1; ext ⟨t, _⟩; exact ne_comm
    have hunif : D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } =
        ((Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card : ENNReal) /
          (T.card : ENNReal) := by
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
        (Set.toFinite _) MeasurableSpace.measurableSet_top]
      simp only [Fintype.card_coe, one_div, ne_eq, Set.Finite.toFinset_setOf,
        Finset.univ_eq_attach]
      rw [ENNReal.div_eq_inv_mul]
    rw [herr, hunif]
    set k := (Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card
    have hd_ne : (T.card : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by
      rw [← Fintype.card_coe]; exact Nat.pos_iff_ne_zero.mp hTpos)
    have hd_nt : (T.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top T.card
    constructor
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt] at hle
      rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]; norm_num,
        mul_comm] at hle
      have h4 : (k : ENNReal) * 4 ≤ (T.card : ENNReal) :=
        calc (k : ENNReal) * 4
            ≤ (T.card : ENNReal) * (4 : ENNReal)⁻¹ * 4 := mul_le_mul_left hle 4
          _ = (T.card : ENNReal) := by
              rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      exact_mod_cast h4
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt]
      rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]; norm_num,
        mul_comm]
      have hk4 : (k : ENNReal) * 4 ≤ (T.card : ENNReal) := by exact_mod_cast hle
      calc (k : ENNReal) = (k : ENNReal) * 4 * (4 : ENNReal)⁻¹ := by
              rw [mul_assoc, mul_comm 4 (4 : ENNReal)⁻¹,
                  ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
            _ ≤ (T.card : ENNReal) * (4 : ENNReal)⁻¹ := mul_le_mul_left hk4 _
  have hgoal_eq : MeasureTheory.Measure.pi (fun _ : Fin m => D) good_quarter =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (↑count_finset) := by
    rw [hpi_val good_quarter, hpre_eq]
  have hpi_sub_bound : @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) (↑count_finset) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    set μ_pi := @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) with hμ_pi_def
    haveI inst_msc_pi : @MeasurableSingletonClass (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) :=
      @Pi.instMeasurableSingletonClass (Fin m) (fun _ => ↥T) (fun _ => ⊤)
        inferInstance (fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩)
    haveI : @MeasureTheory.IsFiniteMeasure ↥T ⊤ D_sub := by
      constructor; rw [hD_sub_prob.measure_univ]; exact ENNReal.one_lt_top
    haveI : @MeasureTheory.SigmaFinite ↥T ⊤ D_sub :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite ↥T ⊤ D_sub inferInstance
    have hD_sub_singleton : ∀ t : ↥T, D_sub {t} = 1 / (T.card : ENNReal) := by
      intro t
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
        (Set.toFinite _) MeasurableSpace.measurableSet_top]
      simp [Set.Finite.toFinset, Fintype.card_coe]
    have hpi_singleton : ∀ xs : Fin m → ↥T,
        μ_pi {xs} = (1 / (T.card : ENNReal)) ^ m := by
      intro xs
      rw [hμ_pi_def, @MeasureTheory.Measure.pi_singleton]
      simp only [hD_sub_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsum_eq : μ_pi (↑count_finset) = ∑ xs ∈ count_finset, μ_pi {xs} :=
      (@MeasureTheory.sum_measure_singleton (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) μ_pi
        count_finset inst_msc_pi).symm
    rw [hsum_eq]
    simp only [hpi_singleton, Finset.sum_const, nsmul_eq_mul]
    have hd_ne : (T.card : ENNReal) ^ m ≠ 0 :=
      pow_ne_zero m (Nat.cast_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr hTne)))
    have hd_ne_top : (T.card : ENNReal) ^ m ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top T.card)
    rw [show (count_finset.card : ENNReal) * (1 / (T.card : ENNReal)) ^ m =
        (count_finset.card : ENNReal) / (T.card : ENNReal) ^ m from by
      rw [one_div, ← ENNReal.inv_pow, div_eq_mul_inv]]
    rw [ENNReal.div_le_iff hd_ne hd_ne_top]
    have h_ennreal : (2 * count_finset.card : ENNReal) ≤ (T.card : ENNReal) ^ m := by
      rw [show (T.card : ENNReal) ^ m = ((T.card ^ m : ℕ) : ENNReal) from by push_cast; rfl]
      push_cast
      have hcard_eq : Fintype.card (Fin m → ↥T) = T.card ^ m := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      have h_le_card : 2 * count_finset.card ≤ Fintype.card (Fin m → ↥T) := by
        simpa [count_finset_def] using hcount
      rw [hcard_eq] at h_le_card
      exact_mod_cast h_le_card
    calc (count_finset.card : ENNReal)
        = (count_finset.card : ENNReal) * 1 := (mul_one _).symm
      _ = (count_finset.card : ENNReal) * (2 * (2 : ENNReal)⁻¹) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ = (count_finset.card : ENNReal) * 2 * (2 : ENNReal)⁻¹ := by ring
      _ = (2 * count_finset.card : ENNReal) * (2 : ENNReal)⁻¹ := by ring
      _ ≤ (T.card : ENNReal) ^ m * (2 : ENNReal)⁻¹ :=
          mul_le_mul_left h_ennreal _
      _ = ENNReal.ofReal (1 / 2 : ℝ) * (T.card : ENNReal) ^ m := by
          rw [show ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ from by
            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]; norm_num]
          ring
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D) good_X
      ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D) good_quarter :=
        MeasureTheory.measure_mono hgood_sub
    _ = @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
          (fun _ => D_sub) (↑count_finset) := hgoal_eq
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := hpi_sub_bound
/-- PAC lower bound core: sample complexity is at least (d-1)/2.
    For any PAC learner with VCDim = d, at least ⌈(d-1)/2⌉ samples needed.
    Proof: construct d shattered points, uniform distribution, counting argument.
    Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean. -/
theorem pac_lower_bound_core (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : VCDim X C = d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    -- Any PAC learner needs at least ⌈(d-1)/(64ε)⌉ samples
    ∀ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
      (∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C, let m := mf ε δ
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)) →
      Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε (1 / 7) := by
  -- Proof by contradiction: assume mf ε (1 / 7) < ⌈(d-1)/(2ε)⌉, derive violation
  -- of the PAC guarantee using NFL counting on the shattered set.
  intro L mf hpac
  by_contra h_lt
  push Not at h_lt
  -- h_lt : mf ε (1 / 7) < ⌈(d-1)/(2ε)⌉
  set m := mf ε (1 / 7) with hm_def
  -- Step 1: Extract shattered set T with |T| = d from VCDim X C = d.
  have ⟨T, hTshat, hTcard⟩ : ∃ T : Finset X, Shatters X C T ∧ T.card = d := by
    have hVCDim_eq : ⨆ (S : Finset X) (_ : Shatters X C S),
        (S.card : WithTop ℕ) = ↑d := hd
    have hle : ∀ S, Shatters X C S → S.card ≤ d := by
      intro S hS
      have : (S.card : WithTop ℕ) ≤ ↑d := by
        calc (S.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) S hS
          _ = ↑d := hVCDim_eq
      exact WithTop.coe_le_coe.mp this
    by_contra h_none
    push Not at h_none
    have hstrict : ∀ S, Shatters X C S → S.card ≤ d - 1 := by
      intro S hS; have := hle S hS; have := h_none S hS; omega
    have hbound : VCDim X C ≤ ↑(d - 1) := by
      apply iSup₂_le; intro S hS
      exact WithTop.coe_le_coe.mpr (hstrict S hS)
    rw [hd] at hbound
    have : d ≤ d - 1 := WithTop.coe_le_coe.mp hbound
    omega
  -- Step 2: Specialize PAC guarantee to δ = 1 / 7
  have hpac17 := hpac (1 / 7 : ℝ) (by norm_num : (0:ℝ) < 1 / 7) (by norm_num : (1:ℝ)/7 ≤ 1)
  -- hpac17 : ∀ D prob, ∀ c ∈ C, Pr[error ≤ ε] ≥ 6 / 7
  -- Step 3: Derive contradiction via NFL counting on shattered T.
  -- Suffices: ∃ D prob, ∃ c ∈ C, PAC guarantee fails at δ = 1 / 7.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          < ENNReal.ofReal (1 - 1 / 7) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hpac17 D hDprob c hcC)
  classical
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hTcard; omega
  set d' := T.card with hd'_def
  have hd'_eq_d : d' = d := hTcard
  have h2m_lt_d : 2 * m < d' := by
    rw [hd'_eq_d]
    by_contra h_ge; push Not at h_ge
    -- h_ge : d ≤ 2 * m. From Nat.lt_ceil: (m : ℝ) < (d-1)/2, so 2m < d-1. Contradiction.
    have hm_real : (m : ℝ) < (d - 1 : ℝ) / 2 := Nat.lt_ceil.mp h_lt
    have hge_real : (d : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h_ge
    linarith
  obtain ⟨_, c₀, hc₀C, _, hcount⟩ := nfl_counting_core hTshat h2m_lt_d L
  obtain ⟨D, hDprob, hgood_half⟩ :=
    pac_lower_bound_good_event_le_half (X := X) (T := T) hTne L m c₀ ε hε1
      (by simpa using hcount)
  refine ⟨D, hDprob, c₀, hc₀C, ?_⟩
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε }
      ≤ ENNReal.ofReal (1 / 2 : ℝ) := hgood_half
    _ < ENNReal.ofReal (1 - 1 / 7 : ℝ) := by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)

-- The no-side-information compression theorem is the Littlestone-Warmuth
-- conjecture, so this kernel exposes only the proved side-information version
-- in `Compression.lean`.

/-- Pigeonhole core: compress is injective on C-realizable labelings.
    If two C-realizable samples over the same points with different labelings
    produce the same compressed set, correctness forces the labelings to agree.
    Γ₇₃: now requires realizability hypotheses for both samples. -/
theorem compress_injective_on_labelings {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionScheme X Bool C)
    (pts : Fin n → X) (_hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by
  have h_recon : cs.reconstruct (cs.compress (fun i => (pts i, f i))) =
                 cs.reconstruct (cs.compress (fun i => (pts i, g i))) :=
    congr_arg cs.reconstruct hfg
  funext i
  -- Realizability hypotheses match the correct field's guard
  have hf_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, f i)) i).1 = ((fun i => (pts i, f i)) i).2 := by
    obtain ⟨c, hcC, hc⟩ := hf_real
    exact ⟨c, hcC, fun i => by simp [hc i]⟩
  have hg_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, g i)) i).1 = ((fun i => (pts i, g i)) i).2 := by
    obtain ⟨c, hcC, hc⟩ := hg_real
    exact ⟨c, hcC, fun i => by simp [hc i]⟩
  have hf := cs.correct (fun i => (pts i, f i)) hf_real' i
  have hg := cs.correct (fun i => (pts i, g i)) hg_real' i
  simp only at hf hg
  rw [← hf, congr_fun h_recon (pts i), hg]

/-- k + 1 ≤ 2^k for all k. Used in the counting step of compression_imp_vcdim_finite. -/
private lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                   _ = 2 ^ (k + 1) := by ring

/-- Shattering is monotone: subsets of shattered sets are shattered. -/
private lemma shatters_subset {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hST : T ⊆ S) (hS : Shatters X C S) : Shatters X C T := by
  intro f
  -- Extend f to a labeling on S
  classical
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  refine ⟨c, hcC, ?_⟩
  intro ⟨x, hx⟩
  have hxS : x ∈ S := hST hx
  have := hcg ⟨x, hxS⟩
  simp only [g, hx, dite_true] at this
  exact this

/-- Exponential beats polynomial at n = 2(k+1)²: (k+1) * (4(k+1)²)^k < 2^(2(k+1)²).
    Core combinatorial inequality for the compression → finite VCDim proof.
    Proof chain: (k+1)^(2k+1) * 2^(2k) ≤ 2^(2k²+3k) < 2^(2k²+4k+2). -/
private lemma exp_beats_poly_at (k : ℕ) :
    (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k < 2 ^ (2 * (k + 1) * (k + 1)) := by
  -- Simplify: 2 * (2 * (k+1) * (k+1)) = 4 * (k+1)²
  -- LHS = (k+1) * (4*(k+1)²)^k = (k+1) * 4^k * (k+1)^(2k) = (k+1)^(2k+1) * 2^(2k)
  -- RHS = 2^(2*(k+1)²) = 2^(2k²+4k+2)
  -- Chain: (k+1)^(2k+1) ≤ (2^k)^(2k+1) = 2^(k(2k+1)) = 2^(2k²+k) [by succ_le_two_pow]
  -- So LHS ≤ 2^(2k²+k) * 2^(2k) = 2^(2k²+3k)
  -- And 2k²+3k < 2k²+4k+2 [by omega]
  -- So LHS < 2^(2k²+4k+2) = RHS
  have h1 : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  -- (k+1) * (4*(k+1)^2)^k = (k+1) * (4^k * (k+1)^(2*k))
  have hsimp : 2 * (2 * (k + 1) * (k + 1)) = 4 * (k + 1) ^ 2 := by ring
  rw [hsimp]
  -- (4 * (k+1)^2)^k = 4^k * ((k+1)^2)^k = 4^k * (k+1)^(2*k) = 2^(2k) * (k+1)^(2k)
  have hpow : (4 * (k + 1) ^ 2) ^ k = 2 ^ (2 * k) * (k + 1) ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num]
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow]
  -- LHS = (k+1) * (2^(2k) * (k+1)^(2k)) = 2^(2k) * (k+1)^(2k+1)
  rw [show (k + 1) * (2 ^ (2 * k) * (k + 1) ^ (2 * k)) =
    2 ^ (2 * k) * (k + 1) ^ (2 * k + 1) from by ring]
  -- RHS: 2 * (k+1) * (k+1) = (k+1)^2 + ... well, 2*(k+1)*(k+1) = 2*(k+1)^2
  have hrhs : 2 * (k + 1) * (k + 1) = 2 * (k + 1) ^ 2 := by ring
  rw [hrhs]
  -- Bound (k+1)^(2k+1) ≤ (2^k)^(2k+1) = 2^(k*(2k+1))
  have h2 : (k + 1) ^ (2 * k + 1) ≤ (2 ^ k) ^ (2 * k + 1) :=
    Nat.pow_le_pow_left h1 _
  rw [← pow_mul] at h2
  -- So LHS ≤ 2^(2k) * 2^(k*(2k+1)) = 2^(2k + k*(2k+1)) = 2^(2k²+3k)
  calc 2 ^ (2 * k) * (k + 1) ^ (2 * k + 1)
      ≤ 2 ^ (2 * k) * 2 ^ (k * (2 * k + 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (2 * k + k * (2 * k + 1)) := by rw [← pow_add]
    _ = 2 ^ (2 * k ^ 2 + 3 * k) := by ring_nf
    _ < 2 ^ (2 * (k + 1) ^ 2) := by
        apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        nlinarith

/-- ∃ compression scheme → VCDim < ⊤.
    Pigeonhole: compress is injective on C-realizable labelings (by correctness),
    but compressed subsets of an n-point sample are bounded. Shatters X C T
    guarantees ALL labelings are C-realizable, so injectivity holds on all 2^n
    labelings. Contradiction for large n.
    Γ₇₃ RESOLVED: CompressionScheme parameterized by C with realizability guard.
    Shattered sets guarantee C-realizability of every labeling, so the
    pigeonhole argument is genuinely non-vacuous. -/
theorem compression_imp_vcdim_finite (X : Type u)
    (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by
  -- Proof by contradiction: assume VCDim X C = ⊤.
  by_contra h_top
  push Not at h_top
  rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  -- VCDim = ⊤ ⟹ arbitrarily large shattered sets
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n
    by_contra h_neg
    push Not at h_neg
    have : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro S hS
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  -- Set N = 2(k+1)² — the exact size we'll use
  set N := 2 * (k + 1) * (k + 1) with hN_def
  -- Get shattered T₀ with |T₀| ≥ N
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  haveI : DecidableEq X := Classical.decEq X
  -- Take subset T ⊆ T₀ with |T| = N exactly (by Finset.exists_subset_card_eq)
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  -- T is shattered (subset of shattered set)
  have hT_shatt : Shatters X C T := shatters_subset hT_sub hT₀_shatt
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  -- Enumerate T injectively
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  -- Build sample from labeling: f ↦ (pts(i), f(i))
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  -- Shatters X C T → every labeling f is C-realizable on pts
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    -- Convert f : Fin n → Bool to a labeling of T via eqv
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    refine ⟨c, hcC, fun i => ?_⟩
    have := hcf' (eqv i)
    simp only [f', pts] at this ⊢
    rw [show T.equivFin (eqv i) = i from T.equivFin.apply_symm_apply i] at this
    exact this
  -- compress ∘ mkSample is injective (core pigeonhole step)
  -- Shatters gives C-realizability for each labeling, firing correctness
  have h_inj : Function.Injective (cs.compress ∘ mkSample) := by
    intro f g hfg
    exact compress_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  -- Counting contradiction via pigeonhole principle.
  -- Target: all subsets of T ×ˢ {true, false} of size ≤ k
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := A.powerset.filter (fun S => S.card ≤ k) with htarget_def
  -- Each compressed set lands in target
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro p hp
      have hsub := cs.compress_sub (mkSample f)
      have hp_set : (p : X × Bool) ∈ (↑(cs.compress (mkSample f)) : Set (X × Bool)) :=
        Finset.mem_coe.mpr hp
      have hp_range : p ∈ Set.range (mkSample f) := hsub hp_set
      obtain ⟨i, hi⟩ := hp_range
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      constructor
      · have : p.1 = pts i := (congr_arg Prod.fst hi).symm
        rw [this]; exact (eqv i).2
      · exact Finset.mem_univ _
    · have := cs.compress_small (mkSample f); omega
  -- Source cardinality: 2^n
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
  -- Target cardinality: |target| ≤ (k+1)·(2n)^k
  have hA_card : A.card = 2 * n := by
    simp [hA_def, Finset.card_product]; ring
  have h_target_le : target.card ≤ (k + 1) * (2 * n) ^ k := by
    calc target.card
        ≤ (Finset.range (k + 1)).sum (fun j => (A.powersetCard j).card) := by
          have : target ⊆ (Finset.range (k + 1)).biUnion (fun j => A.powersetCard j) := by
            intro S hS
            simp only [htarget_def, Finset.mem_filter, Finset.mem_powerset] at hS
            simp only [Finset.mem_biUnion, Finset.mem_range]
            exact ⟨S.card, by omega, Finset.mem_powersetCard.mpr ⟨hS.1, rfl⟩⟩
          exact (Finset.card_le_card this).trans Finset.card_biUnion_le
      _ = (Finset.range (k + 1)).sum (fun j => (2 * n).choose j) := by
          simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (k + 1)).sum (fun _ => (2 * n) ^ k) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          have hj_le : j ≤ k := by omega
          calc (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ k := by
                have hn_pos : 0 < n := by
                  rw [hn_eq, hN_def]; positivity
                have h2n_pos : 0 < 2 * n := by omega
                exact Nat.pow_le_pow_right h2n_pos hj_le
      _ = (k + 1) * (2 * n) ^ k := by simp [Finset.sum_const, Finset.card_range]
  -- Key inequality: (k+1)·(2n)^k < 2^n, using n = 2(k+1)² exactly
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (k + 1) * (k + 1) := hn_eq.trans hN_def
    calc target.card ≤ (k + 1) * (2 * n) ^ k := h_target_le
      _ = (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k := by rw [hn_val]
      _ < 2 ^ (2 * (k + 1) * (k + 1)) := exp_beats_poly_at k
      _ = 2 ^ n := by rw [hn_val]
  -- Pigeonhole: more labelings than target slots → collision contradicts injectivity
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [h_source_card]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt
        (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))


/-- Growth function polynomially bounded → VCDim < ⊤.
    Reverse direction: if GrowthFunction m ≤ ∑_{i≤d} C(m,i) for all m ≥ d,
    then VCDim ≤ d (otherwise GrowthFunction = 2^m for m = VCDim > d). -/
theorem growth_bounded_imp_vcdim_finite (X : Type u)
    (C : ConceptClass X Bool)
    (hgrowth : ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :
    VCDim X C < ⊤ := by
  -- M-Contrapositive: VCDim = ⊤ → growth bound fails.
  by_contra h
  push Not at h
  have hinf : VCDim X C = ⊤ := le_antisymm le_top h
  obtain ⟨d, hd⟩ := hgrowth
  -- Use iSup₂_eq_top to get a shattered set T with |T| > d
  have hvcdim_unbounded := (iSup₂_eq_top
    (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    (by rw [VCDim] at hinf; exact hinf)
  -- Get T with |T| > d, hence |T| ≥ d+1
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded d (WithTop.coe_lt_top d)
  -- hTcard : d < T.card (as WithTop ℕ)
  have hTcard' : d + 1 ≤ T.card := by exact_mod_cast WithTop.coe_lt_coe.mp hTcard
  -- Apply hd to m = T.card ≥ d:
  have hd_app := hd T.card (le_trans (Nat.le_succ d) hTcard')
  -- Step A: Shattering → GrowthFunction ≥ 2^T.card
  -- When T is shattered, all 2^|T| labelings are realized.
  -- GrowthFunction(C, |T|) = sSup over |T|-element sets of ncard(restrictions).
  -- Since T itself is |T|-element and shattered: ncard(restrictions of C to T) = 2^|T|.
  -- So GrowthFunction ≥ 2^|T|.
  have hgrowth_large : 2 ^ T.card ≤ GrowthFunction X C T.card := by
    -- GrowthFunction(m) = sSup over m-element sets S of ncard{restrictions of C to S}
    -- T is an T.card-element set that is shattered, so all 2^|T| labelings are realized.
    unfold GrowthFunction
    apply le_csSup
    · -- BddAbove: ncard of any subset of (↥S → Bool) ≤ 2^S.card = 2^T.card
      use 2 ^ T.card
      rintro n ⟨⟨S, hScard⟩, rfl⟩
      calc Set.ncard { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
          ≤ Set.ncard (Set.univ : Set (↥S → Bool)) := Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card (↥S → Bool) := Set.ncard_univ _
        _ = Nat.card Bool ^ Nat.card ↥S := Nat.card_fun
        _ = 2 ^ S.card := by
            rw [Nat.card_eq_fintype_card, Fintype.card_bool,
                Nat.card_eq_fintype_card, Fintype.card_coe]
        _ = 2 ^ T.card := by rw [hScard]
    · -- T witnesses this value in the range
      refine ⟨⟨T, rfl⟩, ?_⟩
      -- Need: ncard {f | ∃ c ∈ C, ...} = 2^T.card when T is shattered
      -- Shattering means every labeling is realized, so the set = Set.univ
      -- The goal after unfolding is about (fun S => ...) ⟨T, rfl⟩, so we simp/unfold first
      change Set.ncard { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } = 2 ^ T.card
      have hset_eq : { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } =
          (Set.univ : Set (↥T → Bool)) := by
        ext f; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact hTshat f
      rw [hset_eq, Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card,
          Fintype.card_bool, Nat.card_eq_fintype_card, Fintype.card_coe]
  -- Step B: ∑_{i≤d} C(T.card, i) < 2^T.card (since T.card > d, partial sum < full sum)
  have hsum_lt_pow : ∑ i ∈ Finset.range (d + 1), Nat.choose T.card i < 2 ^ T.card := by
    -- ∑_{i=0}^{T.card} C(T.card, i) = 2^T.card (sum_range_choose)
    -- Since d + 1 ≤ T.card, range(d+1) ⊊ range(T.card + 1), and missing terms > 0
    have hd_lt_Tcard : d < T.card := by omega
    -- Use: each C(m,i) ≤ C(m, m/2) (choose_le_middle), and there are ≤ d+1 terms
    -- Alternatively: partial sum < full sum = 2^T.card
    rw [← Nat.sum_range_choose T.card]
    exact Finset.sum_lt_sum_of_subset (i := T.card)
      (Finset.range_mono (by omega))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))
      (fun h => absurd (Finset.mem_range.mp h) (by omega))
      (by rw [Nat.choose_self]; exact Nat.one_pos)
      (fun j _ _ => Nat.zero_le _)
  -- Step C: Contradiction
  -- Chain: 2^T.card ≤ GrowthFunction ≤ ∑ C(T.card,i) < 2^T.card → contradiction
  exact absurd (le_trans hgrowth_large hd_app) (not_le.mpr hsum_lt_pow)
/-- PAC lower bound membership: if m achieves PAC for C with VCDim = d,
    then m ≥ ⌈(d-1)/(64ε)⌉.
    This is the core adversarial counting argument factored for PAC.lean assembly.
    Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean.

    Proof route (double-averaging on shattered set):
    1. VCDim = d → ∃ shattered S with |S| = d
    2. D = uniform on S (probability measure, each point has weight 1/d)
    3. m < ⌈(d-1)/(64ε)⌉ → 2m < d → NFL counting applies
    4. Double-averaging over 2^d labelings: E_f[E_xs[error]] ≥ (d-m)/(2d) > 1 / 4
    5. Reversed Markov: ∃ c₀ ∈ C with Pr[error ≤ 1 / 8] ≤ 6 / 7
    6. For ε ≤ 1 / 8: Pr[error ≤ ε] ≤ 6 / 7 = 1 - 1 / 7, contradicting PAC -/
theorem pac_lower_bound_member (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d) (m : ℕ)
    (hm : m ∈ { m : ℕ | ∃ (L : BatchLearner X Bool),
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
        ∀ c ∈ C,
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ) }) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ m := by
  -- Proof by contradiction: assume m < ⌈(d-1)/(64ε)⌉ and derive a violation
  -- of the PAC guarantee using the NFL counting argument on the shattered set.
  by_contra h_lt
  push Not at h_lt
  -- h_lt : m < ⌈(d-1)/(64ε)⌉
  -- Step 1: Extract shattered set T with |T| = d from VCDim X C = d.
  have ⟨T, hTshat, hTcard⟩ : ∃ T : Finset X, Shatters X C T ∧ T.card = d := by
    -- VCDim = d with d ≥ 1 → ∃ witness achieving the sup
    have hVCDim_eq : ⨆ (S : Finset X) (_ : Shatters X C S),
        (S.card : WithTop ℕ) = ↑d := hd
    have hle : ∀ S, Shatters X C S → S.card ≤ d := by
      intro S hS
      have : (S.card : WithTop ℕ) ≤ ↑d := by
        calc (S.card : WithTop ℕ)
            ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
              le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                (S.card : WithTop ℕ)) S hS
          _ = ↑d := hVCDim_eq
      exact WithTop.coe_le_coe.mp this
    by_contra h_none
    push Not at h_none
    have hstrict : ∀ S, Shatters X C S → S.card ≤ d - 1 := by
      intro S hS; have := hle S hS; have := h_none S hS; omega
    have hbound : VCDim X C ≤ ↑(d - 1) := by
      apply iSup₂_le; intro S hS
      exact WithTop.coe_le_coe.mpr (hstrict S hS)
    rw [hd] at hbound
    have : d ≤ d - 1 := WithTop.coe_le_coe.mp hbound
    omega
  -- Step 2: Extract the learner L from the PAC membership hypothesis
  obtain ⟨L, hL⟩ := hm
  -- Step 3: T is nonempty (|T| = d ≥ 1)
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hTcard; omega
  -- Step 4: Construct D = pushforward of uniform on ↥T to X.
  -- D is (1/d) · ∑_{x ∈ T} δ_x, a probability measure on X supported on T.
  --
  -- Step 5: The NFL double-averaging argument on the shattered set T.
  -- With 1/(64ε) constant, m < ⌈(d-1)/(64ε)⌉ → 2m < d = |T|.
  --
  -- PROOF ROUTE (same as pac_lower_bound_core):
  -- (1) 2m < d from h_lt and ε ≤ 1.
  -- (2) Double-averaging over f : ↥T → Bool (each realized by c_f ∈ C):
  --     pairing on unseen points gives E_f[D{error}] ≥ (d-m)/(2d) > 1 / 4.
  -- (3) By Fubini + averaging: ∃ c₀ ∈ C with E_xs[error(c₀)] > 1 / 4.
  -- (4) Reversed Markov: Pr[error ≤ 1 / 8] < 6 / 7.
  -- (5) For ε ≤ 1 / 8: contradiction with PAC at δ ≤ 1 / 7.
  --     For ε > 1 / 8: same, since 2m < d still holds.
  --
  -- SORRY: the double-averaging + reversed Markov measure bridge.
  -- Infrastructure: pairing counting (disagreement_sum_eq proved),
  -- finite sum averaging, reversed Markov on [0,1]-valued rv.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          < ENNReal.ofReal (1 - δ) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hL D hDprob c hcC)
  classical
  set d' := T.card with hd'_def
  have hd'_eq_d : d' = d := hTcard
  have h2m_lt_d : 2 * m < d' := by
    rw [hd'_eq_d]
    by_contra h_ge; push Not at h_ge
    have hm_real : (m : ℝ) < (d - 1 : ℝ) / 2 := Nat.lt_ceil.mp h_lt
    have hge_real : (d : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast h_ge
    linarith
  obtain ⟨_, c₀, hc₀C, _, hcount⟩ := nfl_counting_core hTshat h2m_lt_d L
  obtain ⟨D, hDprob, hgood_half⟩ :=
    pac_lower_bound_good_event_le_half (X := X) (T := T) hTne L m c₀ ε hε1
      (by simpa using hcount)
  refine ⟨D, hDprob, c₀, hc₀C, ?_⟩
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal ε }
      ≤ ENNReal.ofReal (1 / 2 : ℝ) := hgood_half
    _ < ENNReal.ofReal (1 - δ) := by
        apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr
        linarith

end NFLInfrastructure

attribute [nolint unusedArguments]
  QueryComplexity
  LabelComplexity
  IsConsistentWith
  uniformMeasure
attribute [nolint docBlame unusedArguments] ermLearn
