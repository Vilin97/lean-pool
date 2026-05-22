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
noncomputable def QueryComplexity (X : Type u)
    (C : ConceptClass X Bool) : ℕ :=
  sInf { _q : ℕ | ∃ (L : ActiveLearner X Bool),
    ∀ (c : Concept X Bool), c ∈ C →
      ∀ (mq : MembershipOracle X Bool), mq.target = c →
        L.learnMQ mq = c }

/-- Label complexity: minimum labels for active PAC learning.
    Formally: sInf { k | ∃ active learner using ≤ k labels achieving PAC(ε,δ) }.
    The current oracle model abstracts away the concrete label counter. -/
noncomputable def LabelComplexity (X : Type u)
    (C : ConceptClass X Bool) : ℝ → ℝ → ℕ :=
  fun ε δ => sInf { _k : ℕ | ε = ε ∧ δ = δ ∧ ∃ (L : ActiveLearner X Bool),
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
/-- Empirical risk minimizer over a nonempty hypothesis space. -/
noncomputable def ermLearn (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (hne : H.Nonempty)
    {m : ℕ} (S : Fin m → X × Y) : Concept X Y :=
  if h : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Y h₀ S loss ≤ EmpiricalError X Y h' S loss
  then h.choose
  else hne.some

theorem ermLearn_in_H (X : Type u) (Y : Type v)
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
noncomputable def ERM (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y)
    (hne : H.Nonempty) : BatchLearner X Y where
  hypotheses := H
  learn := fun {_m} S => ermLearn X Y H loss hne S
  output_in_H := fun S => ermLearn_in_H X Y H loss hne S

end ERM_section

section TrueError

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
  rw [← MeasureTheory.Measure.real_def, ← MeasureTheory.integral_indicator_one hmeas]
  have integrand_eq : (fun x => Set.indicator {x | h x ≠ c x} (1 : X → ℝ) x) =
      (fun x => zeroOneLoss Bool (h x) (c x)) := by
    ext x
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, zeroOneLoss]
    split_ifs <;> simp_all
  rw [integrand_eq]
  have hphi : Measurable (fun x => (x, c x) : X → X × Bool) := measurable_id.prodMk hcmeas
  have hf_meas : Measurable (fun p : X × Bool => zeroOneLoss Bool (h p.1) p.2) :=
    Measurable.ite (measurableSet_eq_fun (hhmeas.comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  exact (MeasureTheory.integral_map hphi.aemeasurable
    hf_meas.stronglyMeasurable.aestronglyMeasurable).symm

end TrueError

section EmpiricalMeasureError

/-- Empirical measure: the uniform distribution over a finite sample.
    D̂_S = (1/m) Σᵢ δ_{xᵢ} where S = (x₁,...,xₘ).
    This is a probability measure when m > 0. -/
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
    under 0-1 loss (up to ENNReal ↔ ℝ conversion). -/
theorem empiricalMeasureError_eq_empiricalError (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    (EmpiricalMeasureError X h c xs).toReal =
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by
  have hm' : m ≠ 0 := by omega
  unfold EmpiricalMeasureError TrueError EmpiricalMeasure
  rw [dif_neg hm']
  unfold EmpiricalError
  rw [if_neg hm', MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finset_sum_apply]
  simp only [MeasureTheory.Measure.dirac_apply, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  rw [smul_eq_mul]
  have hne_top : ∀ i ∈ Finset.univ, (if h (xs i) ≠ c (xs i) then (1 : ENNReal) else 0) ≠ ⊤ := by
    intro i _; split_ifs <;> simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum hne_top,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
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

/-- A hypothesis h is consistent with labeled sample S. -/
def IsConsistentWith (X : Type u) (Y : Type v)
    (h : Concept X Y) {m : ℕ} (S : Fin m → X × Y) : Prop :=
  ∀ i : Fin m, h (S i).1 = (S i).2

/-- Consistency implies zero empirical 0-1 error. -/
theorem consistent_imp_zero_empiricalError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (hcons : IsConsistentWith X Bool h (fun i => (xs i, c (xs i)))) :
    EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) = 0 := by
  unfold EmpiricalError
  rw [if_neg (by omega : m ≠ 0)]
  have hsum : (Finset.univ.sum fun i : Fin m =>
      zeroOneLoss Bool (h ((fun i => (xs i, c (xs i))) i).1)
        ((fun i => (xs i, c (xs i))) i).2) = 0 :=
    Finset.sum_eq_zero (fun i _ => by simp only; unfold zeroOneLoss; rw [if_pos (hcons i)])
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
  · intro hzero
    rw [div_eq_zero_iff] at hzero
    cases hzero with
    | inl hsum =>
      have hterms := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hloss_nonneg _ _) |>.mp hsum
      intro i
      exact hfaith.loss_zero_imp_eq _ _ (hterms i (Finset.mem_univ i))
    | inr hm_zero => exact absurd hm_zero (ne_of_gt (Nat.cast_pos.mpr hm))
  · intro hcons
    have : (Finset.univ.sum fun i : Fin m => loss (h (S i).1) (S i).2) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hcons i]; exact hfaith.loss_self_zero _)
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
  set S' := (fun i => (S i, c (S i)))
  have hEmp_nonneg : ∀ h' : Concept X Bool, 0 ≤ EmpiricalError X Bool h' S' loss := by
    intro h'
    unfold EmpiricalError
    split_ifs with hm
    · rfl
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => hloss_nonneg _ _)) (Nat.cast_nonneg m)
  have hc_emp_zero : EmpiricalError X Bool c S' loss = 0 := by
    unfold EmpiricalError
    split_ifs with hm
    · rfl
    · rw [Finset.sum_eq_zero (fun i _ => hfaith.loss_self_zero _), zero_div]
  have hexists : ∃ h₀ ∈ H, ∀ h' ∈ H,
      EmpiricalError X Bool h₀ S' loss ≤ EmpiricalError X Bool h' S' loss :=
    ⟨c, hreal hcC, fun h' _ => by rw [hc_emp_zero]; exact hEmp_nonneg h'⟩
  unfold ermLearn
  rw [dif_pos hexists]
  obtain ⟨_, hch_min⟩ := hexists.choose_spec
  have hch_zero : EmpiricalError X Bool hexists.choose S' loss = 0 :=
    le_antisymm (by have := hch_min c (hreal hcC); rw [hc_emp_zero] at this; exact this)
      (hEmp_nonneg _)
  by_cases hm : (0 : ℕ) < m
  · exact (empError_zero_iff_consistent hexists.choose hm S' loss hfaith hloss_nonneg).mp hch_zero
  · have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hm)
    subst hm0
    intro i; exact i.elim0

end Consistency

section ConcentrationInfrastructure

/-- A function f : (Fin m → X) → ℝ has bounded differences if changing
    any one coordinate changes f by at most c. -/
def HasBoundedDifferences {X : Type u} {m : ℕ} (f : (Fin m → X) → ℝ) (c : ℝ) : Prop :=
  ∀ (xs : Fin m → X) (i : Fin m) (x' : X),
    |f xs - f (Function.update xs i x')| ≤ c

/-- EmpiricalError of a fixed hypothesis h is a bounded-difference function
    of the sample, with constant 1/m. -/
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
  rw [← sub_div, abs_div, show |(m : ℝ)| = m from abs_of_nonneg (Nat.cast_nonneg m)]
  suffices h_bound : |∑ x : Fin m, zeroOneLoss Bool (h (xs x)) (c (xs x)) -
    ∑ x : Fin m, zeroOneLoss Bool (h (Function.update xs j x' x))
      (c (Function.update xs j x' x))| ≤ 1 from div_le_div_of_nonneg_right h_bound hm_pos.le
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
    MeasureTheory.prob_le_one), MeasureTheory.IsProbabilityMeasure.measure_univ]
  calc ENNReal.ofReal (1 - δ)
      = 1 - ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_sub 1 (le_of_lt hδ), ENNReal.ofReal_one]
    _ ≤ 1 - μ s := tsub_le_tsub_left hbound 1

/-- One-sided Hoeffding: for a fixed h with TrueError(h,c,D) = p > ε,
    the probability that h is consistent on all m IID samples is ≤ (1-ε)^m. -/
theorem consistent_tail_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : D { x | h x ≠ c x } ≥ ENNReal.ofReal ε)
    (hmeas : MeasurableSet { x | h x ≠ c x }) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) }
      ≤ ENNReal.ofReal ((1 - ε) ^ m) := by
  rw [show { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) } =
      Set.pi Set.univ (fun _ : Fin m => { x : X | h x = c x }) from by
    ext xs; simp [Set.mem_pi],
    MeasureTheory.Measure.pi_pi]
  have hD_agree : D { x | h x = c x } ≤ ENNReal.ofReal (1 - ε) := by
    rw [show { x : X | h x = c x } = { x : X | h x ≠ c x }ᶜ from by ext x; simp,
        MeasureTheory.measure_compl hmeas (MeasureTheory.measure_ne_top D _),
        MeasureTheory.IsProbabilityMeasure.measure_univ,
        show ENNReal.ofReal (1 - ε) = 1 - ENNReal.ofReal ε from by
          rw [ENNReal.ofReal_sub 1 (le_of_lt hε), ENNReal.ofReal_one]]
    exact tsub_le_tsub_left herr 1
  calc ∏ i : Fin m, D { x | h x = c x }
      ≤ ∏ _i : Fin m, ENNReal.ofReal (1 - ε) := Finset.prod_le_prod' (fun i _ => hD_agree)
    _ = ENNReal.ofReal ((1 - ε) ^ m) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 1 - ε)]

/-- Sample-dependent covering lemma: for a FIXED sample xs : Fin m → X,
    bad hypotheses in C can be covered by at most GrowthFunction(C,m) representatives. -/
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
        ∃ j : Fin n, ∀ i, reps j (xs i) = c (xs i) := by aesop

lemma pow_mul_exp_neg_le_factorial_div {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ d * Real.exp (-t) ≤ ↑((d + 1).factorial) / t := by
  have h1 : t ^ (d + 1) / ↑((d + 1).factorial) ≤ Real.exp t :=
    Real.pow_div_factorial_le_exp t (le_of_lt ht) (d + 1)
  have h2 : t ^ (d + 1) ≤ ↑((d + 1).factorial) * Real.exp t := by
    have := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (d + 1)))).mp h1
    linarith [mul_comm (Real.exp t) (↑(d + 1).factorial)]
  rw [pow_succ] at h2
  rw [le_div_iff₀ ht]
  calc t ^ d * Real.exp (-t) * t
      = t ^ (d + 1) * Real.exp (-t) := by ring_nf
    _ ≤ ↑((d + 1).factorial) * Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (-t)))
    _ = ↑((d + 1).factorial) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- VCDim < ⊤ → growth function polynomially bounded by partial binomial sum.
    Forward direction of fundamental_theorem conjunct 5.
    Uses Sauer-Shelah: GrowthFunction(m) ≤ ∑_{i≤d} C(m,i) where d = VCDim. -/
theorem vcdim_finite_imp_growth_bounded (X : Type u)
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ, VCDim X C = (v : WithTop ℕ) :=
    let ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
    ⟨n, hn.symm⟩
  haveI : DecidableEq X := Classical.decEq X
  use v
  intro m hm
  unfold GrowthFunction
  apply csSup_le'
  rintro n ⟨⟨S, hSm⟩, rfl⟩
  change { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }.ncard ≤
    ∑ i ∈ Finset.range (v + 1), m.choose i
  set RS : Set (↥S → Bool) := { f | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
  have hRS_finite : Set.Finite RS := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  set RS_fs := hRS_finite.toFinset
  rw [Set.ncard_eq_toFinset_card RS hRS_finite]
  haveI : DecidableEq ↥S := Classical.typeDecidableEq _
  haveI : DecidableEq (Finset ↥S) := Classical.typeDecidableEq _
  let toSub : (↥S → Bool) → Finset ↥S := fun f => Finset.univ.filter (fun x => f x = true)
  have h_toSub_inj : Function.Injective toSub := fun f g hfg => by
    funext x
    have := Finset.ext_iff.mp hfg x
    simp only [toSub, Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  set 𝒜 := RS_fs.image toSub
  have h_vcdim_le : 𝒜.vcDim ≤ v := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT_mem
    have hT_shat : 𝒜.Shatters T := Finset.mem_shatterer.mp hT_mem
    suffices hT_lift : Shatters X C (T.map ⟨Subtype.val, Subtype.val_injective⟩) by
      have hle : ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ) ≤ v :=
        hv ▸ le_iSup₂_of_le _ hT_lift le_rfl
      rw [Finset.card_map] at hle
      exact_mod_cast hle
    intro f
    let fb : ↥S → Bool := fun y =>
      if hy : y ∈ T then f ⟨↑y, Finset.mem_map.mpr ⟨y, hy, rfl⟩⟩ else false
    let t : Finset ↥S := T.filter (fun y => fb y = true)
    have ht_sub : t ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA_mem, hTA⟩ := hT_shat ht_sub
    obtain ⟨g, hg_fs, hg_eq⟩ := Finset.mem_image.mp hA_mem
    obtain ⟨c, hcC, hcg⟩ := hRS_finite.mem_toFinset.mp hg_fs
    refine ⟨c, hcC, ?_⟩
    intro ⟨x, hx_mem⟩
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx_mem
    obtain ⟨y, hyT, rfl⟩ := hx_mem
    have hcgy : c ↑y = g y := hcg y
    have hy_in_A : y ∈ A ↔ g y = true := by subst hg_eq
                                            simp [toSub, Finset.mem_filter]
    have hy_in_t : y ∈ t ↔ fb y = true := by simp [t, Finset.mem_filter, hyT]
    have hy_inter : y ∈ T ∩ A ↔ y ∈ t :=
      ⟨fun h => (Finset.ext_iff.mp hTA y).mp h, fun h => (Finset.ext_iff.mp hTA y).mpr h⟩
    have key : g y = fb y := by
      cases hgy : g y <;> cases hfby : fb y
      · rfl
      · exact absurd (hy_in_A.mp (Finset.mem_inter.mp (hy_inter.mpr (hy_in_t.mpr hfby))).2)
          (by simp_all)
      · exact absurd (hy_in_t.mp (hy_inter.mp (Finset.mem_inter.mpr ⟨hyT, hy_in_A.mpr hgy⟩)))
          (by simp_all)
      · rfl
    rw [hcgy, key]
    simp [fb, hyT]
  have h3 := @Finset.card_shatterer_le_sum_vcDim ↥S _ 𝒜
  calc RS_fs.card
      = 𝒜.card := (Finset.card_image_of_injective _ h_toSub_inj).symm
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by
        rw [← Fintype.card_coe S]
        exact h3
    _ ≤ ∑ k ∈ Finset.Iic v, S.card.choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr h_vcdim_le)
    _ = ∑ k ∈ Finset.range (v + 1), S.card.choose k := by
        congr 1; ext x; simp [Finset.mem_Iic, Finset.mem_range]
    _ = ∑ k ∈ Finset.range (v + 1), m.choose k := by rw [hSm]

end ConcentrationInfrastructure

section UniformConvergence

/-- Uniform convergence of empirical error to true error over a hypothesis class. -/
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

/-- Quantitative uniform convergence: with explicit sample complexity bound. -/
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
  let learnFn : {m : ℕ} → (Fin m → X × Bool) → Concept X Bool := fun {m} S =>
    if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2 then h.choose else hC.some
  have learn_in_H : ∀ {m : ℕ} (S : Fin m → X × Bool), learnFn S ∈ C := by
    intro m S
    change (if h : ∃ h₀ ∈ C, ∀ i : Fin m, h₀ (S i).1 = (S i).2
          then h.choose else hC.some) ∈ C
    split
    · next h => exact h.choose_spec.1
    · exact hC.some_mem
  let L : BatchLearner X Bool := { hypotheses := C, learn := learnFn, output_in_H := learn_in_H }
  let mf : ℝ → ℝ → ℕ := fun ε δ =>
    if hε : 0 < ε then if hδ : 0 < δ then (hUC ε δ hε hδ).choose else 0 else 0
  refine ⟨L, mf, ?_⟩
  intro ε δ hε hδ D hD c hcC
  have hmf : mf ε δ = (hUC ε δ hε hδ).choose := by simp only [mf, dif_pos hε, dif_pos hδ]
  set m := mf ε δ
  have hUC_inst := (hUC ε δ hε hδ).choose_spec D hD c m (by rw [hmf])
  apply ge_trans _ hUC_inst
  apply MeasureTheory.OuterMeasure.mono
  intro xs hxs
  simp only [Set.mem_setOf_eq] at hxs ⊢
  set S := (fun i => (xs i, c (xs i)) : Fin m → X × Bool) with hS_def
  set h₀ := L.learn S
  have hh₀C : h₀ ∈ C := L.output_in_H S
  have hcons : IsConsistentWith X Bool h₀ S := by
    have hexists : ∃ h₁ ∈ C, ∀ i : Fin m, h₁ ((fun i => (xs i, c (xs i))) i).1 =
        ((fun i => (xs i, c (xs i))) i).2 := ⟨c, hcC, fun i => rfl⟩
    unfold IsConsistentWith
    intro i
    change learnFn S (S i).1 = (S i).2
    simp only [learnFn, hS_def, dif_pos hexists]
    exact (hexists.choose_spec).2 i
  have hxs_h₀ := hxs h₀ hh₀C
  have hempzero : EmpiricalError X Bool h₀ S (zeroOneLoss Bool) = 0 := by
    unfold EmpiricalError
    split_ifs with hm0
    · rfl
    · rw [Finset.sum_eq_zero (fun i _ => by unfold zeroOneLoss; rw [if_pos (hcons i)]), zero_div]
  unfold TrueErrorReal TrueError at hxs_h₀
  rw [hempzero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hxs_h₀
  have hne_top : D {x | h₀ x ≠ c x} ≠ ⊤ := MeasureTheory.measure_ne_top D _
  have hlt : D {x | h₀ x ≠ c x} < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hxs_h₀
  exact le_of_lt hlt

end UniformConvergence

section ConcentrationBridge

/-- Sample complexity for PAC learning with VCDim = d. -/
noncomputable def PACsampleComplexity (d : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil ((8 / ε) * (d * Real.log (2 / ε) + Real.log (2 / δ)))

/-- The sample complexity bound is positive for valid parameters.
    This is a prerequisite for all PAC bounds. -/
theorem pac_sample_complexity_pos (d : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d) :
    0 < PACsampleComplexity d ε δ := by
  unfold PACsampleComplexity
  apply Nat.lt_ceil.mpr
  simp only [Nat.cast_zero]
  exact mul_pos (div_pos (by norm_num) hε) (add_pos
    (mul_pos (Nat.cast_pos.mpr hd) (Real.log_pos ((one_lt_div hε).mpr (by linarith))))
    (Real.log_pos ((one_lt_div hδ).mpr (by linarith))))

end ConcentrationBridge

/-- Regret: cumulative excess loss of online learner vs best fixed hypothesis. -/
noncomputable def Regret (X : Type u) (Y : Type v)
    (L : OnlineLearner X Y) (H : HypothesisSpace X Y)
    (seq : ℕ → X × Y) (T : ℕ) (loss : LossFunction Y) : ℝ :=
  let cumulLoss := L.cumulativeLoss loss ((List.range T).map seq)
  let seqList := (List.range T).map seq
  let bestFixed := sInf ((fun h => fixedHypothesisLoss h loss seqList) '' H)
  cumulLoss - bestFixed

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
  conv_lhs =>
    arg 2; ext f
    rw [show (univ.filter fun x => f x ≠ h x).card =
      ∑ x : α, if f x ≠ h x then 1 else 0 from by simp [card_filter]]
  rw [sum_comm]
  suffices ∀ x : α, ∑ f : α → Bool, (if f x ≠ h x then 1 else 0) =
      2 ^ (Fintype.card α - 1) by
    simp only [this, sum_const, card_univ, smul_eq_mul]
  intro x
  rw [show (∑ f : α → Bool, if f x ≠ h x then (1 : ℕ) else 0) =
      (univ.filter fun f : α → Bool => f x ≠ h x).card from by rw [card_filter]]
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
              · subst hyx
                cases hfx : f y <;> cases hhx : h y <;> simp_all
              · rfl
            right_inv := by intro g; ext ⟨y, hy⟩; simp [hy] }]
  rw [Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

/-- Pigeonhole consequence: for any h on a Fintype with card ≥ 2,
    there exists a function f disagreeing with h on more than |α|/4 points.
    This is the per-sample NFL counting lemma. -/
theorem exists_many_disagreements {α : Type*} [Fintype α]
    (h : α → Bool) (hcard : 2 ≤ Fintype.card α) :
    ∃ f : α → Bool,
      Fintype.card α < 4 * (Finset.univ.filter fun x => f x ≠ h x).card := by
  classical
  by_contra H
  push Not at H
  have H' : ∀ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4 :=
    fun f => by have := H f
                omega
  have hsum_le : ∑ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤
      Fintype.card (α → Bool) * (Fintype.card α / 4) :=
    calc ∑ f : α → Bool, (Finset.univ.filter fun x => f x ≠ h x).card
        ≤ ∑ _f : α → Bool, Fintype.card α / 4 :=
          Finset.sum_le_sum fun f _ => H' f
      _ = Fintype.card (α → Bool) * (Fintype.card α / 4) := by
          simp [Finset.sum_const, Finset.card_univ]
  have hsum_eq := disagreement_sum_eq h
  rw [hsum_eq] at hsum_le
  have hcard_fun : Fintype.card (α → Bool) = 2 ^ Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [hcard_fun] at hsum_le
  set n := Fintype.card α with hn
  have hn_pos : 1 ≤ n := by omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 from by omega]
    ring
  rw [hpow] at hsum_le
  have hpow_pos : 0 < 2 ^ (n - 1) := Nat.pos_of_ne_zero (by positivity)
  have key : n ≤ 2 * (n / 4) := Nat.le_of_mul_le_mul_right
    (by linarith [hsum_le] : n * 2 ^ (n - 1) ≤ (2 * (n / 4)) * 2 ^ (n - 1))
    hpow_pos
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
  have hdc_le_n : ∀ f : α → Bool, disagree_count f ≤ n := fun f => Finset.card_filter_le _ _
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
    rw [htotal, disagreement_sum_eq h] at hadd
    nlinarith [hpow]
  set S := (Finset.univ.filter fun f : α → Bool =>
    disagree_count f ≤ n / 4).card with hS_def
  have hmarkov : S * (n - n / 4) ≤ n * 2 ^ (n - 1) :=
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
  have h3_gt : 2 * n < 3 * (n - n / 4) := by omega
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
  set seen := Finset.image xs Finset.univ
  let flip : (α → Bool) → (α → Bool) := fun f t => if t ∈ seen then f t else !f t
  have hflip_invol : ∀ f : α → Bool, flip (flip f) = f := by
    intro f; ext t; simp only [flip]; split_ifs <;> simp
  have hflip_seen : ∀ (f : α → Bool) (i : Fin m), flip f (xs i) = f (xs i) := by
    intro f i; simp only [flip]
    have : xs i ∈ seen := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    simp [this]
  have hflip_output : ∀ f : α → Bool, output (flip f) = output f :=
    fun f => houtput (flip f) f (hflip_seen f)
  have hpair_bound : ∀ f : α → Bool,
      ¬((Finset.univ.filter fun t => f t ≠ output f t).card * 4 ≤ d ∧
        (Finset.univ.filter fun t => flip f t ≠ output (flip f) t).card * 4 ≤ d) := by
    intro f ⟨hgf, hgflip⟩
    rw [hflip_output] at hgflip
    have hunseen_le : (Finset.univ \ seen).card ≤
        (Finset.univ.filter fun t => f t ≠ output f t).card +
        (Finset.univ.filter fun t => flip f t ≠ output f t).card :=
      (Finset.card_le_card (fun t ht => by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ht
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hft : f t ≠ output f t
        · exact Or.inl hft
        · push Not at hft
          exact Or.inr (show (if t ∈ seen then f t else !f t) ≠ output f t by
            simp only [ht, ↓reduceIte]; rw [← hft]; exact Bool.not_ne_self (f t)))).trans
        (Finset.card_union_le _ _)
    have hseen_le : seen.card ≤ m := le_trans Finset.card_image_le (by simp)
    have hinter_le : (Finset.univ ∩ seen).card ≤ m :=
      le_trans (Finset.card_le_card Finset.inter_subset_right) hseen_le
    have hsdiff := Finset.card_sdiff_add_card_inter Finset.univ seen
    rw [Finset.card_univ] at hsdiff
    omega
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
    exact hpair_bound g' ⟨hg'S, by rwa [hg'eq]⟩
  have hflip_card : flipS.card = S.card :=
    Finset.card_image_of_injective _ (fun a b hab => by
      have := congr_arg flip hab; rwa [hflip_invol, hflip_invol] at this)
  linarith [show S.card + flipS.card ≤ Fintype.card (α → Bool) from
    (Finset.card_union_of_disjoint hdisjoint ▸ Finset.card_le_univ _)]

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
  have hrealize : ∀ f : ↥T → Bool, ∃ c ∈ C, ∀ t : ↥T, c (↑t) = f t := hT
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
  by_contra h_all_bad
  push Not at h_all_bad
  have h_all_large : ∀ f : ↥T → Bool,
      Fintype.card (Fin m → ↥T) <
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
          ≤ d).card := by
    intro f
    have hcf := (hrealize f).choose_spec.2
    have hlt := h_all_bad f (hrealize f).choose (hrealize f).choose_spec.1 hcf
    suffices heq : (Finset.univ.filter fun xs : Fin m → ↥T =>
        (Finset.univ.filter fun t : ↥T =>
          (hrealize f).choose ((↑t : X)) ≠
            L.learn (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) (↑t)).card * 4
        ≤ d).card =
      (Finset.univ.filter fun xs : Fin m → ↥T =>
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
        ≤ d).card by rw [← heq]
                     exact hlt
    congr 1; apply Finset.filter_congr; intro xs _
    have hinner : (Finset.univ.filter fun t : ↥T =>
          (hrealize f).choose ((↑t : X)) ≠
            L.learn (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) (↑t)) =
        (Finset.univ.filter fun t : ↥T =>
          f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)) :=
      Finset.filter_congr (fun t _ => by
        rw [hcf t, show (fun i => ((↑(xs i) : X), (hrealize f).choose (↑(xs i)))) =
          (fun i => ((↑(xs i) : X), f (xs i))) from funext (fun i => by rw [hcf])])
    rw [hinner]
  set gc : (↥T → Bool) → ℕ := fun f =>
    (Finset.univ.filter fun xs : Fin m → ↥T =>
      (Finset.univ.filter fun t : ↥T =>
        f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4
      ≤ d).card
  have hsum_large : Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T) <
      ∑ f : ↥T → Bool, 2 * gc f :=
    calc Fintype.card (↥T → Bool) * Fintype.card (Fin m → ↥T)
        = ∑ _f : ↥T → Bool, Fintype.card (Fin m → ↥T) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ < ∑ f : ↥T → Bool, 2 * gc f :=
          Finset.sum_lt_sum (fun f _ => le_of_lt (h_all_large f))
            ⟨fun _ => false, Finset.mem_univ _, h_all_large _⟩
  let P : (↥T → Bool) → (Fin m → ↥T) → Prop := fun f xs =>
    (Finset.univ.filter fun t : ↥T =>
      f t ≠ (L.learn (fun i => ((↑(xs i) : X), f (xs i)))) (↑t)).card * 4 ≤ d
  have hsum_bounded : ∑ f : ↥T → Bool, 2 * gc f ≤
      Fintype.card (Fin m → ↥T) * Fintype.card (↥T → Bool) := by
    rw [show ∑ f : ↥T → Bool, 2 * gc f = 2 * ∑ f : ↥T → Bool, gc f from by
      rw [Finset.mul_sum]]
    have hswap : ∑ f : ↥T → Bool, gc f =
        ∑ xs : Fin m → ↥T, (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
      simp_rw [show ∀ f, gc f = (Finset.univ.filter fun xs => P f xs).card from fun _ => rfl,
        Finset.card_eq_sum_ones]
      rw [show ∑ f ∈ Finset.univ,
          ∑ _x ∈ Finset.univ.filter (fun xs : Fin m → ↥T => P f xs), 1 =
          ∑ f ∈ Finset.univ, ∑ xs ∈ Finset.univ, if P f xs then 1 else 0 from by
          congr 1; ext f; rw [Finset.sum_filter],
        show ∑ xs ∈ Finset.univ,
          ∑ _x ∈ Finset.univ.filter (fun f : ↥T → Bool => P f xs), 1 =
          ∑ xs ∈ Finset.univ, ∑ f ∈ Finset.univ, if P f xs then 1 else 0 from by
          congr 1; ext xs; rw [Finset.sum_filter]]
      exact Finset.sum_comm
    rw [hswap]
    calc 2 * ∑ xs : Fin m → ↥T,
          (Finset.univ.filter fun f : ↥T → Bool => P f xs).card
        = ∑ xs : Fin m → ↥T,
          2 * (Finset.univ.filter fun f : ↥T → Bool => P f xs).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _xs : Fin m → ↥T, Fintype.card (↥T → Bool) :=
          Finset.sum_le_sum (fun xs _ => hper_xs xs)
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
    (hne : Nonempty X) : MeasureTheory.Measure X :=
  let _nonemptyWitness := hne
  (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count

/-- The uniform measure is a probability measure when X is nonempty and finite. -/
theorem uniformMeasure_isProbability (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hne : Nonempty X) (hpos : 0 < Fintype.card X) :
    MeasureTheory.IsProbabilityMeasure (uniformMeasure X hne) := by
  constructor
  unfold uniformMeasure
  change (1 / (Fintype.card X : ENNReal)) • MeasureTheory.Measure.count (Set.univ : Set X) = 1
  rw [MeasureTheory.Measure.count_apply_finite' Set.finite_univ MeasurableSet.univ,
      Set.Finite.toFinset_eq_toFinset, Set.toFinset_univ, Finset.card_univ, smul_eq_mul]
  exact ENNReal.div_mul_cancel (by simp [Nat.pos_iff_ne_zero.mp hpos])
    (ENNReal.natCast_ne_top _)

/-- NFL core: for any learner and any finite domain, there exists a hard
    distribution and concept. Factors through uniformMeasure construction.
    This is the core argument used by both nfl_fixed_sample and pac_lower_bound. -/
theorem nfl_core (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 := by
  have hpos : 0 < Fintype.card X := by omega
  have hne : Nonempty X := Fintype.card_pos_iff.mp hpos
  let D := uniformMeasure X hne
  have hprob : MeasureTheory.IsProbabilityMeasure D :=
    uniformMeasure_isProbability X hne hpos
  refine ⟨D, hprob, ?_⟩
  classical
  let xs₀ : Fin m → X := fun _ => hne.some
  have per_sample : ∀ (xs : Fin m → X), ∃ (c : X → Bool),
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
        > ENNReal.ofReal (1 / 8) := by
    intro xs
    let h0 := L.learn (m := m) (fun i => (xs i, false))
    let c1 : X -> Bool := fun x => if x ∈ Set.range xs then false else !h0 x
    have hc1_train : (fun i => (xs i, c1 (xs i))) = fun i => (xs i, false) := by
      funext i; simp only [c1, Set.mem_range_self, ↓reduceIte]
    refine ⟨c1, ?_⟩
    rw [hc1_train]
    have herr_sup : (Set.range xs)ᶜ ⊆ {x : X | h0 x ≠ c1 x} := by
      intro x hx; simp only [Set.mem_compl_iff] at hx
      simp only [Set.mem_setOf_eq, c1, if_neg hx]; cases h0 x <;> simp
    apply lt_of_lt_of_le _ (MeasureTheory.measure_mono herr_sup)
    have hfin := Set.finite_range xs
    rw [show D (Set.range xs)ᶜ =
        1 - D (Set.range xs) from MeasureTheory.prob_compl_eq_one_sub hfin.measurableSet]
    have hD_seen_le : D (Set.range xs) ≤ 1 / 2 := by
      change uniformMeasure X hne _ ≤ _
      unfold uniformMeasure
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul,
          MeasureTheory.Measure.count_apply_finite' hfin hfin.measurableSet]
      have hrc : hfin.toFinset.card ≤ m :=
        (Finset.card_le_card (fun x hx => by
          simpa only [Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_univ,
            true_and] using hx)).trans
          (Finset.card_image_le.trans (Fintype.card_fin m).le)
      have hn0 : (Fintype.card X : ENNReal) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
      calc (1 / (↑(Fintype.card X) : ENNReal)) * ↑hfin.toFinset.card
          ≤ (1 / ↑(Fintype.card X)) * (↑m : ENNReal) :=
            mul_le_mul_right (Nat.cast_le.mpr hrc) _
        _ ≤ 1 / 2 := by
            rw [one_div, one_div,
                ENNReal.inv_mul_le_iff hn0 (ENNReal.natCast_ne_top _)]
            rw [show (↑(Fintype.card X) : ENNReal) * (2 : ENNReal)⁻¹ =
                (↑(Fintype.card X) : ENNReal) / 2 from div_eq_mul_inv _ _ |>.symm,
                ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero)
                  (Or.inl ENNReal.ofNat_ne_top)]
            calc (↑m : ENNReal) * 2 = ↑(2 * m) := by push_cast; ring
              _ ≤ ↑(Fintype.card X) := Nat.cast_le.mpr hm
    calc ENNReal.ofReal (1 / 8)
        < 1 / 2 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
            simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
            norm_num
      _ ≤ 1 - D (Set.range xs) := by
            calc (1 : ENNReal) / 2 = 1 - 1 / 2 := by norm_num
              _ ≤ 1 - D (Set.range xs) := tsub_le_tsub_left hD_seen_le 1
  obtain ⟨c₀, hc₀⟩ := per_sample xs₀
  refine ⟨c₀, ?_⟩
  calc (0 : ENNReal)
      < MeasureTheory.Measure.pi (fun _ : Fin m => D) {xs₀} := by
        have : ∀ i : Fin m, MeasureTheory.SigmaFinite ((fun _ => D) i) :=
          fun _ => @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ D inferInstance
        rw [MeasureTheory.Measure.pi_singleton]
        apply pos_iff_ne_zero.mpr
        rw [Finset.prod_ne_zero_iff]
        intro i _
        change (uniformMeasure X hne) {xs₀ i} ≠ 0
        simp only [uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
        apply mul_ne_zero
        · exact ne_of_gt (ENNReal.div_pos one_ne_zero (ENNReal.natCast_ne_top _))
        · rw [MeasureTheory.Measure.count_apply_finite'
              (Set.toFinite _) (measurableSet_singleton _)]
          simp
    _ ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs | D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            > ENNReal.ofReal (1 / 8) } :=
          MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hc₀)

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
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ,
      Set.preimage_univ, hD_sub_prob.measure_univ]
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
    have h14 : ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
      norm_num
    constructor
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt, h14, mul_comm] at hle
      have h4 : (k : ENNReal) * 4 ≤ (T.card : ENNReal) :=
        calc (k : ENNReal) * 4
            ≤ (T.card : ENNReal) * (4 : ENNReal)⁻¹ * 4 := mul_le_mul_left hle 4
          _ = (T.card : ENNReal) := by
              rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      exact_mod_cast h4
    · intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt, h14, mul_comm]
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
    have h12 : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num
    calc (count_finset.card : ENNReal)
        = (count_finset.card : ENNReal) * 1 := (mul_one _).symm
      _ = (count_finset.card : ENNReal) * (2 * (2 : ENNReal)⁻¹) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ = (2 * count_finset.card : ENNReal) * (2 : ENNReal)⁻¹ := by ring
      _ ≤ (T.card : ENNReal) ^ m * (2 : ENNReal)⁻¹ := mul_le_mul_left h_ennreal _
      _ = ENNReal.ofReal (1 / 2 : ℝ) * (T.card : ENNReal) ^ m := by rw [h12]
                                                                    ring
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D) good_X
      ≤ MeasureTheory.Measure.pi (fun _ : Fin m => D) good_quarter :=
        MeasureTheory.measure_mono hgood_sub
    _ = @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
          (fun _ => D_sub) (↑count_finset) := hgoal_eq
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := hpi_sub_bound
private lemma vcdim_eq_imp_shattered_card {X : Type u} (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (hd_pos : 1 ≤ d) :
    ∃ T : Finset X, Shatters X C T ∧ T.card = d := by
  have hVCDim_eq : ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) = ↑d := hd
  have hle : ∀ S, Shatters X C S → S.card ≤ d := fun S hS =>
    WithTop.coe_le_coe.mp (le_trans (le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
      (S.card : WithTop ℕ)) S hS) hVCDim_eq.le)
  by_contra h_none
  push Not at h_none
  have hstrict : ∀ S, Shatters X C S → S.card ≤ d - 1 := by
    intro S hS
    have := hle S hS
    have := h_none S hS
    omega
  have hbound : VCDim X C ≤ ↑(d - 1) := iSup₂_le fun S hS =>
    WithTop.coe_le_coe.mpr (hstrict S hS)
  rw [hd] at hbound
  have : d ≤ d - 1 := WithTop.coe_le_coe.mp hbound
  omega

/-- PAC lower bound core: sample complexity is at least (d-1)/2.
    For any PAC learner with VCDim = d, at least ⌈(d-1)/2⌉ samples needed.
    Proof: construct d shattered points, uniform distribution, counting argument.
    Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean. -/
theorem pac_lower_bound_core (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : VCDim X C = d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
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
  intro L mf hpac
  by_contra h_lt
  push Not at h_lt
  set m := mf ε (1 / 7)
  have ⟨T, hTshat, hTcard⟩ := vcdim_eq_imp_shattered_card C d hd hd_pos
  have hpac17 := hpac (1 / 7 : ℝ) (by norm_num : (0:ℝ) < 1 / 7) (by norm_num : (1:ℝ)/7 ≤ 1)
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
  have h2m_lt_d : 2 * m < T.card := by
    rw [hTcard]
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
    _ < ENNReal.ofReal (1 - 1 / 7 : ℝ) :=
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)

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
  have h_recon := congr_arg cs.reconstruct hfg
  funext i
  have hf_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, f i)) i).1 = ((fun i => (pts i, f i)) i).2 :=
    let ⟨c, hcC, hc⟩ := hf_real
    ⟨c, hcC, fun i => by simp [hc i]⟩
  have hg_real' : ∃ c ∈ C, ∀ i : Fin n,
      c ((fun i => (pts i, g i)) i).1 = ((fun i => (pts i, g i)) i).2 :=
    let ⟨c, hcC, hc⟩ := hg_real
    ⟨c, hcC, fun i => by simp [hc i]⟩
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
  classical
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  exact ⟨c, hcC, fun ⟨x, hx⟩ => by
    have := hcg ⟨x, hST hx⟩
    simp only [g, hx, dite_true] at this
    exact this⟩

/-- Exponential beats polynomial at n = 2(k+1)²: (k+1) * (4(k+1)²)^k < 2^(2(k+1)²).
    Core combinatorial inequality for the compression → finite VCDim proof.
    Proof chain: (k+1)^(2k+1) * 2^(2k) ≤ 2^(2k²+3k) < 2^(2k²+4k+2). -/
private lemma exp_beats_poly_at (k : ℕ) :
    (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k < 2 ^ (2 * (k + 1) * (k + 1)) := by
  have h1 : k + 1 ≤ 2 ^ k := succ_le_two_pow k
  rw [show 2 * (2 * (k + 1) * (k + 1)) = 4 * (k + 1) ^ 2 from by ring]
  have hpow : (4 * (k + 1) ^ 2) ^ k = 2 ^ (2 * k) * (k + 1) ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow, show (k + 1) * (2 ^ (2 * k) * (k + 1) ^ (2 * k)) =
    2 ^ (2 * k) * (k + 1) ^ (2 * k + 1) from by ring,
    show 2 * (k + 1) * (k + 1) = 2 * (k + 1) ^ 2 from by ring]
  have h2 : (k + 1) ^ (2 * k + 1) ≤ (2 ^ k) ^ (2 * k + 1) := Nat.pow_le_pow_left h1 _
  rw [← pow_mul] at h2
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
  by_contra h_top
  push Not at h_top
  rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n
    by_contra h_neg
    push Not at h_neg
    have : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro S hS
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  set N := 2 * (k + 1) * (k + 1) with hN_def
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  haveI : DecidableEq X := Classical.decEq X
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  have hT_shatt : Shatters X C T := shatters_subset hT_sub hT₀_shatt
  set n := T.card with hn_def
  have hn_eq : n = N := hT_card
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  have hpts_inj : Function.Injective pts :=
    fun _ _ h => eqv.injective (Subtype.val_injective h)
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    refine ⟨c, hcC, fun i => ?_⟩
    have := hcf' (eqv i)
    simp only [f', pts] at this ⊢
    rw [show T.equivFin (eqv i) = i from T.equivFin.apply_symm_apply i] at this
    exact this
  have h_inj : Function.Injective (cs.compress ∘ mkSample) :=
    fun f g hfg => compress_injective_on_labelings cs pts hpts_inj f g
      (h_realizable f) (h_realizable g) hfg
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := A.powerset.filter (fun S => S.card ≤ k) with htarget_def
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
  have h_source_card : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp [Fintype.card_fin, Fintype.card_bool]
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
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (k + 1) * (k + 1) := hn_eq.trans hN_def
    calc target.card ≤ (k + 1) * (2 * n) ^ k := h_target_le
      _ = (k + 1) * (2 * (2 * (k + 1) * (k + 1))) ^ k := by rw [hn_val]
      _ < 2 ^ (2 * (k + 1) * (k + 1)) := exp_beats_poly_at k
      _ = 2 ^ n := by rw [hn_val]
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (h_source_card ▸ h_target_lt) (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))


/-- Growth function polynomially bounded → VCDim < ⊤.
    Reverse direction: if GrowthFunction m ≤ ∑_{i≤d} C(m,i) for all m ≥ d,
    then VCDim ≤ d (otherwise GrowthFunction = 2^m for m = VCDim > d). -/
theorem growth_bounded_imp_vcdim_finite (X : Type u)
    (C : ConceptClass X Bool)
    (hgrowth : ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :
    VCDim X C < ⊤ := by
  by_contra h
  push Not at h
  have hinf : VCDim X C = ⊤ := le_antisymm le_top h
  obtain ⟨d, hd⟩ := hgrowth
  have hvcdim_unbounded := (iSup₂_eq_top
    (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    (by rw [VCDim] at hinf; exact hinf)
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded d (WithTop.coe_lt_top d)
  have hTcard' : d + 1 ≤ T.card := by exact_mod_cast WithTop.coe_lt_coe.mp hTcard
  have hd_app := hd T.card (le_trans (Nat.le_succ d) hTcard')
  have hgrowth_large : 2 ^ T.card ≤ GrowthFunction X C T.card := by
    unfold GrowthFunction
    apply le_csSup
    · use 2 ^ T.card
      rintro n ⟨⟨S, hScard⟩, rfl⟩
      calc Set.ncard { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
          ≤ Nat.card Bool ^ Nat.card ↥S := by
            calc _ ≤ Set.ncard (Set.univ : Set (↥S → Bool)) :=
                Set.ncard_le_ncard (Set.subset_univ _)
              _ = Nat.card (↥S → Bool) := Set.ncard_univ _
              _ = _ := Nat.card_fun
        _ = 2 ^ T.card := by
            rw [Nat.card_eq_fintype_card, Fintype.card_bool,
                Nat.card_eq_fintype_card, Fintype.card_coe, hScard]
    · refine ⟨⟨T, rfl⟩, ?_⟩
      change Set.ncard { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } = 2 ^ T.card
      rw [show { f : ↥T → Bool | ∃ c ∈ C, ∀ x : ↥T, c ↑x = f x } =
          (Set.univ : Set (↥T → Bool)) from by
          ext f; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hTshat f,
          Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card,
          Fintype.card_bool, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hsum_lt_pow : ∑ i ∈ Finset.range (d + 1), Nat.choose T.card i < 2 ^ T.card := by
    rw [← Nat.sum_range_choose T.card]
    exact Finset.sum_lt_sum_of_subset (i := T.card)
      (Finset.range_mono (by omega))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))
      (fun h => absurd (Finset.mem_range.mp h) (by omega))
      (by rw [Nat.choose_self]; exact Nat.one_pos)
      (fun j _ _ => Nat.zero_le _)
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
  by_contra h_lt
  push Not at h_lt
  obtain ⟨T, hTshat, hTcard⟩ := vcdim_eq_imp_shattered_card C d hd hd_pos
  obtain ⟨L, hL⟩ := hm
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hTcard; omega
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
  have h2m_lt_d : 2 * m < T.card := by
    rw [hTcard]
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
    _ < ENNReal.ofReal (1 - δ) :=
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by linarith)

end NFLInfrastructure
