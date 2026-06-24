/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Criterion.PAC
import LeanPool.FormalLearningTheory.Criterion.Extended
import LeanPool.FormalLearningTheory.Complexity.VCDimension
import LeanPool.FormalLearningTheory.Complexity.Ordinal
import LeanPool.FormalLearningTheory.Theorem.Online
import LeanPool.FormalLearningTheory.Theorem.Separation
import LeanPool.FormalLearningTheory.Complexity.Structures
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Learner.Active
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Extended Theorems

Advice reduction, meta-learning lower-bound infrastructure, and separation
results for compression and SQ dimension.
-/

universe u v

/-! ## Multi-Task Meta-Learning Infrastructure -/

/-- A task environment: a finite collection of concept classes (tasks)
    that a meta-learner is trained on. Each task is a concept class
    over the same domain X.

    This is the formalization of Baxter (2000)'s "learning environment."
    In the full theory, tasks are drawn i.i.d. from a distribution over
    concept classes; here we use a finite deterministic collection as the
    base case. -/
structure TaskEnvironment (X : Type u) where
  /-- Number of training tasks -/
  numTasks : ℕ
  /-- The concept classes for each task -/
  tasks : Fin numTasks → ConceptClass X Bool

/-- A meta-learner with PAC guarantees: given a task environment (training tasks),
    produces a BatchLearner and sample complexity function for new tasks.

    Compared to MetaLearner (in Active.lean), this structure:
    - takes a TaskEnvironment (multiple training tasks) rather than a single ConceptClass
    - exposes the sample complexity function (not just the learner)
    - is designed for quantitative PAC bounds, not just learnability

    The key question: does seeing n training tasks reduce the per-task
    sample complexity on new tasks? Baxter (2000) shows the answer is yes
    under task similarity, but the NFL lower bound still applies per-task. -/
structure MetaLearnerPAC (X : Type u) [MeasurableSpace X] where
  /-- Given training tasks, produce a learner for new tasks -/
  learn : TaskEnvironment X → BatchLearner X Bool
  /-- Given training tasks, produce a sample complexity function -/
  sampleComplexity : TaskEnvironment X → ℝ → ℝ → ℕ

/-- A task sample environment: n training tasks, each with m samples.
    The meta-learner observes labeled samples from each task and must
    produce a learner for a new (unseen) task.

    This extends TaskEnvironment by specifying sample sizes and
    the actual samples drawn. The meta-learner's output may depend
    on the samples but not on the true concepts. -/
structure TaskSampleEnvironment (X : Type u) [MeasurableSpace X] where
  /-- Number of training tasks -/
  numTasks : ℕ
  /-- Samples per task -/
  samplesPerTask : ℕ
  /-- The concept classes (one per task) -/
  taskClasses : Fin numTasks → ConceptClass X Bool
  /-- The true concepts (one per task, each in its class) -/
  trueConcepts : (j : Fin numTasks) → Concept X Bool
  /-- Each true concept is in its class -/
  concept_mem : ∀ j, trueConcepts j ∈ taskClasses j

/-- A sample-based meta-learner: sees labeled samples from n training tasks,
    produces a BatchLearner for new tasks.
    Unlike MetaLearnerPAC (which takes a TaskEnvironment directly),
    this meta-learner only sees the data, not the concept classes. -/
structure SampleMetaLearner (X : Type u) [MeasurableSpace X] where
  /-- Given n × m labeled samples, produce a learner -/
  learn : {n m : ℕ} → (Fin n → Fin m → X × Bool) → BatchLearner X Bool
  /-- Given n × m, produce sample complexity for the new task -/
  sampleComplexity : ℕ → ℕ → ℝ → ℝ → ℕ

/-! ## Advice Elimination Infrastructure -/

/-- Joint measurability of a sample-dependent advice learner's evaluation map. -/
def AdviceEvalMeasurable
    {X : Type u} [MeasurableSpace X] {A : Type*}
    (LA : LearnerWithAdvice X Bool A) : Prop :=
  ∀ (a : A) (m : ℕ),
    Measurable (fun p : (Fin m → X × Bool) × X => LA.learnWithAdvice a p.1 p.2)

/-- PAC learnability with finite advice, plus measurability for holdout validation. -/
def PACLearnableWithAdviceRegular
    (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) [Fintype A] [nonemptyA : Nonempty A] : Prop :=
  Fintype.card A = Fintype.card A ∧ Classical.choice nonemptyA = Classical.choice nonemptyA ∧
  ∃ (LA : LearnerWithAdvice X Bool A) (mf_adv : ℝ → ℝ → ℕ),
    AdviceEvalMeasurable LA ∧
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∃ a : A,
          MeasureTheory.Measure.pi (fun _ : Fin (mf_adv ε δ) => D)
            {xs : Fin (mf_adv ε δ) → X |
              TrueError X (LA.learnWithAdvice a (fun i => (xs i, c (xs i)))) c D
                ≤ ENNReal.ofReal ε}
          ≥ ENNReal.ofReal (1 - δ)

/-- First m₁ coordinates of a sample of size m₁ + m₂. -/
def adviceTrainSample {X : Type u} {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Fin m₁ → X × Bool :=
  fun i => S ⟨i.1, Nat.lt_add_right m₂ i.2⟩

/-- Next m₂ coordinates of a sample of size m₁ + m₂. -/
def adviceValSample {X : Type u} {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Fin m₂ → X × Bool :=
  fun j => S ⟨m₁ + j.1, Nat.add_lt_add_left j.2 m₁⟩

/-- Choose the advice value with minimum validation empirical error. -/
noncomputable def bestAdvice {X : Type u}
    {A : Type*} [Fintype A] [Nonempty A]
    (cand : A → Concept X Bool) {m : ℕ} (Sval : Fin m → X × Bool) : A :=
  Classical.choose <|
    Finset.exists_min_image Finset.univ
      (fun a => EmpiricalError X Bool (cand a) Sval (zeroOneLoss Bool))
      Finset.univ_nonempty

/-- The advice-elimination learner applied to a labeled sample. -/
noncomputable def adviceSelectedHypothesis {X : Type u}
    {A : Type*} [Fintype A] [Nonempty A]
    (LA : LearnerWithAdvice X Bool A) {m₁ m₂ : ℕ}
    (S : Fin (m₁ + m₂) → X × Bool) : Concept X Bool :=
  let cand := fun a => LA.learnWithAdvice a (adviceTrainSample S)
  cand (bestAdvice cand (adviceValSample S))

private lemma learnWithAdvice_measurable_fixed {X : Type u} [MeasurableSpace X]
    {A : Type*} (LA : LearnerWithAdvice X Bool A)
    (h_eval : AdviceEvalMeasurable LA) (a : A) {m : ℕ}
    (S : Fin m → X × Bool) :
    Measurable (LA.learnWithAdvice a S) := by
  exact (h_eval a m).comp (Measurable.prodMk measurable_const measurable_id)

private lemma trueErrorReal_le_of_bestAdvice {X : Type u} [MeasurableSpace X]
    {A : Type*} [Fintype A] [Nonempty A]
    (cand : A → Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) {m : ℕ} (Sval : Fin m → X × Bool)
    (η τ : ℝ) (_hη : 0 ≤ η)
    (hclose : ∀ a : A,
      |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) Sval (zeroOneLoss Bool)| ≤ η)
    (aStar : A) (hstar : TrueErrorReal X (cand aStar) c D ≤ τ) :
    TrueErrorReal X (cand (bestAdvice cand Sval)) c D ≤ τ + 2 * η := by
  set best := bestAdvice cand Sval
  have hmin := Classical.choose_spec
    (Finset.exists_min_image Finset.univ
      (fun a => EmpiricalError X Bool (cand a) Sval (zeroOneLoss Bool))
      Finset.univ_nonempty)
  have hmin_le : EmpiricalError X Bool (cand best) Sval (zeroOneLoss Bool) ≤
      EmpiricalError X Bool (cand aStar) Sval (zeroOneLoss Bool) :=
    hmin.2 aStar (Finset.mem_univ _)
  have h_best_close := hclose best
  have h_star_close := hclose aStar
  rw [abs_le] at h_best_close h_star_close
  linarith

private lemma finite_validation_family_bound {X : Type u} [MeasurableSpace X]
    {A : Type*} [Fintype A]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (cand : A → Concept X Bool) (h_cand_meas : ∀ a : A, Measurable (cand a))
    (m : ℕ) (hm : 0 < m) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ a : A,
        |TrueErrorReal X (cand a) c D -
          EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool)| ≥ η}
    ≤ ENNReal.ofReal ((Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m * η ^ 2)) := by
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
  -- Step 1: Contain the existential set in the union over A
  have h_sub : {xs : Fin m → X | ∃ a : A,
      |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η} ⊆ ⋃ a : A, {xs | |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η} := by
    intro xs ⟨a, ha⟩; exact Set.mem_iUnion.mpr ⟨a, ha⟩
  -- Step 2: Per-advice bound via Hoeffding (lower + upper tail)
  have h_per_advice : ∀ a : A, μ {xs : Fin m → X |
      |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ↑m * η ^ 2)) := by
    intro a
    have hmeas : MeasurableSet {x : X | cand a x ≠ c x} :=
      (measurableSet_eq_fun (h_cand_meas a) hc_meas).compl
    -- |gap| ≥ η means EmpErr ≤ TrueErr - η OR EmpErr ≥ TrueErr + η
    set LowerTail := {xs : Fin m → X | EmpiricalError X Bool (cand a)
      (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≤
        TrueErrorReal X (cand a) c D - η}
    set UpperTail := {xs : Fin m → X | EmpiricalError X Bool (cand a)
      (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥
        TrueErrorReal X (cand a) c D + η}
    have h_split : {xs : Fin m → X | |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η} ⊆ LowerTail ∪ UpperTail := by
      intro xs hxs
      simp only [Set.mem_setOf_eq] at hxs
      by_cases h : EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool) ≤ TrueErrorReal X (cand a) c D - η
      · exact Or.inl h
      · right
        simp only [UpperTail, Set.mem_setOf_eq]
        push Not at h
        -- h: EmpErr > TrueErr - η, so TrueErr - EmpErr < η
        -- hxs: |TrueErr - EmpErr| ≥ η
        -- If TrueErr - EmpErr ≥ 0, then |TrueErr - EmpErr| = TrueErr - EmpErr < η,
        -- contradicting hxs. So TrueErr - EmpErr < 0.
        set diff := TrueErrorReal X (cand a) c D -
          EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool)
        change |diff| ≥ η at hxs
        have h_diff_lt : diff < η := by simp only [diff]; linarith
        have h_neg : diff < 0 := by
          by_contra h_nn
          push Not at h_nn
          have h_eq := abs_of_nonneg h_nn
          rw [h_eq] at hxs
          linarith
        rw [abs_of_neg h_neg] at hxs
        simp only [diff] at hxs; linarith
    -- Each tail bounded by exp(-2mη²) via Hoeffding
    have h_lower := hoeffding_one_sided D (cand a) c m hm η hη hη1 hmeas
    have h_upper := hoeffding_one_sided_upper D (cand a) c m hm η hη hη1 hmeas
    calc μ {xs | |TrueErrorReal X (cand a) c D -
          EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool)| ≥ η}
        ≤ μ (LowerTail ∪ UpperTail) := μ.mono h_split
      _ ≤ μ LowerTail + μ UpperTail := MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * η ^ 2)) +
          ENNReal.ofReal (Real.exp (-2 * ↑m * η ^ 2)) := add_le_add h_lower h_upper
      _ = ENNReal.ofReal (2 * Real.exp (-2 * ↑m * η ^ 2)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← two_mul]
  -- Step 3: Union bound over A
  calc μ {xs | ∃ a : A, |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η}
      ≤ μ (⋃ a : A, {xs | |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η}) := μ.mono h_sub
    _ ≤ ∑ a : A, μ {xs | |TrueErrorReal X (cand a) c D -
        EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
          (zeroOneLoss Bool)| ≥ η} := MeasureTheory.measure_iUnion_fintype_le μ _
    _ ≤ ∑ _a : A, ENNReal.ofReal (2 * Real.exp (-2 * ↑m * η ^ 2)) :=
        Finset.sum_le_sum (fun a _ => h_per_advice a)
    _ = ENNReal.ofReal ((Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m * η ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        ring_nf

/-- For a probability measure, μ(S) ≥ 1 - μ(Sᶜ), and hence μ(S) ≥ 1 - δ if μ(Sᶜ) ≤ δ. -/
private lemma prob_ge_one_sub_compl {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Set Ω) (δ : ENNReal)
    (h : μ Sᶜ ≤ δ) :
    μ S ≥ 1 - δ := by
  rw [ge_iff_le, tsub_le_iff_right]
  calc (1 : ENNReal)
      = μ Set.univ := (MeasureTheory.IsProbabilityMeasure.measure_univ).symm
    _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_union_le S Sᶜ
    _ ≤ μ S + δ := add_le_add_right h (μ S)

/-- Cylinder set measure on product: if an event depends only on the first coordinates
    (those satisfying predicate p), then its measure under D^ι equals D^{p}(event).
    Uses piEquivPiSubtypeProd: D^ι ≃ D^{p} × D^{¬p}, and
    (D^{p} × D^{¬p})(A × univ) = D^{p}(A) · D^{¬p}(univ) = D^{p}(A). -/
private lemma pi_cylinder_set_eq {ι : Type*} [Fintype ι]
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.SigmaFinite D]
    (p : ι → Prop) [DecidablePred p]
    (S : Set (∀ _i : {i // p i}, X))
    (_hS : MeasurableSet S) :
    MeasureTheory.Measure.pi (fun _ : ι => D)
      {xs : ι → X | (fun i : {i // p i} => xs i.1) ∈ S} =
    MeasureTheory.Measure.pi (fun _ : {i // p i} => D) S := by
  -- Use measurePreserving_piEquivPiSubtypeProd to decompose D^ι into D^{p} × D^{¬p}
  set μ := MeasureTheory.Measure.pi (fun _ : ι => D)
  set μ_p := MeasureTheory.Measure.pi (fun _ : {i // p i} => D)
  set μ_np := MeasureTheory.Measure.pi (fun _ : {i // ¬p i} => D)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p
  have h_mp := MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : ι => D) p
  -- D^ι = (D^{p} × D^{¬p}) ∘ e⁻¹
  -- {xs | proj xs ∈ S} = e⁻¹ (S ×ˢ univ)
  have h_eq : {xs : ι → X | (fun i : {i // p i} => xs i.1) ∈ S} =
      e ⁻¹' (S ×ˢ Set.univ) := by
    ext xs
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    rfl
  rw [h_eq, h_mp.measure_preimage_equiv (S ×ˢ Set.univ),
      MeasureTheory.Measure.prod_prod,
      MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]

/-- Extract the first m₁ + m₂ coordinates from a sample of size Nat.pair m₁ m₂. -/
private def usedPrefix {X : Type u} [MeasurableSpace X]
    (m₁ m₂ : ℕ) (xs : Fin (Nat.pair m₁ m₂) → X) : Fin (m₁ + m₂) → X :=
  fun i => xs (Fin.castLE (Nat.add_le_pair m₁ m₂) i)

/-- Split Fin (m₁ + m₂) → X into (Fin m₁ → X) × (Fin m₂ → X) measurably. -/
private def splitUsedEquiv {X : Type u} [MeasurableSpace X]
    (m₁ m₂ : ℕ) :
    (Fin (m₁ + m₂) → X) ≃ᵐ ((Fin m₁ → X) × (Fin m₂ → X)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin m₁ ⊕ Fin m₂ => X) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m₁ ⊕ Fin m₂ => X))

/-- Sampling Nat.pair m₁ m₂ coordinates and taking the first m₁+m₂ gives the
    same measure as sampling m₁+m₂ coordinates directly. The extra junk
    coordinates integrate out via pi_cylinder_set_eq. -/
private lemma nat_pair_sample_marginal
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.SigmaFinite D]
    (m₁ m₂ : ℕ)
    (Success : Set (Fin (m₁ + m₂) → X))
    (hSuccess : MeasurableSet Success) :
    MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D)
      ((usedPrefix (X := X) m₁ m₂) ⁻¹' Success) =
    MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D) Success := by
  -- Let N = Nat.pair m₁ m₂, n = m₁ + m₂. We have n ≤ N.
  -- Strategy: use pi_cylinder_set_eq to marginalize junk coordinates,
  -- then measurePreserving_piCongrLeft to reindex {i // i < n} → Fin n.
  let N := Nat.pair m₁ m₂
  let n := m₁ + m₂
  let p : Fin N → Prop := fun i => (i : ℕ) < n
  haveI : DecidablePred p := fun i => inferInstance
  let e₁ : Fin n ≃ {i : Fin N // p i} := Fin.castLEquiv (Nat.add_le_pair m₁ m₂)
  -- Transport Success to the subtype index space
  let SuccessSub : Set ({i : Fin N // p i} → X) :=
    (fun f : {i : Fin N // p i} → X => fun j : Fin n => f (e₁ j)) ⁻¹' Success
  -- Show usedPrefix⁻¹'(Success) = cylinder set for SuccessSub
  have h_eq : (usedPrefix (X := X) m₁ m₂) ⁻¹' Success =
      {xs : Fin N → X | (fun j : {i : Fin N // p i} => xs j.1) ∈ SuccessSub} := by
    ext xs
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SuccessSub, p, N, n]
    constructor <;> intro h <;> (convert h using 1; rfl)
  have hSuccessSub_meas : MeasurableSet SuccessSub :=
    measurableSet_preimage (measurable_pi_lambda _ (fun j => measurable_pi_apply (e₁ j))) hSuccess
  rw [h_eq, pi_cylinder_set_eq D p SuccessSub hSuccessSub_meas]
  -- Now D^{p}(SuccessSub) and need D^{Fin n}(Success) — reindex via e₁
  have h_mp : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ => X) e₁)
      (MeasureTheory.Measure.pi (fun _ : Fin n => D))
      (MeasureTheory.Measure.pi (fun _ : {i : Fin N // p i} => D)) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => D) e₁
  have h_preimage :
      (MeasurableEquiv.piCongrLeft (fun _ => X) e₁) ⁻¹' SuccessSub = Success := by
    ext f
    simp only [Set.mem_preimage, SuccessSub]
    constructor <;> intro h <;> (convert h using 1; rfl)
  rw [← h_preimage, h_mp.measure_preimage_equiv]

/-- Split D^{m₁+m₂} into D^{m₁} × D^{m₂} via splitUsedEquiv. -/
private lemma used_sample_split_measure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (m₁ m₂ : ℕ)
    (Success : Set ((Fin m₁ → X) × (Fin m₂ → X))) (_hS : MeasurableSet Success) :
    MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D)
      ((splitUsedEquiv (X := X) m₁ m₂) ⁻¹' Success) =
    ((MeasureTheory.Measure.pi (fun _ : Fin m₁ => D)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin m₂ => D))) Success := by
  -- splitUsedEquiv = piCongrLeft(finSumFinEquiv.symm).trans(sumPiEquivProdPi)
  -- Both are measure-preserving, so compose them.
  have h0 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin m₁ ⊕ Fin m₂ => X) finSumFinEquiv.symm)
      (MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D))
      (MeasureTheory.Measure.pi (fun _ : Fin m₁ ⊕ Fin m₂ => D)) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => D) finSumFinEquiv.symm
  have h1 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m₁ ⊕ Fin m₂ => X))
      (MeasureTheory.Measure.pi (fun _ : Fin m₁ ⊕ Fin m₂ => D))
      ((MeasureTheory.Measure.pi (fun _ : Fin m₁ => D)).prod
        (MeasureTheory.Measure.pi (fun _ : Fin m₂ => D))) :=
    MeasureTheory.measurePreserving_sumPiEquivProdPi (fun _ => D)
  have hmp := h0.trans h1
  -- hmp is MeasurePreserving for splitUsedEquiv
  -- splitUsedEquiv = e0.trans e1, and hmp preserves the right measures
  -- hmp.measure_preimage_equiv gives us the result
  simpa [splitUsedEquiv] using hmp.measure_preimage_equiv (s := Success)

private lemma adviceGoodTrain_measurable {X : Type u} [MeasurableSpace X]
    {A : Type*} (LA : LearnerWithAdvice X Bool A)
    (h_eval : AdviceEvalMeasurable LA) (aStar : A)
    (c : Concept X Bool) (D : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite D]
    {m₁ : ℕ} (hcm : Measurable c) (ε : ℝ) :
    MeasurableSet {xs₁ : Fin m₁ → X |
      TrueError X (LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i)))) c D
        ≤ ENNReal.ofReal (ε / 2)} := by
  have h_label : Measurable
      (fun xs₁ : Fin m₁ → X => fun i : Fin m₁ => (xs₁ i, c (xs₁ i))) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply i).prodMk (hcm.comp (measurable_pi_apply i)))
  have h_joint : Measurable (fun p : (Fin m₁ → X) × X =>
      LA.learnWithAdvice aStar (fun i => (p.1 i, c (p.1 i))) p.2) :=
    (h_eval aStar m₁).comp (h_label.comp measurable_fst |>.prodMk measurable_snd)
  have h_c_snd : Measurable (fun p : (Fin m₁ → X) × X => c p.2) :=
    hcm.comp measurable_snd
  have h_disagree : MeasurableSet {p : (Fin m₁ → X) × X |
      LA.learnWithAdvice aStar (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} :=
    (measurableSet_eq_fun h_joint h_c_snd).compl
  have h_meas_fun : Measurable (fun xs₁ : Fin m₁ → X =>
      D {x | LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i))) x ≠ c x}) :=
    measurable_measure_prodMk_left (ν := D) h_disagree
  exact h_meas_fun measurableSet_Iic

private lemma adviceBadVal_measurable {X : Type u} [MeasurableSpace X]
    {A : Type*} [Countable A] (LA : LearnerWithAdvice X Bool A)
    (h_eval : AdviceEvalMeasurable LA)
    (c : Concept X Bool) (D : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite D]
    {m₁ m₂ : ℕ} (hcm : Measurable c) (ε : ℝ) :
    MeasurableSet {p : (Fin m₁ → X) × (Fin m₂ → X) | ∃ a : A,
      |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
        EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
          (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4} := by
  suffices h : ∀ a : A, MeasurableSet {p : (Fin m₁ → X) × (Fin m₂ → X) |
      |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
        EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
          (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4} by
    rw [show {p : (Fin m₁ → X) × (Fin m₂ → X) | ∃ a : A,
        |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
          EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
            (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4} =
        ⋃ a : A, {p | |TrueErrorReal X
          (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
            EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
              (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4} from by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
    exact MeasurableSet.iUnion h
  intro a
  have h_label_a : Measurable
      (fun xs₁ : Fin m₁ → X => fun i : Fin m₁ => (xs₁ i, c (xs₁ i))) :=
    measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply i).prodMk (hcm.comp (measurable_pi_apply i)))
  have h_joint_a : Measurable (fun q : (Fin m₁ → X) × X =>
      LA.learnWithAdvice a (fun i => (q.1 i, c (q.1 i))) q.2) :=
    (h_eval a m₁).comp (h_label_a.comp measurable_fst |>.prodMk measurable_snd)
  have h_c_snd_a : Measurable (fun q : (Fin m₁ → X) × X => c q.2) :=
    hcm.comp measurable_snd
  have h_disagree_a : MeasurableSet {q : (Fin m₁ → X) × X |
      LA.learnWithAdvice a (fun i => (q.1 i, c (q.1 i))) q.2 ≠ c q.2} :=
    (measurableSet_eq_fun h_joint_a h_c_snd_a).compl
  have h_true_meas : Measurable (fun xs₁ : Fin m₁ → X =>
      (D {x | LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i))) x ≠ c x}).toReal) :=
    (measurable_measure_prodMk_left (ν := D) h_disagree_a).ennreal_toReal
  have h_trueR : Measurable (fun p : (Fin m₁ → X) × (Fin m₂ → X) =>
      TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D) := by
    change Measurable ((fun xs₁ : Fin m₁ → X => (D {x | LA.learnWithAdvice a
      (fun i => (xs₁ i, c (xs₁ i))) x ≠ c x}).toReal) ∘ Prod.fst)
    exact h_true_meas.comp measurable_fst
  have h_empR : Measurable (fun p : (Fin m₁ → X) × (Fin m₂ → X) =>
      EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
        (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)) := by
    simp only [EmpiricalError]
    split
    · exact measurable_const
    · apply Measurable.div_const
      apply Finset.measurable_sum
      intro j _
      simp only [zeroOneLoss]
      apply Measurable.ite
      · have h_eval_j : Measurable (fun p : (Fin m₁ → X) × (Fin m₂ → X) =>
            LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))) (p.2 j)) := by
          have h_pair : Measurable (fun p : (Fin m₁ → X) × (Fin m₂ → X) =>
              ((fun i => (p.1 i, c (p.1 i))), p.2 j)) :=
            (h_label_a.comp measurable_fst).prodMk
              ((measurable_pi_apply j).comp measurable_snd)
          exact (h_eval a m₁).comp h_pair
        have h_c_j : Measurable (fun p : (Fin m₁ → X) × (Fin m₂ → X) => c (p.2 j)) :=
          hcm.comp ((measurable_pi_apply j).comp measurable_snd)
        exact measurableSet_eq_fun h_eval_j h_c_j
      · exact measurable_const
      · exact measurable_const
  exact (h_trueR.sub h_empR).abs measurableSet_Ici

private theorem adviceGoodPair_subset_success {X : Type u} [MeasurableSpace X]
    {A : Type*} [Fintype A] [Nonempty A]
    (LA : LearnerWithAdvice X Bool A) (aStar : A)
    (c : Concept X Bool) (D : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure D] {m₁ m₂ : ℕ} {ε : ℝ} (hε : 0 < ε) :
    {p : (Fin m₁ → X) × (Fin m₂ → X) |
      TrueError X (LA.learnWithAdvice aStar (fun i => (p.1 i, c (p.1 i)))) c D
        ≤ ENNReal.ofReal (ε / 2) ∧
      ∀ a : A,
        |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
          EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
            (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| < ε / 4}
    ⊆
    {p : (Fin m₁ → X) × (Fin m₂ → X) |
      let train := fun i => (p.1 i, c (p.1 i))
      let val := fun j => (p.2 j, c (p.2 j))
      let cand := fun a => LA.learnWithAdvice a train
      D {x | cand (bestAdvice cand val) x ≠ c x} ≤ ENNReal.ofReal ε} := by
  intro p ⟨hgt, hbv⟩
  have hbv_le : ∀ a : A,
      |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
        EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
          (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≤ ε / 4 :=
    fun a => le_of_lt (hbv a)
  have hsel_real : TrueErrorReal X
      (LA.learnWithAdvice
        (bestAdvice (fun a => LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
          (fun j => (p.2 j, c (p.2 j))))
        (fun i => (p.1 i, c (p.1 i)))) c D ≤ ε :=
    calc TrueErrorReal X
          (LA.learnWithAdvice
            (bestAdvice (fun a => LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
              (fun j => (p.2 j, c (p.2 j))))
            (fun i => (p.1 i, c (p.1 i)))) c D
        ≤ ε / 2 + 2 * (ε / 4) :=
          trueErrorReal_le_of_bestAdvice
            (fun a => LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
            c D (fun j => (p.2 j, c (p.2 j))) (ε / 4) (ε / 2) (by linarith) hbv_le aStar (by
              unfold TrueErrorReal
              exact ENNReal.toReal_le_of_le_ofReal (by linarith) hgt)
      _ = ε := by ring
  change D {x | LA.learnWithAdvice
      (bestAdvice (fun a => LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
        (fun j => (p.2 j, c (p.2 j))))
      (fun i => (p.1 i, c (p.1 i))) x ≠ c x} ≤ ENNReal.ofReal ε
  have hne_top : D {x | LA.learnWithAdvice
      (bestAdvice (fun a => LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
        (fun j => (p.2 j, c (p.2 j))))
      (fun i => (p.1 i, c (p.1 i))) x ≠ c x} ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ _))
      (by rw [MeasureTheory.IsProbabilityMeasure.measure_univ]; exact ENNReal.one_lt_top))
  have := ENNReal.ofReal_toReal hne_top
  rw [TrueErrorReal, TrueError] at hsel_real
  rw [← this]
  exact ENNReal.ofReal_le_ofReal hsel_real

private theorem probability_compl_le_of_ge_one_sub_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {S : Set Ω} (hS_meas : MeasurableSet S) {δ : ℝ}
    (h_ge : μ S ≥ ENNReal.ofReal (1 - δ / 2)) :
    μ Sᶜ ≤ ENNReal.ofReal (δ / 2) := by
  rw [MeasureTheory.measure_compl hS_meas (MeasureTheory.measure_ne_top _ _),
    MeasureTheory.IsProbabilityMeasure.measure_univ]
  refine le_trans (tsub_le_tsub_left h_ge 1) ?_
  by_cases hδ2 : 2 ≤ δ
  · exact le_trans tsub_le_self
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  · rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - δ / 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

private lemma adviceValidationUniformBound {X : Type u} [MeasurableSpace X]
    {A : Type*} [Fintype A] [Nonempty A]
    (LA : LearnerWithAdvice X Bool A) (h_eval : AdviceEvalMeasurable LA)
    (c : Concept X Bool) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.SigmaFinite D] {m₁ m₂ : ℕ} (hcm : Measurable c)
    (hm₂_pos : 0 < m₂) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hm₂_ge : Real.log (4 * ↑(Fintype.card A) / δ) /
      (2 * (min (ε / 4) 1) ^ 2) ≤ ↑m₂) :
    ∀ xs₁ : Fin m₁ → X,
      MeasureTheory.Measure.pi (fun _ : Fin m₂ => D)
        {xs₂ : Fin m₂ → X | ∃ a : A,
          |TrueErrorReal X (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i)))) c D -
            EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i))))
              (fun i => (xs₂ i, c (xs₂ i))) (zeroOneLoss Bool)| ≥ ε / 4}
        ≤ ENNReal.ofReal (δ / 2) := by
  intro xs₁
  let μ₂ := MeasureTheory.Measure.pi (fun _ : Fin m₂ => D)
  set η := min (ε / 4) 1 with hη_def
  have hη : 0 < η := by simp [η, hε]
  have hη1 : η ≤ 1 := by simp [η]
  let cand : A → Concept X Bool := fun a =>
    LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i)))
  have h_cand_meas : ∀ a : A, Measurable (cand a) :=
    fun a => learnWithAdvice_measurable_fixed LA h_eval a _
  have hfvb := finite_validation_family_bound D c hcm cand h_cand_meas m₂ hm₂_pos η hη hη1
  have h_sub : {xs : Fin m₂ → X | ∃ a : A,
      |TrueErrorReal X (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i)))) c D -
        EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i))))
          (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε / 4} ⊆
      {xs : Fin m₂ → X | ∃ a : A,
        |TrueErrorReal X (cand a) c D -
          EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
            (zeroOneLoss Bool)| ≥ η} := by
    intro xs hxs
    simp only [Set.mem_setOf_eq, cand] at hxs ⊢
    obtain ⟨a, ha⟩ := hxs
    exact ⟨a, le_trans (min_le_left _ _) ha⟩
  calc μ₂ {xs : Fin m₂ → X | ∃ a : A,
          |TrueErrorReal X (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i)))) c D -
            EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i))))
              (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε / 4}
      ≤ μ₂ {xs : Fin m₂ → X | ∃ a : A,
          |TrueErrorReal X (cand a) c D -
            EmpiricalError X Bool (cand a) (fun i => (xs i, c (xs i)))
              (zeroOneLoss Bool)| ≥ η} :=
        μ₂.mono h_sub
    _ ≤ ENNReal.ofReal ((Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m₂ * η ^ 2)) := hfvb
    _ ≤ ENNReal.ofReal (δ / 2) := by
        apply ENNReal.ofReal_le_ofReal
        have h2η2_pos : (0 : ℝ) < 2 * η ^ 2 := by positivity
        have hA_pos : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
        set R := 4 * ↑(Fintype.card A) / δ with hR_def
        have hR_pos : (0 : ℝ) < R := div_pos (by positivity) hδ
        have hm₂_ge' : Real.log R / (2 * η ^ 2) ≤ ↑m₂ := by simpa [R, η] using hm₂_ge
        have hlog_le : Real.log R ≤ 2 * ↑m₂ * η ^ 2 := by
          have := mul_le_mul_of_nonneg_right hm₂_ge' (le_of_lt h2η2_pos)
          rw [div_mul_cancel₀ _ (ne_of_gt h2η2_pos)] at this
          linarith
        by_cases hR1 : R ≤ 1
        · have hA_le : (Fintype.card A : ℝ) * 2 ≤ δ / 2 := by
            have : R * δ = 4 * ↑(Fintype.card A) := by simp only [R]; field_simp
            nlinarith
          have hexp_le : Real.exp (-2 * ↑m₂ * η ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg η])
          calc (Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m₂ * η ^ 2)
              ≤ (Fintype.card A : ℝ) * 2 * 1 := by gcongr
            _ = (Fintype.card A : ℝ) * 2 := mul_one _
            _ ≤ δ / 2 := hA_le
        · push Not at hR1
          have hexp_bound :
              Real.exp (-2 * ↑m₂ * η ^ 2) ≤ δ / (4 * ↑(Fintype.card A)) := by
            have h1 : -(2 * ↑m₂ * η ^ 2) ≤ -Real.log R := by linarith
            have h2 : -2 * ↑m₂ * η ^ 2 = -(2 * ↑m₂ * η ^ 2) := by ring
            rw [h2]
            calc Real.exp (-(2 * ↑m₂ * η ^ 2))
                ≤ Real.exp (-Real.log R) := Real.exp_le_exp_of_le h1
              _ = R⁻¹ := by rw [Real.exp_neg, Real.exp_log hR_pos]
              _ = δ / (4 * ↑(Fintype.card A)) := by simp only [R]; rw [inv_div]
          calc (Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m₂ * η ^ 2)
              ≤ (Fintype.card A : ℝ) * 2 * (δ / (4 * ↑(Fintype.card A))) := by gcongr
            _ = δ / 2 := by field_simp; ring

private theorem adviceGoodFull_subset_goal {X : Type u} [MeasurableSpace X]
    {A : Type*} [Fintype A] [Nonempty A]
    (LA : LearnerWithAdvice X Bool A) (c : Concept X Bool)
    (D : MeasureTheory.Measure X) {m₁ m₂ : ℕ} {ε : ℝ}
    (GoodPair : Set ((Fin m₁ → X) × (Fin m₂ → X)))
    (hGP_sub_SP : GoodPair ⊆
      {p : (Fin m₁ → X) × (Fin m₂ → X) |
        let train := fun i => (p.1 i, c (p.1 i))
        let val := fun j => (p.2 j, c (p.2 j))
        let cand := fun a => LA.learnWithAdvice a train
        D {x | cand (bestAdvice cand val) x ≠ c x} ≤ ENNReal.ofReal ε}) :
    (usedPrefix (X := X) m₁ m₂) ⁻¹'
      ((splitUsedEquiv (X := X) m₁ m₂) ⁻¹' GoodPair)
    ⊆
      {xs : Fin (Nat.pair m₁ m₂) → X | D {x |
        LA.learnWithAdvice
          (bestAdvice (fun a => LA.learnWithAdvice a
            (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
              c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩))))
            (fun j : Fin m₂ => (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩,
              c (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩))))
          (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
            c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩)))
          x ≠ c x} ≤ ENNReal.ofReal ε} := by
  have h_split_fst : ∀ (ys : Fin (m₁ + m₂) → X) (i : Fin m₁),
      (splitUsedEquiv (X := X) m₁ m₂ ys).1 i = ys (Fin.castAdd m₂ i) := by
    intro ys i
    simp [splitUsedEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, finSumFinEquiv,
      Equiv.sumPiEquivProdPi, Fin.castAdd]
  have h_split_snd : ∀ (ys : Fin (m₁ + m₂) → X) (j : Fin m₂),
      (splitUsedEquiv (X := X) m₁ m₂ ys).2 j = ys (Fin.natAdd m₁ j) := by
    intro ys j
    simp [splitUsedEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, finSumFinEquiv,
      Equiv.sumPiEquivProdPi, Fin.natAdd]
  have h_composed_fst : ∀ (xs' : Fin (Nat.pair m₁ m₂) → X) (i : Fin m₁),
      (splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i =
      xs' ⟨i.1, by have := Nat.left_le_pair m₁ m₂; omega⟩ := by
    intro xs' i; rw [h_split_fst]; simp [usedPrefix, Fin.castLE, Fin.castAdd]
  have h_composed_snd : ∀ (xs' : Fin (Nat.pair m₁ m₂) → X) (j : Fin m₂),
      (splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j =
      xs' ⟨m₁ + j.1, by have := Nat.add_le_pair m₁ m₂; omega⟩ := by
    intro xs' j; rw [h_split_snd]; simp [usedPrefix, Fin.castLE, Fin.natAdd]
  have h_full_hyp : ∀ xs' : Fin (Nat.pair m₁ m₂) → X,
      LA.learnWithAdvice
        (bestAdvice
          (fun a => LA.learnWithAdvice a (fun i : Fin m₁ =>
            ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i,
             c ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i))))
          (fun j : Fin m₂ =>
            ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j,
             c ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j))))
        (fun i : Fin m₁ =>
          ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i,
           c ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i))) =
      LA.learnWithAdvice
        (bestAdvice
          (fun a => LA.learnWithAdvice a (fun i : Fin m₁ =>
            (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
             c (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩))))
          (fun j : Fin m₂ =>
            (xs' ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩,
             c (xs' ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩))))
        (fun i : Fin m₁ =>
          (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
           c (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩))) := by
    intro xs'
    have ht : ∀ i : Fin m₁,
        ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i,
         c ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i)) =
        (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
         c (xs' ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩)) := by
      intro i; simp only [h_composed_fst]
    have hv : ∀ j : Fin m₂,
        ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j,
         c ((splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j)) =
        (xs' ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩,
         c (xs' ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩)) := by
      intro j; simp only [h_composed_snd]
    simp only [funext ht, funext hv]
  intro xs hxs
  have hxGP : splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs) ∈ GoodPair := hxs
  have hxSP := hGP_sub_SP hxGP
  simp only [Set.mem_setOf_eq] at hxSP ⊢
  rw [← h_full_hyp xs]
  exact hxSP

/-- Advice elimination (Ben-David & Dichterman 1998):
    If C is PAC-learnable with concept-dependent advice from a FINITE set A
    (with measurability regularity), then C is PAC-learnable without advice.

    Proof strategy: run the advice-augmented learner with each a ∈ A on a
    training portion of the sample, producing |A| candidate hypotheses. Use a
    validation portion to select the candidate with lowest empirical error.
    Union bound over |A| advice values + Hoeffding on validation controls total
    failure probability. Sample complexity: O(m_orig(ε/2, δ/(2|A|)) + log(|A|/δ)/ε²).

    The [Fintype A] constraint is essential: for infinite A, the theorem is false
    (no finite union bound). [Nonempty A] ensures the advice space is inhabited. -/
theorem advice_elimination (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableHypotheses X C]
    (A : Type*) [Fintype A] [Nonempty A] :
    PACLearnableWithAdviceRegular X C A → PACLearnable X C := by
  have hc_meas : ∀ c ∈ C, Measurable c := MeasurableHypotheses.mem_measurable (C := C)
  intro ⟨_, _, LA, mf_adv, h_eval, h_adv⟩
  -- Construct the advice-elimination learner.
  -- The learner tries all advice values and picks the best one via validation.
  -- The hypothesis space is all of Set.univ (unrestricted).
  --
  -- For the PAC guarantee, we use the training hypothesis + validation Hoeffding
  -- + union bound. The sample is split into training (first m₁) and validation (rest).
  --
  -- PROOF STRATEGY: We show PAC learnability by:
  -- 1. Training phase: ∃ a* with TrueError(h_{a*}) ≤ ε/2 (w.h.p. from hypothesis)
  -- 2. Validation phase: |TrueErr - EmpErr| < ε/4 for all candidates (w.h.p. from Hoeffding)
  -- 3. Selection: bestAdvice picks h with minimum EmpErr, giving TrueErr ≤ ε/2 + 2·(ε/4) = ε
  -- 4. Union bound: combined probability ≥ 1 - δ
  --
  -- The formal argument requires product-measure decomposition to handle the
  -- independence of training and validation samples. This crosses the measure-theory
  -- bridge at the D^{m₁} × D^{m₂} → D^{m₁+m₂} joint.
  --
  -- We construct the learner and provide the sample complexity.
  -- The core probabilistic argument uses the proved infrastructure:
  -- finite_validation_family_bound (Hoeffding + union over A)
  -- trueErrorReal_le_of_bestAdvice (deterministic selection bound)
  refine ⟨⟨Set.univ,
    fun {m} S =>
      let m₁ := (Nat.unpair m).1
      let m₂ := (Nat.unpair m).2
      let train : Fin m₁ → X × Bool :=
        fun i => S ⟨i.1, lt_of_lt_of_le i.2 (Nat.unpair_left_le m)⟩
      let val : Fin m₂ → X × Bool :=
        fun j => S ⟨m₁ + j.1, by have := Nat.unpair_add_le m; omega⟩
      let cand := fun a => LA.learnWithAdvice a train
      cand (bestAdvice cand val),
    fun _ => Set.mem_univ _⟩, ?mf, ?pac⟩
  -- Sample complexity: encode training and validation sizes via Nat.pair
  case mf =>
    exact fun ε δ =>
      Nat.pair (mf_adv (ε / 2) (δ / 2))
        (Nat.ceil ((1 / (2 * (min (ε / 4) 1) ^ 2)) *
          Real.log (4 * ↑(Fintype.card A) / δ)) + 1)
  -- PAC guarantee
  case pac =>
    intro ε δ hε hδ D hD c hcC
    obtain ⟨aStar, haStar⟩ := h_adv (ε / 2) (δ / 2) (by linarith) (by linarith) D hD c hcC
    haveI : MeasureTheory.SigmaFinite D := inferInstance
    have hcm : Measurable c := hc_meas c hcC
    set m₁ := mf_adv (ε / 2) (δ / 2)
    set m₂ := Nat.ceil ((1 / (2 * (min (ε / 4) 1) ^ 2)) * Real.log (4 * ↑(Fintype.card A) / δ)) + 1
    -- === GoodPair architecture: measurable inner event ===
    simp_rw [Nat.unpair_pair]
    let μ₁ := MeasureTheory.Measure.pi (fun _ : Fin m₁ => D)
    let μ₂ := MeasureTheory.Measure.pi (fun _ : Fin m₂ => D)
    -- GoodTrain: the distinguished advice aStar produces a hypothesis with TrueError ≤ ε/2
    let GoodTrain : Set (Fin m₁ → X) :=
      {xs₁ | TrueError X
        (LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i)))) c D
        ≤ ENNReal.ofReal (ε / 2)}
    -- SuccessProd: the actual success event on the product space
    let SuccessProd : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
      {p | let train := fun i => (p.1 i, c (p.1 i))
           let val := fun j => (p.2 j, c (p.2 j))
           let cand := fun a => LA.learnWithAdvice a train
           D {x | cand (bestAdvice cand val) x ≠ c x} ≤ ENNReal.ofReal ε}
    -- GoodPair: training succeeds AND all candidates have accurate empirical error
    let GoodPair : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
      {p | p.1 ∈ GoodTrain ∧
           ∀ a : A,
             |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
               EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
                 (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| < ε / 4}
    -- === KU_2: GoodPair ⊆ SuccessProd (deterministic core) ===
    have hGP_sub_SP : GoodPair ⊆ SuccessProd := by
      simpa [GoodPair, GoodTrain, SuccessProd] using
        adviceGoodPair_subset_success (LA := LA) (aStar := aStar) (c := c) (D := D)
          (m₁ := m₁) (m₂ := m₂) (ε := ε) hε
    -- === KU_3 + transport + final bound ===
    have hgt_ge : μ₁ GoodTrain ≥ ENNReal.ofReal (1 - δ / 2) := haStar
    have hm₂_pos : 0 < m₂ := by simp only [m₂]; omega
    -- === GoodPair transport architecture (Steps 2a-2k) ===
    -- Step 2a: Define BadVal, GoodUsed, GoodFull
    let BadVal : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
      {p | ∃ a : A,
        |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
          EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
            (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4}
    let GoodUsed : Set (Fin (m₁ + m₂) → X) :=
      (splitUsedEquiv (X := X) m₁ m₂) ⁻¹' GoodPair
    let GoodFull : Set (Fin (Nat.pair m₁ m₂) → X) :=
      (usedPrefix (X := X) m₁ m₂) ⁻¹' GoodUsed
    -- Step 2b: GoodPair equivalence
    have hGP_eq : GoodPair = {p | p.1 ∈ GoodTrain ∧ p ∉ BadVal} := by
      ext p; simp only [GoodPair, BadVal, Set.mem_setOf_eq, not_exists, not_le]
    -- Step 2c: Measurability
    have hGoodTrain_meas : MeasurableSet GoodTrain := by
      simpa [GoodTrain] using
        adviceGoodTrain_measurable LA h_eval aStar c D (m₁ := m₁) hcm ε
    have hBadVal_meas : MeasurableSet BadVal := by
      simpa [BadVal] using
        adviceBadVal_measurable LA h_eval c D (m₁ := m₁) (m₂ := m₂) hcm ε
    have hGoodPair_meas : MeasurableSet GoodPair := by
      rw [hGP_eq]
      exact (measurableSet_preimage measurable_fst hGoodTrain_meas).inter hBadVal_meas.compl
    have hGoodUsed_meas : MeasurableSet GoodUsed :=
      measurableSet_preimage (splitUsedEquiv (X := X) m₁ m₂).measurable hGoodPair_meas
    -- Step 2d: GoodFull ⊆ goal_set
    have hGP_sub_target : GoodPair ⊆
        {p : (Fin m₁ → X) × (Fin m₂ → X) |
          let train := fun i => (p.1 i, c (p.1 i))
          let val := fun j => (p.2 j, c (p.2 j))
          let cand := fun a => LA.learnWithAdvice a train
          D {x | cand (bestAdvice cand val) x ≠ c x} ≤ ENNReal.ofReal ε} := by
      simpa [SuccessProd] using hGP_sub_SP
    have hGoodFull_sub_goal : GoodFull ⊆
        {xs : Fin (Nat.pair m₁ m₂) → X | D {x |
          LA.learnWithAdvice
            (bestAdvice (fun a => LA.learnWithAdvice a
              (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
                c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩))))
              (fun j : Fin m₂ => (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩,
                c (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩))))
            (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
              c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩)))
            x ≠ c x} ≤ ENNReal.ofReal ε} := by
      simpa [GoodFull, GoodUsed] using
        adviceGoodFull_subset_goal LA c D (m₁ := m₁) (m₂ := m₂) (ε := ε)
          GoodPair hGP_sub_target
    -- Step 2f: Training complement bound
    have htrain_compl : μ₁ GoodTrainᶜ ≤ ENNReal.ofReal (δ / 2) := by
      exact probability_compl_le_of_ge_one_sub_half μ₁ hGoodTrain_meas hgt_ge
    -- Step 2g: Validation uniform bound
    have hm₂_ge : Real.log (4 * ↑(Fintype.card A) / δ) /
        (2 * (min (ε / 4) 1) ^ 2) ≤ ↑m₂ := by
      have h1 : Real.log (4 * ↑(Fintype.card A) / δ) /
          (2 * (min (ε / 4) 1) ^ 2) =
          (1 / (2 * (min (ε / 4) 1) ^ 2)) *
            Real.log (4 * ↑(Fintype.card A) / δ) := by
        ring
      rw [h1]
      calc (1 / (2 * (min (ε / 4) 1) ^ 2)) *
            Real.log (4 * ↑(Fintype.card A) / δ)
          ≤ ↑(Nat.ceil ((1 / (2 * (min (ε / 4) 1) ^ 2)) *
              Real.log (4 * ↑(Fintype.card A) / δ))) :=
            Nat.le_ceil _
        _ ≤ ↑(Nat.ceil ((1 / (2 * (min (ε / 4) 1) ^ 2)) *
              Real.log (4 * ↑(Fintype.card A) / δ)) + 1) := by
            exact_mod_cast Nat.le_succ _
        _ = ↑m₂ := by simp [m₂]
    have hval_uniform : ∀ xs₁ : Fin m₁ → X,
        μ₂ {xs₂ | (xs₁, xs₂) ∈ BadVal} ≤ ENNReal.ofReal (δ / 2) := by
      intro xs₁
      simpa [BadVal, μ₂] using
        adviceValidationUniformBound LA h_eval c D (m₁ := m₁) (m₂ := m₂)
          hcm hm₂_pos ε δ hε hδ hm₂_ge xs₁
    -- Step 2h: Product complement bounds
    have hBadVal_prod : (μ₁.prod μ₂) BadVal ≤ ENNReal.ofReal (δ / 2) := by
      rw [MeasureTheory.Measure.prod_apply hBadVal_meas]
      have h_fiber : ∀ xs₁ : Fin m₁ → X,
          μ₂ (Prod.mk xs₁ ⁻¹' BadVal) ≤ ENNReal.ofReal (δ / 2) := by
        intro xs₁
        have : Prod.mk xs₁ ⁻¹' BadVal = {xs₂ | (xs₁, xs₂) ∈ BadVal} := by ext; simp
        rw [this]
        exact hval_uniform xs₁
      calc ∫⁻ xs₁, μ₂ (Prod.mk xs₁ ⁻¹' BadVal) ∂μ₁
          ≤ ∫⁻ _, ENNReal.ofReal (δ / 2) ∂μ₁ :=
            MeasureTheory.lintegral_mono h_fiber
        _ = ENNReal.ofReal (δ / 2) := by
            simp [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
    -- Step 2i: GoodPair probability bound
    have hGP_compl_sub : GoodPairᶜ ⊆
        {p : (Fin m₁ → X) × (Fin m₂ → X) | p.1 ∉ GoodTrain} ∪ BadVal := by
      intro p hp
      rw [hGP_eq] at hp
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hp
      exact hp.imp id (fun h => not_not.mp h)
    have hGoodPair_bound : (μ₁.prod μ₂) GoodPair ≥ ENNReal.ofReal (1 - δ) := by
      have hcompl : (μ₁.prod μ₂) GoodPairᶜ ≤ ENNReal.ofReal δ :=
        calc (μ₁.prod μ₂) GoodPairᶜ
            ≤ (μ₁.prod μ₂) ({p : (Fin m₁ → X) × (Fin m₂ → X) | p.1 ∉ GoodTrain} ∪ BadVal) :=
              (μ₁.prod μ₂).mono hGP_compl_sub
          _ ≤ (μ₁.prod μ₂) {p : (Fin m₁ → X) × (Fin m₂ → X) | p.1 ∉ GoodTrain} +
              (μ₁.prod μ₂) BadVal :=
              MeasureTheory.measure_union_le _ _
          _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
              apply add_le_add _ hBadVal_prod
              have hrect : {p : (Fin m₁ → X) × (Fin m₂ → X) | p.1 ∉ GoodTrain} =
                  GoodTrainᶜ ×ˢ Set.univ := by ext p; simp
              rw [hrect, MeasureTheory.Measure.prod_prod,
                  MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
              exact htrain_compl
          _ = ENNReal.ofReal δ := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
              congr 1; ring
      have h1 := prob_ge_one_sub_compl (μ₁.prod μ₂) GoodPair (ENNReal.ofReal δ) hcompl
      -- h1 : (μ₁.prod μ₂) GoodPair ≥ 1 - ENNReal.ofReal δ
      -- Need: ≥ ENNReal.ofReal (1 - δ)
      calc (μ₁.prod μ₂) GoodPair
          ≥ 1 - ENNReal.ofReal δ := h1
        _ = ENNReal.ofReal (1 - δ) := by
            conv_lhs => rw [← ENNReal.ofReal_one]
            exact (ENNReal.ofReal_sub 1 (le_of_lt hδ)).symm
    -- Step 2j: Transport chain
    have h_transport :
        MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull
        = (μ₁.prod μ₂) GoodPair := by
      calc MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull
          = MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D) GoodUsed :=
            nat_pair_sample_marginal D m₁ m₂ GoodUsed hGoodUsed_meas
        _ = (μ₁.prod μ₂) GoodPair :=
            used_sample_split_measure D m₁ m₂ GoodPair hGoodPair_meas
    -- Step 2k: Final bound. The learner exposes `Nat.unpair (Nat.pair m₁ m₂)`;
    -- the proof above uses `m₁` and `m₂`, so the last step transports across that cast.
    have h_gf_bound : MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull
        ≥ ENNReal.ofReal (1 - δ) := by
      rw [h_transport]; exact hGoodPair_bound
    have h_combined : MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D)
        {xs : Fin (Nat.pair m₁ m₂) → X | D {x |
          LA.learnWithAdvice
            (bestAdvice (fun a => LA.learnWithAdvice a
              (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
                c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩))))
              (fun j : Fin m₂ => (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩,
                c (xs ⟨m₁ + ↑j, by have := Nat.add_le_pair m₁ m₂; omega⟩))))
            (fun i : Fin m₁ => (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩,
              c (xs ⟨↑i, by have := Nat.left_le_pair m₁ m₂; omega⟩)))
            x ≠ c x} ≤ ENNReal.ofReal ε}
      ≥ ENNReal.ofReal (1 - δ) :=
      le_trans h_gf_bound
        ((MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D)).mono
          hGoodFull_sub_goal)
    -- Route E: bridge via convert + Fin.heq_fun_iff
    have h_fst : (Nat.unpair (Nat.pair m₁ m₂)).1 = m₁ := by simp [Nat.unpair_pair]
    have h_snd : (Nat.unpair (Nat.pair m₁ m₂)).2 = m₂ := by simp [Nat.unpair_pair]
    convert h_combined using 10
    all_goals first
    | simp only [Nat.unpair_pair]
    | (exact (Fin.heq_fun_iff h_fst).mpr (fun i => rfl))
    | (exact (Fin.heq_fun_iff h_snd).mpr (fun i => rfl))
    | (congr 1 <;> (first
        | (ext a; congr 1; exact (Fin.heq_fun_iff h_fst).mpr (fun i => rfl))
        | (exact (Fin.heq_fun_iff h_snd).mpr (fun j => rfl))))

/-- Baxter base case: any meta-learner's output is subject to the NFL lower bound.
    Even after seeing arbitrarily many training tasks, the meta-learner's output
    learner on a NEW task C_new with VCDim = d requires at least ⌈(d-1)/2⌉ samples.

    This is the n=1 (single environment) base case of Baxter (2000).
    The full Baxter bound (n environments, per-task m ≥ d/(ε²·n)) requires
    multi-environment product measure infrastructure not yet built.

    Proof: the meta-learner produces a BatchLearner L and sample complexity mf.
    If (L, mf) achieves PAC on C_new, then mf ε δ is a PAC-valid sample size,
    so pac_lower_bound_member gives ⌈(d-1)/2⌉ ≤ mf ε δ.

    The full multi-environment Baxter bound is outside this kernel; this theorem
    records the single-environment lower-bound component. -/
theorem baxter_base_case (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (ML : MetaLearnerPAC X)
    (env : TaskEnvironment X)
    (C_new : ConceptClass X Bool)
    (d : ℕ) (hd : VCDim X C_new = d) (hd_pos : 1 ≤ d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7)
    (hPAC : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C_new,
        MeasureTheory.Measure.pi
          (fun _ : Fin (ML.sampleComplexity env ε δ) => D)
          { xs : Fin (ML.sampleComplexity env ε δ) → X |
            D { x | (ML.learn env).learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ ML.sampleComplexity env ε δ := by
  exact pac_lower_bound_member X C_new d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
    (ML.sampleComplexity env ε δ) ⟨ML.learn env, hPAC⟩

/-- Baxter's multi-task lower bound: any sample-based meta-learner
    that achieves PAC on a new task C_new with VCDim = d, after seeing
    n training tasks with m samples each, requires ⌈(d-1)/2⌉ samples
    for the new task.

    This is the n-independent version. The n-dependent improvement
    m ≥ Ω(d/(ε²·n)) requires the product-measure information-theoretic
    argument.

    Key insight: the meta-learner's output (L, mf) is a PAC witness
    for C_new. By pac_lower_bound_member, any PAC witness requires
    at least ⌈(d-1)/2⌉ samples. The meta-learner's training phase
    (seeing n tasks) cannot reduce this bound because the new task's
    concept class is adversarially chosen AFTER training.

    The n-dependent improvement (Baxter 2000, Theorem 3):
    For the PRODUCT measure over n tasks × m samples per task,
    the adversary argument gives m ≥ Ω(d/(ε²·n)).
    This requires:
    - TaskDistribution: a measure over concept classes
    - Product measure: D^(n×m) decomposed as (D^m)^n
    - Information-theoretic counting: n·m bits vs 2^d labelings
    This theorem proves the n-independent base case. -/
theorem baxter_full (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (SML : SampleMetaLearner X)
    (C_new : ConceptClass X Bool)
    (d : ℕ) (hd : VCDim X C_new = d) (hd_pos : 1 ≤ d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7)
    (n m : ℕ)
    (training_data : Fin n → Fin m → X × Bool)
    (hPAC : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C_new,
        let mf := SML.sampleComplexity n m ε δ
        MeasureTheory.Measure.pi
          (fun _ : Fin mf => D)
          { xs : Fin mf → X |
            D { x | (SML.learn training_data).learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SML.sampleComplexity n m ε δ := by
  apply pac_lower_bound_member X C_new d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
  exact ⟨SML.learn training_data, hPAC⟩

/-- VC dimension does not determine SQ hardness:
    there exists a concept class with finite VC dimension but infinite SQ dimension
    under some distribution at some positive correlation threshold.
    Witness: singleton indicators on ℕ, with SQDimension = ⊤ at τ = 1.
    For any probability D on ℕ, the correlation between distinct indicators 1_i, 1_j
    is |1 - 2(D({i}) + D({j}))| ≤ 1, so every finite subset of C qualifies at τ = 1.
    Since C is infinite, SQDimension = ⊤.
    The statement quantifies the measurable domain, distribution, and threshold
    parameters used by `SQDimension`. -/
theorem vcdim_not_implies_hardness :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      VCDim X C < ⊤ ∧
      ∃ (D : MeasureTheory.Measure X) (_ : MeasureTheory.IsProbabilityMeasure D)
        (τ : ℝ), 0 < τ ∧ SQDimension X C D τ = ⊤ := by
  -- Witness: X = ℕ, C = singleton indicators {fun x => decide (x = n) | n : ℕ}.
  -- VCDim = 1: shatters any singleton {n}, cannot shatter any pair {n, m}.
  -- SQDimension = ⊤ at τ = 1 for ANY probability D:
  -- Correlation between distinct indicators = |1 - 2(D({i}) + D({j}))| ≤ 1 = τ,
  -- so every finite subfamily has pairwise |corr| ≤ 1 = τ. Since C is infinite, SQDim = ⊤.
  let C : ConceptClass ℕ Bool := { f | ∃ n : ℕ, f = fun x => decide (x = n) }
  refine ⟨ℕ, inferInstance, C, ?_, ?_⟩
  · -- VCDim C < ⊤: C shatters singletons but not pairs.
    -- Upper bound: VCDim ≤ 1.
    -- For any S with |S| ≥ 2, let a, b ∈ S with a ≠ b.
    -- The labeling f(a) = true, f(b) = true requires ∃ n, (a == n) = true ∧ (b == n) = true,
    -- i.e., a = n = b, contradicting a ≠ b. So S is not shattered.
    have hle : VCDim ℕ C ≤ 1 := by
      unfold VCDim
      apply iSup₂_le
      intro S hS
      -- Show: if S is shattered by C, then |S| ≤ 1.
      -- Contrapositive: if |S| ≥ 2, S is not shattered.
      by_contra h
      push Not at h
      -- h : (1 : WithTop ℕ) < ↑S.card
      have hcard : 1 < S.card := by
        by_contra hle
        push Not at hle
        exact not_lt.mpr (WithTop.coe_le_coe.mpr hle) h
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      -- The all-true labeling: every point gets label `true`.
      obtain ⟨c, hcC, hcall⟩ := hS (fun _ => true)
      obtain ⟨n, hn⟩ := hcC
      have ha' := hcall ⟨a, ha⟩
      have hb' := hcall ⟨b, hb⟩
      -- c = fun x => decide (x = n), so c a = true means a = n, c b = true means b = n
      simp only [hn, decide_eq_true_eq] at ha' hb'
      exact hab (ha'.trans hb'.symm)
    exact lt_of_le_of_lt hle (WithTop.coe_lt_top 1)
  · -- SQDimension C D τ = ⊤ at D = Dirac at 0, τ = 1.
    -- For the Dirac measure δ₀ on ℕ and τ = 1:
    -- The correlation |∫ (if c₁ x = c₂ x then 1 else -1) dδ₀| ≤ 1 = τ always holds
    -- (since the integrand is bounded by 1 in absolute value and δ₀ is a probability measure).
    -- So every finite subfamily of C satisfies the pairwise bound at τ = 1.
    -- Since C is infinite, SQDim = ⊤.
    refine ⟨MeasureTheory.Measure.dirac 0,
            MeasureTheory.Measure.dirac.isProbabilityMeasure,
            1, one_pos, ?_⟩
    -- Show SQDimension ℕ C (Measure.dirac 0) 1 = ⊤.
    -- SQDimension is ⨆ over Finsets S of concepts with S ⊆ C and pairwise |corr| ≤ 1.
    -- For any n, we can find a Finset of n+1 distinct concepts in C with |corr| ≤ 1.
    -- The bound |corr| ≤ 1 is trivially satisfied for any integrand bounded by [-1, 1]
    -- under any probability measure.
    -- The hard part: constructing the Finset witness with the integral bound.
    -- The integral ∫ x, (if c₁ x = c₂ x then 1 else -1) ∂(dirac 0) evaluates to
    -- (if c₁ 0 = c₂ 0 then 1 else -1), and |±1| ≤ 1 = τ.
    -- So the pairwise correlation condition holds for ALL pairs at τ = 1.
    -- Strategy: show ∀ b < ⊤, ∃ S with card > b and pairwise |corr| ≤ 1.
    -- For each n, construct a Finset of n distinct singleton indicators.
    -- The pairwise |correlation| ≤ 1 holds trivially under Dirac measure
    -- (∫ f d(dirac 0) = f 0, and |f 0| ≤ 1 since f 0 ∈ {-1, 1}).
    unfold SQDimension
    rw [iSup₂_eq_top]
    intro b hb
    -- b < ⊤ in WithTop ℕ, so b = ↑n for some n.
    obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hb)
    -- Construct Finset of n+1 distinct concepts from C.
    classical
    let mkIndicator : ℕ → Concept ℕ Bool := fun k x => decide (x = k)
    have hinj : Function.Injective mkIndicator := by
      intro k₁ k₂ heq
      have h := congr_fun heq k₁
      simpa [mkIndicator] using h
    let S : Finset (Concept ℕ Bool) := (Finset.range (n + 1)).image mkIndicator
    have hcard : S.card = n + 1 := by
      rw [Finset.card_image_of_injective _ hinj]
      exact Finset.card_range (n + 1)
    -- S ⊆ C: every indicator is in C.
    have hsubC : ↑S ⊆ C := by
      intro f hf
      simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hf
      obtain ⟨k, _, rfl⟩ := hf
      exact ⟨k, rfl⟩
    -- Pairwise correlation ≤ 1: under dirac 0, ∫ f d(dirac 0) = f 0.
    have hcorr : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ →
        |∫ x, (if c₁ x = c₂ x then (1 : ℝ) else -1)
          ∂MeasureTheory.Measure.dirac (0 : ℕ)| ≤ 1 := by
      intro c₁ _ c₂ _ _
      rw [MeasureTheory.integral_dirac]
      split_ifs <;> simp
    refine ⟨S, ⟨hsubC, hcorr⟩, ?_⟩
    rw [hcard]
    exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_of_le (le_refl n))
