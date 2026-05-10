/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Criterion.PAC
import LeanPool.FormalLearningTheory.Criterion.Online
import LeanPool.FormalLearningTheory.Criterion.Gold
import LeanPool.FormalLearningTheory.Criterion.Extended
import LeanPool.FormalLearningTheory.Complexity.Structures
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Complexity.Symmetrization
import LeanPool.FormalLearningTheory.Complexity.Measurability
import LeanPool.FormalLearningTheory.Theorem.Online
import LeanPool.FormalLearningTheory.PureMath.Concentration
import Mathlib.Probability.Moments.Variance

/-!
# Separation Theorems

These prove that the paradigms are genuinely different —
the criteria do NOT imply each other.
-/

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

-- ============================================================
-- Adversary lemma: Shatters → VCDim ≤ mistake bound (universe-polymorphic)
-- ============================================================

/-- Count mistakes starting from state s (universe-polymorphic version). -/
private noncomputable def mistakesFromU {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      mistakesFromU L (L.update s x (c x)) c xs

/-- Relate mistakesFromU to the original mistakes function. -/
private theorem mistakesFromU_init_eq {X : Type u}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    mistakesFromU L L.init c seq = L.mistakes c seq := by
  suffices h : ∀ (s : L.State) (acc : ℕ),
      OnlineLearner.mistakes.go L c s seq acc = mistakesFromU L s c seq + acc by
    simp [OnlineLearner.mistakes, h L.init 0]
  induction seq with
  | nil => intro s acc; simp [OnlineLearner.mistakes.go, mistakesFromU]
  | cons x xs ih =>
    intro s acc
    simp only [OnlineLearner.mistakes.go, mistakesFromU]
    rw [ih]
    by_cases h : L.predict s x = c x
    · simp_all
    · simp_all; omega

/-- Restricted shattering: if C shatters S and we restrict to {c ∈ C | c x = b},
    then S \ {x} is shattered by the restricted class (when x ∈ S). -/
private theorem shatters_restrict {X : Type u} [DecidableEq X] {C : ConceptClass X Bool}
    {S : Finset X} (hshat : Shatters X C S) {x : X} (hx : x ∈ S) (b : Bool) :
    Shatters X {c ∈ C | c x = b} (S.erase x) := by
  classical
  intro f
  -- Build labeling on S: assign x ↦ b, everything else per f
  let f' : ↥S → Bool := fun ⟨y, hy⟩ =>
    if h : y ∈ S.erase x then f ⟨y, h⟩ else b
  obtain ⟨c, hcC, hc⟩ := hshat f'
  have hcx : c x = b := by
    have := hc ⟨x, hx⟩
    simp only [f', Finset.mem_erase, ne_eq, not_true_eq_false, false_and, dite_false] at this
    exact this
  refine ⟨c, ⟨hcC, hcx⟩, fun ⟨y, hy⟩ => ?_⟩
  have hy_S : y ∈ S := Finset.mem_of_mem_erase hy
  have := hc ⟨y, hy_S⟩
  simp only [f', hy, dite_true] at this
  exact this

/-- Adversary argument directly from shattering (universe-polymorphic).
    Given a shattered set S and any online learner L starting from state s,
    there exists a sequence and target concept where L makes |S| mistakes. -/
private theorem adversary_from_shatters {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {S : Finset X}
    (hshat : Shatters X C S) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      mistakesFromU L s c seq = S.card := by
  classical
  induction S using Finset.induction_on generalizing C s with
  | empty =>
    obtain ⟨c₀, hc₀, _⟩ := hshat (fun ⟨_, h⟩ => by simp at h)
    exact ⟨[], c₀, hc₀, rfl⟩
  | @insert x S' hx ih =>
    -- Present x to L. Choose label that causes a mistake.
    by_cases hpred : L.predict s x = true
    · -- L predicts true → assign false
      have hshat' := shatters_restrict hshat (Finset.mem_insert_self x S') false
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ :=
        ih (s := L.update s x false) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesFromU, hc'mem.2, hpred, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega
    · -- L predicts false → assign true
      have hpf : L.predict s x = false := by
        cases h : L.predict s x <;> simp_all
      have hshat' := shatters_restrict hshat (Finset.mem_insert_self x S') true
      rw [Finset.erase_insert hx] at hshat'
      obtain ⟨seq', c', hc'mem, hcount⟩ :=
        ih (s := L.update s x true) hshat'
      refine ⟨x :: seq', c', hc'mem.1, ?_⟩
      simp only [mistakesFromU, hc'mem.2, hpf, Finset.card_insert_of_notMem hx]
      simp [hcount]; omega

/-- Mistake-bounded learner → VCDim ≤ M (universe-polymorphic). -/
private theorem vcdim_le_of_mistake_bounded {X : Type u}
    {C : ConceptClass X Bool} {M : ℕ}
    (hM : MistakeBounded X Bool C M) : VCDim X C ≤ ↑M := by
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard : M + 1 ≤ S.card := by exact_mod_cast WithTop.coe_lt_coe.mp hgt
  obtain ⟨L, hL⟩ := hM
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_from_shatters L L.init hshat
  have hbound := hL c hcC seq
  rw [← mistakesFromU_init_eq] at hbound
  omega

/-- Online learnable → PAC learnable.
    Γ₄₈: requires LittlestoneDim → VCDim bridge or online-to-batch conversion. -/
theorem online_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hol : OnlineLearnable X Bool C)
    [MeasurableConceptClass X C] :
    PACLearnable X C := by
  have hmeas_C := MeasurableConceptClass.hmeas_C C
  have hc_meas := MeasurableConceptClass.hc_meas C
  have hWB := MeasurableConceptClass.hWB C
  -- Step 1: OnlineLearnable gives mistake bound M
  obtain ⟨M, hM⟩ := hol
  -- Step 2: VCDim ≤ M < ⊤
  have hvcdim : VCDim X C < ⊤ := by
    calc VCDim X C ≤ ↑M := vcdim_le_of_mistake_bounded hM
      _ < ⊤ := WithTop.coe_lt_top M
  -- Step 3: VCDim < ⊤ → PACLearnable (via UC route, no bad_consistent_covering)
  exact vcdim_finite_imp_pac_via_uc' X C hvcdim hmeas_C hc_meas hWB

/-- Majority vote: returns true iff strictly more than half the votes are true. -/
private def boosted_majority (k : ℕ) (votes : Fin k → Bool) : Bool :=
  k < 2 * ((Finset.univ.filter (fun j => votes j)).card)

-- chebyshev_majority_bound moved to MathLib.Concentration

-- ============================================================
-- FP4 Phase 1: Scaffolding for boost_two_thirds_to_pac
-- ============================================================

/-- Joint measurability of a batch learner's evaluation map. -/
def LearnEvalMeasurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop :=
  ∀ m : ℕ,
    Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2)

/-- T1: A learner with joint measurability gives measurable hypotheses for fixed training data. -/
private lemma learn_measurable_fixed
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  exact (hL_meas m).comp (measurable_const.prodMk measurable_id)

/-- The event that block j produces a hypothesis with D-error ≤ rate(n). -/
private def goodBlockEvent
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (D : MeasureTheory.Measure X)
    (c : Concept X Bool) (rate : ℕ → ℝ)
    (k n : ℕ) (j : Fin k) : Set (Fin (k * n) → X) :=
  { ω : Fin (k * n) → X |
      D { x : X |
          L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x }
        ≤ ENNReal.ofReal (rate n) }

/-- T2: goodBlockEvent is measurable for each block index j. -/
private lemma goodBlockEvent_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (k n : ℕ) :
    ∀ j : Fin k, MeasurableSet (goodBlockEvent L D c rate k n j) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  intro j
  -- Prove measurability of the "good training set" event (inline T0 argument)
  have h_label : Measurable (fun p : (Fin n → X) × X =>
      fun i : Fin n => (p.1 i, c (p.1 i))) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (hc_meas.comp ((measurable_pi_apply i).comp measurable_fst)))
  have h_joint : Measurable (fun p : (Fin n → X) × X =>
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2) :=
    (hL_meas n).comp (h_label.prodMk measurable_snd)
  have h_c_snd : Measurable (fun p : (Fin n → X) × X => c p.2) :=
    hc_meas.comp measurable_snd
  have h_disagree : MeasurableSet {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} :=
    (measurableSet_eq_fun h_joint h_c_snd).compl
  have h_sec_eq : ∀ xs : Fin n → X, Prod.mk xs ⁻¹' {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} =
      {x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x} := by
    intro xs; ext x; rfl
  have h_meas_fn : Measurable (fun xs : Fin n → X =>
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }) := by
    have := measurable_measure_prodMk_left (ν := D) h_disagree
    simp only [h_sec_eq] at this
    exact this
  have hA : MeasurableSet
      { xs : Fin n → X |
          D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
            ≤ ENNReal.ofReal (rate n) } :=
    h_meas_fn measurableSet_Iic
  -- goodBlockEvent is the preimage of A under block_extract
  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => block_extract k n ω j) ⁻¹'
        { xs : Fin n → X |
            D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (rate n) } := by
    ext ω; rfl
  rw [hpre]
  exact measurableSet_preimage (block_extract_measurable k n j) hA

/-- T0: Shared helper — measurability of the "good training set" event for a single block. -/
private lemma measurableSet_goodBlock_A
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (n : ℕ) :
    MeasurableSet
      { xs : Fin n → X |
          D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
            ≤ ENNReal.ofReal (rate n) } := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  -- Step 1: The labeling map (xs, x) ↦ (fun i => (xs i, c (xs i))) is measurable
  have h_label : Measurable (fun p : (Fin n → X) × X =>
      fun i : Fin n => (p.1 i, c (p.1 i))) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (hc_meas.comp ((measurable_pi_apply i).comp measurable_fst)))
  -- Joint measurability: (xs, x) ↦ L.learn(labeled(xs)) x
  have h_joint : Measurable (fun p : (Fin n → X) × X =>
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2) :=
    (hL_meas n).comp (h_label.prodMk measurable_snd)
  -- c ∘ snd: (xs, x) ↦ c x
  have h_c_snd : Measurable (fun p : (Fin n → X) × X => c p.2) :=
    hc_meas.comp measurable_snd
  -- Disagreement set is measurable in the product space
  have h_disagree : MeasurableSet {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} :=
    (measurableSet_eq_fun h_joint h_c_snd).compl
  -- Step 2: Section-measure function xs ↦ D{x | learn(xs)(x) ≠ c(x)} is measurable
  have h_sec_eq : ∀ xs : Fin n → X, Prod.mk xs ⁻¹' {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} =
      {x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x} := by
    intro xs; ext x; rfl
  have h_meas_fn : Measurable (fun xs : Fin n → X =>
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }) := by
    have := measurable_measure_prodMk_left (ν := D) h_disagree
    simp only [h_sec_eq] at this
    exact this
  -- Step 3: Preimage of Iic under measurable function
  exact h_meas_fn measurableSet_Iic

/-- T3: Block extraction pushforward of product measure equals product measure. -/
private lemma map_block_extract_eq_pi
    {X : Type u} [MeasurableSpace X]
    (k n : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)).map
      (fun ω : Fin (k * n) → X => block_extract k n ω j)
      =
    MeasureTheory.Measure.pi (fun _ : Fin n => D) := by
  open MeasureTheory MeasureTheory.Measure ProbabilityTheory Equiv in
  -- The currying MeasurableEquiv: Fin(k*n) → X  ≃ᵐ  Fin k → (Fin n → X)
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin n => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin n) X
  set e : (Fin (k * n) → X) ≃ᵐ (Fin k → Fin n → X) := pcl.trans cur
  -- block_extract = e pointwise
  have he : ∀ ω, block_extract k n ω j = e ω j := by
    intro ω; ext i
    simp only [block_extract, e, MeasurableEquiv.trans_apply, pcl, cur]
    simp [MeasurableEquiv.piCongrLeft, piCongrLeft_apply, MeasurableEquiv.curry,
      Function.curry]
  set μ := Measure.pi (fun _ : Fin (k * n) => D)
  set D' : Fin k → Measure (Fin n → X) := fun _ => Measure.pi (fun _ : Fin n => D)
  -- μ.map pcl preserves measure
  have hpcl : MeasurePreserving pcl μ (Measure.pi (fun _ : Fin k × Fin n => D)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k × Fin n => D) finProdFinEquiv.symm
  -- (flat on Fin k × Fin n).map cur = nested product
  have hcur : (Measure.pi (fun _ : Fin k × Fin n => D)).map cur = Measure.pi D' := by
    have h1 : Measure.pi (fun _ : Fin k × Fin n => D) =
        infinitePi (fun _ : Fin k × Fin n => D) :=
      (infinitePi_eq_pi (μ := fun _ : Fin k × Fin n => D)).symm
    rw [h1]
    have h3 : D' = fun _ : Fin k => infinitePi (fun _ : Fin n => D) := by
      funext; exact (infinitePi_eq_pi (μ := fun _ : Fin n => D)).symm
    have h2 : Measure.pi D' = infinitePi D' :=
      (infinitePi_eq_pi (μ := D')).symm
    rw [h2, h3]
    exact infinitePi_map_curry (fun _ : Fin k => fun _ : Fin n => D)
  -- μ.map e = Measure.pi D'
  have hmap_e : μ.map e = Measure.pi D' := by
    have : (e : (Fin (k * n) → X) → (Fin k → Fin n → X)) = cur ∘ pcl := rfl
    rw [this, ← map_map cur.measurable pcl.measurable, hpcl.map_eq, hcur]
  -- Factor through e and project
  have hcomp : (fun ω => block_extract k n ω j) = (fun f => f j) ∘ (e : (Fin (k * n) → X) → _) := by
    ext ω i; exact congrFun (he ω) i
  calc μ.map (fun ω => block_extract k n ω j)
      = μ.map ((fun f => f j) ∘ (e : (Fin (k * n) → X) → _)) := by rw [hcomp]
    _ = (Measure.pi D').map (fun f => f j) := by
          rw [← map_map (measurable_pi_apply j) e.measurable, hmap_e]
    _ = D' j := (measurePreserving_eval D' j).map_eq
    _ = Measure.pi (fun _ : Fin n => D) := rfl

/-- T5: The goodBlockEvents are independent under the product measure. -/
private lemma iIndepSet_goodBlockEvents
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (k n : ℕ) :
    ProbabilityTheory.iIndepSet
      (goodBlockEvent L D c rate k n)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D)) := by
  -- Step 1: Define A (good training set) and express goodBlockEvent as preimage
  let A : Set (Fin n → X) :=
    { xs : Fin n → X |
        D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
          ≤ ENNReal.ofReal (rate n) }
  have hA : MeasurableSet A := measurableSet_goodBlock_A L D c hc_meas rate n
  have hpre : ∀ j : Fin k, goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => block_extract k n ω j) ⁻¹' A := by
    intro j; ext ω; rfl
  -- Step 2: Convert iIndepSet to iIndep, then bridge from iIndepFun
  rw [ProbabilityTheory.iIndepSet_iff_iIndep]
  apply ProbabilityTheory.iIndep_of_iIndep_of_le
      ((ProbabilityTheory.iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_block_extract k n D))
  -- Step 3: Show generateFrom {goodBlockEvent j} ≤ comap (block_extract · j) _
  intro j
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs, hpre j]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩

/-- T4: each block's good event has probability at least `2 / 3`, transported from
the base learner guarantee. -/
private lemma goodBlockEvent_prob_ge_two_thirds
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L] (rate : ℕ → ℝ)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3))
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hcC : c ∈ C) (hc_meas : Measurable c)
    (k n : ℕ) (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D))
      (goodBlockEvent L D c rate k n j)
      ≥ ENNReal.ofReal (2 / 3) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  -- Step 1: Express goodBlockEvent as preimage of the "good training set" A under block_extract
  let A : Set (Fin n → X) :=
    { xs : Fin n → X |
        D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
          ≤ ENNReal.ofReal (rate n) }
  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => block_extract k n ω j) ⁻¹' A := by
    ext ω; rfl
  -- Step 2: Push forward via map_block_extract_eq_pi
  have hA : MeasurableSet A := measurableSet_goodBlock_A L D c hc_meas rate n
  rw [hpre, ← MeasureTheory.Measure.map_apply (block_extract_measurable k n j) hA,
      map_block_extract_eq_pi k n D j]
  -- Step 3: Apply the base learner guarantee
  exact huniv D inferInstance c hcC n

section ClassicalInstances

attribute [local instance] Classical.propDecidable

/-- T6: Chebyshev concentration for 7 / 12 threshold — when k ≥ 36/δ independent events
    each have probability ≥ 2 / 3, the fraction exceeding 7 / 12 is ≥ 1-δ. -/
private lemma chebyshev_seven_twelfths_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (36 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2 / 3)) :
    μ {ω | 7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ) := by
  open MeasureTheory ProbabilityTheory Finset in
  -- Step 1: Define indicator random variables X_j and their sum S
  set X : Fin k → Ω → ℝ := fun j => (events j).indicator (fun _ => (1 : ℝ))
  set S : Ω → ℝ := fun ω => ∑ j : Fin k, X j ω
  -- Step 2: S counts the number of events that hold
  have hS_count : ∀ ω, S ω = ((univ.filter (fun j => ω ∈ events j)).card : ℝ) := by
    intro ω; simp only [S, X, Set.indicator_apply]
    conv_lhs => arg 2; ext j; rw [show (if ω ∈ events j then (1 : ℝ) else 0) =
      (if ω ∈ events j then 1 else 0 : ℕ) from by split_ifs <;> simp]
    rw [← Nat.cast_sum, Finset.sum_boole]; rfl
  -- Step 3: The indicator functions are independent
  have hindep_fun : iIndepFun (m := fun _ => inferInstance)
      (fun j => (events j).indicator (fun _ => (1 : ℝ))) μ :=
    hindep.iIndepFun_indicator
  -- Step 4: Each X_j is bounded in [0, 1], hence MemLp 2
  have hX_bound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro j; apply Filter.Eventually.of_forall; intro ω
    simp only [X, Set.indicator_apply, Set.mem_Icc]
    split_ifs <;> constructor <;> norm_num
  have hX_meas : ∀ j, AEMeasurable (X j) μ := by
    intro j
    exact (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable.aemeasurable
  have hX_memLp : ∀ j, MemLp (X j) 2 μ := by
    intro j
    exact memLp_of_bounded (hX_bound j)
      (stronglyMeasurable_one.indicator (hevents_meas j)).aestronglyMeasurable 2
  -- Step 5: Variance of each X_j ≤ 1 / 4 (Popoviciu)
  have hvar_bound : ∀ j, ProbabilityTheory.variance (X j) μ ≤ 1 / 4 := by
    intro j
    calc ProbabilityTheory.variance (X j) μ
        ≤ ((1 - 0) / 2) ^ 2 := variance_le_sq_of_bounded (hX_bound j) (hX_meas j)
      _ = 1 / 4 := by norm_num
  -- Step 6: Pairwise independence for variance_sum
  have hpairwise : Set.Pairwise (↑(univ : Finset (Fin k)))
      (fun i j => (X i) ⟂ᵢ[μ] (X j)) := by
    intro i _ j _ hij; exact hindep_fun.indepFun hij
  -- Step 7: Variance of S = sum of variances ≤ k/4
  have hvar_S : ProbabilityTheory.variance (∑ j : Fin k, X j) μ ≤ k / 4 := by
    rw [IndepFun.variance_sum (fun i _ => hX_memLp i) hpairwise]
    calc ∑ j : Fin k, ProbabilityTheory.variance (X j) μ
        ≤ ∑ _j : Fin k, (1 : ℝ) / 4 := sum_le_sum (fun j _ => hvar_bound j)
      _ = k * (1 / 4) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = k / 4 := by ring
  -- Step 8: k > 0
  have hk_pos : (0 : ℝ) < ↑k := lt_of_lt_of_le (by positivity : (0 : ℝ) < 36 / δ) hk
  -- Step 9: E[X_j] ≥ 2 / 3
  have hEX : ∀ j, ∫ ω, X j ω ∂μ ≥ 2 / 3 := by
    intro j; simp only [X]
    rw [integral_indicator_const (1 : ℝ) (hevents_meas j), smul_eq_mul, mul_one]
    rw [ge_iff_le, ← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)
      (hprob j).le
  -- Step 10: Integrability
  have hX_int : ∀ j, Integrable (X j) μ := fun j => (hX_memLp j).integrable one_le_two
  -- Step 11: E[S] ≥ 2k/3 (S = fun ω => ∑ j, X j ω)
  have hES : ∫ ω, S ω ∂μ ≥ 2 * ↑k / 3 := by
    change ∫ ω, (∑ j : Fin k, X j ω) ∂μ ≥ _
    rw [integral_finset_sum univ (fun j _ => hX_int j)]
    calc ∑ j : Fin k, ∫ ω, X j ω ∂μ
        ≥ ∑ _j : Fin k, (2 : ℝ) / 3 := sum_le_sum (fun j _ => hEX j)
      _ = ↑k * (2 / 3) := by rw [sum_const]; simp [nsmul_eq_mul]
      _ = 2 * ↑k / 3 := by ring
  -- Step 12: MemLp S 2 μ
  have hS_memLp : MemLp S 2 μ := by
    change MemLp (fun ω => ∑ j : Fin k, X j ω) 2 μ
    have h := memLp_finset_sum univ (fun j (_ : j ∈ univ) => hX_memLp j)
    convert h using 1
  -- Step 13: Var[S] ≤ k/4
  have hvar_S_fn : ProbabilityTheory.variance S μ ≤ ↑k / 4 := by
    change ProbabilityTheory.variance (fun ω => ∑ j : Fin k, X j ω) μ ≤ _
    have : ProbabilityTheory.variance (fun ω => ∑ j : Fin k, X j ω) μ =
        ProbabilityTheory.variance (∑ j : Fin k, X j) μ := by
      congr 1; ext ω; simp [sum_apply]
    rw [this]; exact hvar_S
  -- Step 14: Apply Chebyshev
  have hk12_pos : (0 : ℝ) < ↑k / 12 := by positivity
  have hcheb := meas_ge_le_variance_div_sq hS_memLp hk12_pos
  -- Step 15: Bound Var[S]/(k/12)^2 ≤ δ
  have hcheb_bound : ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2) ≤ δ := by
    calc ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2)
        ≤ (↑k / 4) / ((↑k / 12) ^ 2) :=
          div_le_div_of_nonneg_right hvar_S_fn (sq_nonneg _)
      _ = 36 / ↑k := by field_simp; ring
      _ ≤ δ := by
          rw [div_le_iff₀ hk_pos]
          have h36 : 36 / δ * δ = 36 := div_mul_cancel₀ 36 (ne_of_gt h_delta_pos)
          nlinarith [hk]
  -- Step 16: μ{bad} ≤ ofReal δ
  have hbad_le : μ {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} ≤ ENNReal.ofReal δ :=
    le_trans hcheb (ENNReal.ofReal_le_ofReal hcheb_bound)
  -- Step 17: {S ≥ 7k/12}ᶜ ⊆ {bad}
  have hcompl_sub : {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ⊆
      {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [Set.mem_setOf_eq]
    have hgap : ∫ ω, S ω ∂μ - S ω ≥ ↑k / 12 := by linarith
    calc ↑k / 12 ≤ ∫ ω, S ω ∂μ - S ω := hgap
      _ ≤ |S ω - ∫ ω, S ω ∂μ| := by rw [abs_sub_comm]; exact le_abs_self _
  -- Step 18: μ{S ≥ 7k/12}ᶜ ≤ ofReal δ
  have hcompl_le : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ≤ ENNReal.ofReal δ :=
    le_trans (μ.mono hcompl_sub) hbad_le
  -- Step 19: Measurability
  have hS_meas : Measurable S := by
    change Measurable (fun ω => ∑ j : Fin k, X j ω)
    exact Finset.measurable_sum _ (fun j _ =>
      (stronglyMeasurable_one.indicator (hevents_meas j)).measurable)
  have hmeas : MeasurableSet {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} :=
    hS_meas measurableSet_Ici
  -- Step 20: μ{S ≥ 7k/12} ≥ 1 - δ
  have hgood : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} ≥ ENNReal.ofReal (1 - δ) := by
    rw [ge_iff_le]
    have h_add : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} + μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ = 1 := by
      rw [measure_add_measure_compl hmeas, measure_univ]
    by_cases hδ1 : δ ≤ 1
    · -- ENNReal.ofReal (1-δ) = 1 - ENNReal.ofReal δ
      rw [ENNReal.ofReal_sub 1 h_delta_pos.le, ENNReal.ofReal_one]
      -- From h_add: μ{good} + μ{compl} = 1
      -- So μ{good} = 1 - μ{compl} (since μ{compl} ≤ 1)
      have hcompl_le_one : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ≤ 1 := by
        calc μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ≤ μ Set.univ := μ.mono (Set.subset_univ _)
          _ = 1 := measure_univ
      -- μ{good} = 1 - μ{compl} from h_add
      have hne : μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hcompl_le_one
      have hgood_eq : 1 - μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ = μ {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} :=
        ENNReal.sub_eq_of_eq_add hne h_add.symm
      rw [← hgood_eq]
      exact tsub_le_tsub_left hcompl_le _
    · push Not at hδ1
      have h1d : 1 - δ ≤ 0 := by linarith
      simp [ENNReal.ofReal_eq_zero.mpr h1d]
  -- Step 21: Convert from {7k/12 ≤ S ω} to {7*k ≤ 12 * card}
  apply le_trans hgood
  apply μ.mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hS_count ω] at hω
  have : (7 : ℝ) * ↑k ≤ 12 * ↑(univ.filter (fun j => ω ∈ events j)).card := by
    linarith
  exact_mod_cast this

end ClassicalInstances

/-- T7: If ≥ 7 / 12 of the hypotheses have D-error ≤ ρ, majority vote has D-error ≤ 7ρ. -/
private lemma majority_error_le_seven_rate_of_good_fraction
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    {k : ℕ} (hk_pos : 0 < k)
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : Fin k → Concept X Bool)
    (hhs_meas : ∀ j : Fin k, Measurable (hs j))
    (good : Finset (Fin k))
    (hgoodfrac : 7 * k ≤ 12 * good.card)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgooderr : ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal ρ) :
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
      ≤ ENNReal.ofReal (7 * ρ) := by
  classical
  let bad : Fin k → Set X := fun j => {x : X | hs j x ≠ c x}
  have hbad_meas : ∀ j, MeasurableSet (bad j) := by
    intro j
    change MeasurableSet {x : X | hs j x ≠ c x}
    have : {x : X | hs j x ≠ c x} = {x : X | hs j x = c x}ᶜ := by
      ext x; simp [ne_eq, Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [this]
    exact (measurableSet_eq_fun (hhs_meas j) hc_meas).compl
  let G : X → ENNReal := fun x =>
    ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
  have hG_meas : Measurable G := by
    refine Finset.measurable_sum good ?_
    intro j _
    exact Measurable.indicator measurable_const (hbad_meas j)
  have hG_ae : AEMeasurable G D := hG_meas.aemeasurable
  let threshold : ENNReal := (2 * good.card - k : ℕ)
  have hklt : k < 2 * good.card := by
    have : (7 : ℕ) * k ≤ 12 * good.card := hgoodfrac
    omega
  have hden_pos_nat : 0 < 2 * good.card - k := Nat.sub_pos_of_lt hklt
  have hmajority_sub :
      {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ⊆ {x : X | threshold ≤ G x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    set wrongAll : ℕ := (Finset.univ.filter (fun j => hs j x ≠ c x)).card with hwrongAll_def
    set wrongGood : ℕ := (good.filter (fun j => hs j x ≠ c x)).card with hwrongGood_def
    have hwrong_all : k ≤ 2 * wrongAll := by
      -- boosted_majority disagrees with c x means majority voted wrong
      have hfilt_id : (Finset.univ.filter (fun j : Fin k => hs j x)).card
          = (Finset.univ.filter (fun j : Fin k => hs j x = true)).card := by
        simp
      cases hcx : c x with
      | false =>
        have hmaj : boosted_majority k (fun j => hs j x) = true := by
          by_contra h
          simp [Bool.not_eq_true] at h
          simp [h, hcx] at hx
        change decide (k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card) =
          true at hmaj
        have hmaj_lt : k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x = true)).card := by
          have hmaj_bool : k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card :=
            of_decide_eq_true hmaj
          rwa [hfilt_id] at hmaj_bool
        have hfilt_ne : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = true)) := by
          ext j; simp [hcx]
        rw [hwrongAll_def, hfilt_ne]
        omega
      | true =>
        have hmaj : boosted_majority k (fun j => hs j x) = false := by
          by_contra h
          simp [Bool.not_eq_false] at h
          simp [h, hcx] at hx
        change decide (k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card) =
          false at hmaj
        have hmaj_le : 2 * (Finset.univ.filter (fun j : Fin k => hs j x = true)).card ≤ k := by
          have hmaj_not : ¬ k < 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card :=
            decide_eq_false_iff_not.mp hmaj
          have hmaj_bool : 2 * (Finset.univ.filter (fun j : Fin k => hs j x)).card ≤ k := by
            omega
          rwa [hfilt_id] at hmaj_bool
        have hfilt_ne : (Finset.univ.filter (fun j : Fin k => hs j x ≠ c x))
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)) := by
          ext j; simp [hcx]
        have hcomp2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
          (fun j => hs j x = true)
        simp only [Finset.card_univ, Fintype.card_fin] at hcomp2
        have hfilt_false : (Finset.univ.filter (fun j : Fin k => ¬hs j x = true)).card
            = (Finset.univ.filter (fun j : Fin k => hs j x = false)).card := by
          congr 1; ext j; simp [Bool.not_eq_true]
        rw [hwrongAll_def, hfilt_ne]
        omega
    have hwrong_split : wrongAll ≤ wrongGood + (k - good.card) := by
      -- Every wrong voter in univ is either in good or not in good
      -- wrongAll = #{j ∈ univ | wrong}, wrongGood = #{j ∈ good | wrong}
      -- #{j ∈ univ \ good | wrong} ≤ |univ \ good| = k - good.card
      have hgood_card_le : good.card ≤ k := by
        calc good.card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = k := Finset.card_fin k
      -- univ.filter p = (good.filter p) ∪ ((univ \ good).filter p)
      have hunion : Finset.univ.filter (fun j : Fin k => hs j x ≠ c x)
          = (good.filter (fun j => hs j x ≠ c x)) ∪
            ((Finset.univ \ good).filter (fun j => hs j x ≠ c x)) := by
        ext j
        simp [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint (good.filter (fun j => hs j x ≠ c x))
          ((Finset.univ \ good).filter (fun j => hs j x ≠ c x)) := by
        apply Finset.disjoint_filter_filter
        exact disjoint_sdiff_self_right
      rw [hwrongAll_def, hunion, Finset.card_union_of_disjoint hdisj]
      have : ((Finset.univ \ good).filter (fun j : Fin k => hs j x ≠ c x)).card
          ≤ (Finset.univ \ good).card := Finset.card_filter_le _ _
      have hsdiff_card : (Finset.univ \ good).card = k - good.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        simp
      omega
    have hthreshold_nat : 2 * good.card - k ≤ 2 * wrongGood := by
      have h1 := hwrong_all
      have h2 := hwrong_split
      have h3 : good.card ≤ k := by
        calc good.card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = k := Finset.card_fin k
      omega
    change threshold ≤ G x
    suffices h : (2 * good.card - k : ℕ) ≤ 2 * wrongGood by
      change (↑(2 * good.card - k) : ENNReal) ≤
        ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
      have hsum_eq : ∑ j ∈ good, (bad j).indicator (fun _ => (2 : ENNReal)) x
          = ↑(2 * wrongGood) := by
        simp only [bad, Set.indicator_apply, Set.mem_setOf_eq]
        trans (∑ j ∈ good, if hs j x ≠ c x then (2 : ENNReal) else 0)
        · rfl
        have hcast : ∀ j ∈ good, (if hs j x ≠ c x then (2 : ENNReal) else 0)
            = (↑(if hs j x ≠ c x then 2 else 0 : ℕ) : ENNReal) := by
          intro j _; split <;> simp
        rw [Finset.sum_congr rfl hcast]
        push_cast [← Nat.cast_sum]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul, mul_comm]
        rfl
      rw [hsum_eq]
      exact_mod_cast h
    exact hthreshold_nat
  have hG_int :
      ∫⁻ x, G x ∂D ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := by
    have hsum_ae :
        ∀ j ∈ good,
          AEMeasurable ((bad j).indicator (fun _ => (2 : ENNReal))) D := by
      intro j _
      exact (Measurable.indicator measurable_const (hbad_meas j)).aemeasurable
    calc
      ∫⁻ x, G x ∂D
          = ∑ j ∈ good, ∫⁻ x, (bad j).indicator (fun _ => (2 : ENNReal)) x ∂D := by
              exact lintegral_finset_sum' good hsum_ae
      _ ≤ ∑ j ∈ good, ENNReal.ofReal (2 * ρ) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [lintegral_indicator_const (hbad_meas j)]
            calc (2 : ENNReal) * D (bad j)
                ≤ 2 * ENNReal.ofReal ρ := by gcongr; exact hgooderr j hj
              _ = ENNReal.ofReal (2 * ρ) := by
                    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = ↑good.card * ENNReal.ofReal (2 * ρ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ↑good.card * ρ) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
  have hthresh_ne_zero : threshold ≠ 0 := by
    change (↑(2 * good.card - k) : ENNReal) ≠ 0
    exact_mod_cast hden_pos_nat.ne'
  have hthresh_ne_top : threshold ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmarkov :
      D {x : X | threshold ≤ G x}
        ≤ (∫⁻ x, G x ∂D) / threshold :=
    meas_ge_le_lintegral_div hG_ae hthresh_ne_zero hthresh_ne_top
  have hratio :
      (∫⁻ x, G x ∂D) / threshold ≤ ENNReal.ofReal (7 * ρ) := by
    rw [ENNReal.div_le_iff hthresh_ne_zero hthresh_ne_top]
    calc ∫⁻ x, G x ∂D
          ≤ ENNReal.ofReal (2 * ↑good.card * ρ) := hG_int
      _ ≤ ENNReal.ofReal (7 * ρ) * threshold := by
            change ENNReal.ofReal (2 * ↑good.card * ρ)
              ≤ ENNReal.ofReal (7 * ρ) * (↑(2 * good.card - k) : ENNReal)
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have hgf : (7 : ℝ) * ↑k ≤ 12 * ↑good.card := by exact_mod_cast hgoodfrac
            have hcast : (↑(2 * good.card - k) : ℝ) = 2 * ↑good.card - ↑k := by
              rw [Nat.cast_sub (by omega : k ≤ 2 * good.card)]
              push_cast; ring
            rw [hcast]
            nlinarith
  calc
    D {x : X | boosted_majority k (fun j => hs j x) ≠ c x}
        ≤ D {x : X | threshold ≤ G x} := D.mono hmajority_sub
    _ ≤ (∫⁻ x, G x ∂D) / threshold := hmarkov
    _ ≤ ENNReal.ofReal (7 * ρ) := hratio

/-- T8: If ≥ 7 / 12 of blocks are good, the boosted hypothesis has D-error ≤ 7·max(rate(n),0). -/
private lemma boosted_sample_error_le_of_good_blocks
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (rate : ℕ → ℝ) (k n : ℕ)
    (ω : Fin (k * n) → X)
    (hk_pos : 0 < k)
    (hgoodfrac :
      7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)).card) :
    D {x : X |
        boosted_majority k
          (fun j => L.learn
            (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x) ≠ c x}
      ≤ ENNReal.ofReal (7 * max (rate n) 0) := by
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  classical
  let hs : Fin k → Concept X Bool := fun j =>
    L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i)))
  let good : Finset (Fin k) :=
    Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)
  have hhs_meas : ∀ j : Fin k, Measurable (hs j) := by
    intro j
    haveI : MeasurableBatchLearner X L := ⟨hL_meas⟩
    exact learn_measurable_fixed L
      (fun i => (block_extract k n ω j i, c (block_extract k n ω j i)))
  have hgooderr :
      ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal (max (rate n) 0) := by
    intro j hj
    have hj' :
        D {x : X |
            L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x}
          ≤ ENNReal.ofReal (rate n) := by
      simpa [good, goodBlockEvent] using hj
    exact le_trans hj' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact majority_error_le_seven_rate_of_good_fraction
    (D := D) (k := k) hk_pos
    (c := c) (hc_meas := hc_meas)
    (hs := hs) (hhs_meas := hhs_meas)
    (good := good) (hgoodfrac := hgoodfrac)
    (ρ := max (rate n) 0) (hρ := le_max_right _ _)
    hgooderr

-- ============================================================
-- End FP4 Phase 1 scaffolding
-- ============================================================

/-- Boosting lemma: given a learner with success probability ≥ 2 / 3 under D^m,
    construct a boosted learner with success probability ≥ 1-δ for any δ > 0.
    Standard technique: run L independently k times on independent samples of
    size m₀, take majority vote.

    Construction:
    - kmin = ⌈9/δ⌉ + 2 (enough blocks for Chebyshev concentration)
    - m₀ from hrate(ε/kmin) so that rate(m₀) < ε/kmin
    - n = max m₀ (kmin - 1). Then k = n + 1 ≥ kmin.
    - Total samples: (n + 1) * n, with Nat.sqrt((n+1)*n) = n.
    - At sample size m = (n+1)*n, L' recovers k = n+1 blocks of size n.
    - Event containment: when > k/2 blocks have D-error ≤ rate(n) < ε/kmin,
      majority D-error ≤ k · rate(n) < k/kmin · ε ≤ ε via union bound.

    The measure-theoretic proof uses:
    (a) block_extract : (Fin (k*n) → X) → Fin k → (Fin n → X)
    (b) iIndepFun for block extractions under product measure D^(k*n)
    (c) chebyshev_majority_bound for i.i.d. Bernoulli(≥2 / 3) events
    (d) block extraction marginal = D^n
    (e) majority vote D-error analysis via union bound

    The helper lemmas below provide the concentration and majority analysis
    needed by the final PAC bound. -/
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    [MeasurableHypotheses X C]
    (L : BatchLearner X Bool) [MeasurableBatchLearner X L]
    (rate : ℕ → ℝ)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2 / 3)) :
    PACLearnable X C := by
  have hc_meas : ∀ c ∈ C, Measurable c := MeasurableHypotheses.mem_measurable (C := C)
  have hL_meas : LearnEvalMeasurable L := MeasurableBatchLearner.eval_measurable
  -- Step 1: Construct the boosted BatchLearner.
  -- L' splits m samples into k = Nat.sqrt(m)+1 blocks of size m/k,
  -- runs L on each block, and takes majority vote.
  let L' : BatchLearner X Bool := {
    hypotheses := Set.univ
    learn := fun {m} S x =>
      let k := Nat.sqrt m + 1
      let blk := m / k
      if blk = 0 then L.learn S x
      else
        boosted_majority k (fun j : Fin k =>
          L.learn (fun i : Fin blk => S ⟨j.val * blk + i.val, by
            have hj := j.isLt; have hi := i.isLt
            have hkblk : k * blk ≤ m := by
              rw [Nat.mul_comm]; exact Nat.div_mul_le_self m k
            calc j.val * blk + i.val
                < j.val * blk + blk := by omega
              _ = (j.val + 1) * blk := by ring
              _ ≤ k * blk := by exact Nat.mul_le_mul_right blk hj
              _ ≤ m := hkblk⟩) x)
    output_in_H := fun _ => Set.mem_univ _ }
  -- Step 2: Construct the sample complexity function.
  -- For given ε, δ > 0:
  --   kmin = ⌈36/δ⌉ + 2 (enough blocks for Chebyshev; ensures kmin ≥ 2)
  --   ε' = ε / 7 (rate target for majority error bound)
  --   m₀ = smallest n with rate(n) < ε'
  --   n = max m₀ (kmin - 1) (ensures n ≥ m₀ AND n+1 ≥ kmin)
  --   mf = (n+1) * n (= k * block_sz, with Nat.sqrt((n+1)*n) = n)
  refine ⟨L', fun ε δ =>
    if hε' : 0 < ε then
      if hδ' : 0 < δ then
        let kmin := Nat.ceil (36 / δ) + 2
        let ε' := ε / 7
        let m₀ := Nat.find (hrate ε' (by positivity))
        let n := max m₀ (kmin - 1)
        (n + 1) * n
      else 0
    else 0, ?_⟩
  -- Step 3: Prove the PAC bound.
  intro ε δ hε hδ D hD c hcC
  -- The proof goal is:
  --   Measure.pi (fun _ : Fin m => D) { xs | D { x | L'.learn ... x ≠ c x } ≤ ofReal ε }
  --     ≥ ofReal (1 - δ)
  -- where m = mf ε δ = (n + 1) * n.
  --
  -- PROOF STRUCTURE:
  -- 1. PARAMETER EXTRACTION:
  --    kmin = ⌈9/δ⌉ + 2, ε' = ε/kmin, m₀ from hrate(ε'), n = max m₀ (kmin-1).
  --    k = n+1 ≥ kmin ≥ ⌈9/δ⌉+2, so 9/δ ≤ k.
  --    rate(n) < ε' = ε/kmin since n ≥ m₀. Block size = n.
  --
  -- 2. LEARNER UNFOLDING:
  --    At sample size m = (n+1)*n, Nat.sqrt(m) = n (via Nat.sqrt_add_eq),
  --    so L' uses k = n+1 blocks of size n. The majority vote branch is entered
  --    since blk = n > 0.
  --
  -- 3. EVENT DEFINITION:
  --    events j = {ω : Fin m → X | D{x | h_j(ω)(x) ≠ c(x)} ≤ ofReal(rate n)}
  --    where h_j(ω) = L.learn(block_j(ω)) is the j-th block hypothesis.
  --
  -- 4. CONCENTRATION (requires chebyshev_majority_bound + independence):
  --    Each events j has μ-probability ≥ 2 / 3 (from huniv + marginal).
  --    Events are independent (from iIndepFun of block extractions).
  --    By Chebyshev: μ({> k/2 good}) ≥ 1 - 9/(4k) ≥ 1 - δ.
  --
  -- 5. EVENT CONTAINMENT (requires majority analysis + Markov bound):
  --    On {ALL blocks good}: for random x ~ D, let Y = #{j : h_j(x) ≠ c(x)}.
  --    E_D[Y] = Σ_j err_j ≤ k · rate(n). Majority errs iff Y > k/2.
  --    By Markov: D{Y > k/2} ≤ E[Y]/(k/2) = 2·rate(n) < 2·ε/kmin ≤ ε.
  --    (When kmin ≥ 2, we have 2/kmin ≤ 1, so 2·ε/kmin ≤ ε.)
  --    NOTE: This uses {ALL blocks good}, not just {> k/2 good}. The probability
  --    P[all good] ≥ 1 - k/3 requires k ≤ 3δ (too small). The full proof needs
  --    either the tournament/validation approach (SSBD Thm 7.7) or a more careful
  --    two-step analysis. Both routes require the same missing infrastructure.
  --
  -- 6. COMPOSE: μ({D-err ≤ ε}) ≥ μ({> k/2 good}) ≥ 1 - δ.
  -- Step 3a: Parameter extraction
  dsimp only
  rw [dif_pos hε, dif_pos hδ]
  have hε'_pos : 0 < ε / 7 := by positivity
  set kmin := Nat.ceil (36 / δ) + 2 with hkmin_def
  set n := max (Nat.find (hrate (ε / 7) hε'_pos)) (kmin - 1) with hn_def
  have hn_pos : 0 < n := by omega
  have hn1_pos : 0 < n + 1 := by omega
  have hsqrt : Nat.sqrt ((n + 1) * n) = n := by
    rw [show (n + 1) * n = n * n + n from by ring]
    exact Nat.sqrt_add_eq n (Nat.le_add_right n n)
  have hblk : (n + 1) * n / (n + 1) = n := Nat.mul_div_cancel_left n (by omega)
  have hblk_ne : ((n + 1) * n / (Nat.sqrt ((n + 1) * n) + 1)) ≠ 0 := by
    rw [hsqrt, hblk]; omega
  have hrate_n : rate n < ε / 7 := by
    exact Nat.find_spec (hrate (ε / 7) hε'_pos) n (le_max_left _ _)
  have h36k : (36 : ℝ) / δ ≤ ↑(n + 1) := by
    calc (36 : ℝ) / δ ≤ ↑(Nat.ceil (36 / δ)) := Nat.le_ceil _
      _ ≤ ↑kmin := by exact_mod_cast (by omega : Nat.ceil (36 / δ) ≤ kmin)
      _ ≤ ↑(n + 1) := by exact_mod_cast (by omega : kmin ≤ n + 1)
  -- Step 3b: Concentration instantiation
  have hevents_meas := goodBlockEvent_measurable L D c (hc_meas c hcC) rate (n + 1) n
  have hindep := iIndepSet_goodBlockEvents L D c (hc_meas c hcC) rate (n + 1) n
  have hprob := fun j => goodBlockEvent_prob_ge_two_thirds C L rate huniv D c hcC
    (hc_meas c hcC) (n + 1) n j
  have hconc := chebyshev_seven_twelfths_bound hδ h36k
    (goodBlockEvent L D c rate (n + 1) n) hevents_meas hindep hprob
  -- Step 3c: Rate bound
  have h7rate : 7 * max (rate n) 0 ≤ ε := by
    have : max (rate n) 0 ≤ ε / 7 := by
      rcases le_or_gt 0 (rate n) with h | h
      · simp [max_eq_left h]; linarith
      · rw [max_eq_right (le_of_lt h)]
        positivity
    linarith
  -- Step 3d: hlearn_unfold (P3c: congrArg ladder via boosted_majority cast)
  have hlearn_unfold : ∀ (ω : Fin ((n + 1) * n) → X) (x : X),
      L'.learn (fun i => (ω i, c (ω i))) x =
      boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (block_extract (n + 1) n ω j i,
                           c (block_extract (n + 1) n ω j i))) x) := by
    intro ω x
    simp only [L']
    have hblk_ne' : ¬ ((n + 1) * n / (((n + 1) * n).sqrt + 1) = 0) := hblk_ne
    rw [if_neg hblk_ne']
    have hsqrt' : ((n + 1) * n).sqrt + 1 = n + 1 := by rw [hsqrt]
    have hblk' : (n + 1) * n / (((n + 1) * n).sqrt + 1) = n := by rw [hsqrt]; exact hblk
    -- Prove by showing the boosted_majority applications are definitionally equal
    -- after casting the Fin types via the equalities hsqrt' and hblk'
    change boosted_majority _ _ = boosted_majority _ _
    -- Key: boosted_majority k f depends on k and Fin k.
    -- We show: boosted_majority k f = boosted_majority k' g when k = k' and f, g agree pointwise
    have hbm : ∀ {k k'} (hk : k = k') (f : Fin k → Bool) (g : Fin k' → Bool),
        (∀ j : Fin k, f j = g ⟨j, hk ▸ j.2⟩) → boosted_majority k f = boosted_majority k' g := by
      intros k k' hk f g hfg; subst hk; exact congrArg (boosted_majority k) (funext hfg)
    apply hbm hsqrt'
    intro j
    -- j : Fin(sqrt+1), need:
    --   L.learn (fun i:Fin(blk) => (ω ⟨j*blk+i, _⟩, c(...))) x
    -- = L.learn (fun i:Fin(n) => (block_extract (n+1) n ω ⟨j, _⟩ i, c(...))) x
    -- Use the same helper pattern for the inner Fin cast
    -- Apply the same pattern for the inner Fin type cast (Fin blk → Fin n)
    -- We need: L.learn S₁ x = L.learn S₂ x where S₁ : Fin(blk) → ... and S₂ : Fin(n) → ...
    -- Use a helper that casts the learn input
    have hlearn_cast : ∀ {m m'} (hm : m = m') (S : Fin m → X × Bool) (S' : Fin m' → X × Bool),
        (∀ i : Fin m, S i = S' ⟨i, hm ▸ i.2⟩) → L.learn S x = L.learn S' x := by
      intros m m' hm S S' hS; subst hm; exact congrArg (L.learn · x) (funext hS)
    apply hlearn_cast hblk'
    intro ⟨i, hi⟩
    simp only [block_extract, finProdFinEquiv, Equiv.coe_fn_mk, hblk']
    -- Goal: (ω ⟨j*n+i, _⟩, c (ω ⟨j*n+i, _⟩)) = (ω ⟨i+n*j, _⟩, c (ω ⟨i+n*j, _⟩))
    -- The Fin values have the same .val (j*n+i = i+n*j by ring)
    -- So the Fins are equal by proof irrelevance, and hence the pairs are equal
    simp only [show j.1 * n + i = i + n * j.1 from by ring]
  -- Step 3e: Error set equality
  have herr_set_eq : ∀ (ω : Fin ((n + 1) * n) → X),
      {x | L'.learn (fun i => (ω i, c (ω i))) x ≠ c x} =
      {x | boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (block_extract (n + 1) n ω j i,
                           c (block_extract (n + 1) n ω j i))) x) ≠ c x} := by
    intro ω; ext x; simp [hlearn_unfold ω x]
  -- Step 3f: Subset
  have hsub : {ω | 7 * (n + 1) ≤ 12 *
      (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate (n + 1) n j)).card} ⊆
      {xs | D {x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x} ≤ ENNReal.ofReal ε} := by
    intro ω hω
    rw [Set.mem_setOf_eq, herr_set_eq ω]
    have hbound := boosted_sample_error_le_of_good_blocks D c (hc_meas c hcC) L
      rate (n + 1) n ω (by omega) hω
    exact le_trans hbound (ENNReal.ofReal_le_ofReal h7rate)
  -- Step 3g: Final composition
  exact le_trans hconc (MeasureTheory.measure_mono hsub)

/-- Universal learnable → PAC learnable.
    Proof sketch: UniversalLearnable gives learner L with rate → 0 and Pr[error ≤ rate(m)] ≥ 2 / 3.
    Two components:
    1. Event containment: rate(m) < ε ⟹ {error ≤ rate(m)} ⊆ {error ≤ ε} (monotonicity).
    2. Confidence boosting: 2 / 3 → 1-δ via median-of-means
       implemented in boost_two_thirds_to_pac.
    Routes through boost_two_thirds_to_pac which encapsulates the Chernoff-based boosting. -/
theorem universal_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    [MeasurableHypotheses X C]
    (hL_meas : ∀ (L : BatchLearner X Bool), LearnEvalMeasurable L)
    (hul : UniversalLearnable X C) :
    PACLearnable X C := by
  have hc_meas : ∀ c ∈ C, Measurable c := MeasurableHypotheses.mem_measurable (C := C)
  obtain ⟨L, rate, hrate, huniv⟩ := hul
  haveI : MeasurableBatchLearner X L := ⟨hL_meas L⟩
  exact boost_two_thirds_to_pac X C L rate hrate huniv

-- PAC does not imply mistake-bounded.
-- Standard witness: X = ℕ, C = threshold functions {x ↦ (x ≤ n) | n : ℕ}.
-- VCDim = 1 (PAC-learnable), LittlestoneDim = ∞ (adversary binary-searches).
-- ============================================================
-- THRESHOLD CONCEPT CLASS ON ℕ
-- ============================================================

/-- Threshold concept class on ℕ: { (· ≤ n) | n : ℕ }.
    VCDim = 1 (PAC-learnable), LittlestoneDim = ∞ (not online-learnable). -/
private def thresholdClass : ConceptClass ℕ Bool :=
  { f | ∃ n : ℕ, f = fun x => decide (x ≤ n) }

-- ============================================================
-- PAC SIDE: VCDim(thresholdClass) ≤ 1 < ⊤
-- ============================================================

/-- Threshold functions are monotone: if x ≤ y and f(y) = true then f(x) = true. -/
private theorem threshold_monotone {n x y : ℕ} (hxy : x ≤ y)
    (hy : decide (y ≤ n) = true) : decide (x ≤ n) = true := by
  simp only [decide_eq_true_eq] at *; omega

/-- No 2-element subset of ℕ is shattered by the threshold class.
    Key: the labeling (smaller → false, larger → true) is impossible by monotonicity. -/
private theorem threshold_not_shatter_pair {S : Finset ℕ} (hcard : 2 ≤ S.card) :
    ¬ Shatters ℕ thresholdClass S := by
  intro hshat
  -- Extract two distinct elements from S
  have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  -- Threshold monotonicity: (· ≤ n) with n < a implies n < b for a < b
  -- So no threshold can map a ↦ false and b ↦ true when a < b
  -- (and symmetrically for b < a).
  -- We show: for EVERY concept c ∈ thresholdClass, if c(a) = false then c(b) = false
  -- (regardless of ordering of a,b — but we'll use that they're distinct)
  -- Actually, we need the SPECIFIC labeling where the smaller gets false.
  -- Since we don't know who's smaller, we use that threshold monotonicity gives:
  -- ∀ n, ∀ x y, x ≤ y → decide(y ≤ n) = true → decide(x ≤ n) = true
  -- Equivalently: decide(x ≤ n) = false → decide(y ≤ n) = false when x ≤ y
  -- So: labeling (a ↦ false, b ↦ true) impossible when a < b
  --     labeling (b ↦ false, a ↦ true) impossible when b < a
  -- Both impossible since a ≠ b. Pick whichever gives a contradiction.
  -- We prove: ∀ c = (· ≤ n), ¬(c a = false ∧ c b = true) ∧ ¬(c b = false ∧ c a = true)
  -- Then ANY labeling that distinguishes a and b is unrealizable. But shattering
  -- requires ALL labelings, so there's a labeling distinguishing a and b.
  -- Pick the labeling that assigns a ↦ false and b ↦ true:
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · -- a < b: labeling (a ↦ false, b ↦ true) is impossible for monotone thresholds
    obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s =>
      if (s : ℕ) = a then false else true)
    have h1 := hc ⟨a, ha⟩
    have h2 := hc ⟨b, hb⟩
    -- h1 : decide (a ≤ n) = if a = a then false else true
    -- h2 : decide (b ≤ n) = if b = a then false else true
    -- Manually reduce the if-then-else
    have : (⟨a, ha⟩ : ↥S).val = a := rfl
    have : (⟨b, hb⟩ : ↥S).val = b := rfl
    -- The coercion from ↥S to ℕ gives a (resp. b), so the condition is a = a (resp. b = a)
    have hca : decide (a ≤ n) = false := by
      convert h1 using 1; simp
    have hcb : decide (b ≤ n) = true := by
      convert h2 using 1
      simp only [show (b : ℕ) ≠ a from Ne.symm hab, ite_false]
    simp only [decide_eq_false_iff_not, not_le] at hca
    simp only [decide_eq_true_eq] at hcb
    omega
  · -- b < a: labeling (b ↦ false, a ↦ true) is impossible
    obtain ⟨c, ⟨n, rfl⟩, hc⟩ := hshat (fun s =>
      if (s : ℕ) = b then false else true)
    have hcb : decide (b ≤ n) = false := by
      convert hc ⟨b, hb⟩ using 1; simp
    have hca : decide (a ≤ n) = true := by
      convert hc ⟨a, ha⟩ using 1
      simp only [show (a : ℕ) ≠ b from hab, ite_false]
    simp only [decide_eq_false_iff_not, not_le] at hcb
    simp only [decide_eq_true_eq] at hca
    omega

/-- VCDim of threshold class on ℕ is finite (≤ 1). -/
private theorem vcdim_threshold_finite : VCDim ℕ thresholdClass < ⊤ := by
  -- Show VCDim ≤ 1 < ⊤
  apply lt_of_le_of_lt _ (WithTop.coe_lt_top (a := 1))
  -- VCDim = ⨆ S shattered, S.card. Need all shattered S to have card ≤ 1.
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard2 : 2 ≤ S.card := by
    exact_mod_cast hgt
  exact threshold_not_shatter_pair hcard2 hshat

-- ============================================================
-- ONLINE SIDE: LittlestoneDim(thresholdClass) = ⊤
-- ============================================================

/-- Build a shattered Littlestone tree of depth d for the threshold class
    restricted to thresholds in interval [lo, lo + 2^d - 1].
    The concept class parameter C should contain all thresholds (· ≤ n) for lo ≤ n ≤ lo + 2^d - 1.
    We show the tree is shattered by C when C ⊇ these thresholds. -/
private noncomputable def thresholdTree (lo : ℕ) : (d : ℕ) → LTree ℕ d
  | 0 => .leaf
  | d + 1 =>
    let mid := lo + 2 ^ d
    .branch mid (thresholdTree mid d) (thresholdTree lo d)

/-- The threshold tree is shattered by any concept class containing all thresholds
    with indices in [lo, lo + 2^d - 1]. -/
private theorem thresholdTree_shattered (lo : ℕ) (d : ℕ)
    (C : ConceptClass ℕ Bool)
    (hC : ∀ n, lo ≤ n → n < lo + 2 ^ d → (fun x => decide (x ≤ n)) ∈ C) :
    (thresholdTree lo d).isShattered C := by
  induction d generalizing lo C with
  | zero =>
    -- Depth 0: need C.Nonempty. lo ≤ lo < lo + 1 = lo + 2^0
    exact ⟨_, hC lo le_rfl (by simp)⟩
  | succ d ih =>
    simp only [thresholdTree, LTree.isShattered]
    set mid := lo + 2 ^ d with hmid_def
    have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    have hpow_succ : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ∃ c ∈ C, c mid = true: take threshold n = mid
      refine ⟨_, hC mid (Nat.le_add_right lo _) ?_, by simp⟩
      rw [hpow_succ]; omega
    · -- ∃ c ∈ C, c mid = false: take threshold n = mid - 1
      have hmid_pos : 0 < mid := by omega
      refine ⟨_, hC (mid - 1) (by omega) (by rw [hpow_succ]; omega), ?_⟩
      simp only [decide_eq_false_iff_not, not_le]; omega
    · -- Left subtree: thresholdTree mid d, shattered by {c ∈ C | c mid = true}
      apply ih mid {c ∈ C | c mid = true}
      intro n hn1 hn2
      constructor
      · exact hC n (by omega) (by rw [hpow_succ]; omega)
      · simp [decide_eq_true_eq]; omega
    · -- Right subtree: thresholdTree lo d, shattered by {c ∈ C | c mid = false}
      apply ih lo {c ∈ C | c mid = false}
      intro n hn1 hn2
      constructor
      · exact hC n hn1 (lt_of_lt_of_le hn2 (by rw [hpow_succ]; omega))
      · simp [decide_eq_false_iff_not, not_le]; omega

-- Show for all d, there's a shattered tree of depth d
private theorem threshold_shattered_all_depths :
    ∀ d : ℕ, ∃ T : LTree ℕ d, T.isShattered thresholdClass :=
  fun d => ⟨thresholdTree 0 d, thresholdTree_shattered 0 d thresholdClass
    (fun n _ _ => ⟨n, rfl⟩)⟩

/-- LittlestoneDim of threshold class = ⊤. -/
private theorem ldim_threshold_top : LittlestoneDim ℕ thresholdClass = ⊤ := by
  -- In WithBot (WithTop ℕ), ⊤ = ↑(⊤ : WithTop ℕ)
  -- Show: for all d, LittlestoneDim ≥ ↑↑d. Then LittlestoneDim = ⊤.
  by_contra hne
  push Not at hne
  have hlt : LittlestoneDim ℕ thresholdClass < ⊤ := lt_top_iff_ne_top.mpr hne
  -- Extract finite bound
  cases hc : LittlestoneDim ℕ thresholdClass with
  | bot =>
    -- ⊥ means empty class, but thresholdClass is nonempty
    have hne : thresholdClass.Nonempty := ⟨_, 0, rfl⟩
    have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑0 : WithTop ℕ) :=
      le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
    rw [hc] at hge; exact absurd hge (by simp)
  | coe v =>
    cases v with
    | top => rw [hc] at hlt; exact absurd hlt (lt_irrefl _)
    | coe n =>
      -- LittlestoneDim = ↑↑n, but we can shatter depth n+1
      have ⟨T, hT⟩ := threshold_shattered_all_depths (n + 1)
      have hge : LittlestoneDim ℕ thresholdClass ≥ ↑(↑(n + 1) : WithTop ℕ) :=
        le_iSup₂_of_le (n + 1) ⟨T, hT⟩ le_rfl
      rw [hc] at hge
      exact absurd hge (by
        simp only [WithBot.coe_le_coe]
        exact not_le.mpr (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)))

theorem pac_not_implies_online :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C := by
  refine ⟨ℕ, ⊤, thresholdClass, ?_, ?_⟩
  · -- PAC learnable: VCDim < ⊤ → PACLearnable (via UC route)
    have hWB : @WellBehavedVC ℕ ⊤ thresholdClass := by
      intro D _ c m ε
      -- Pi of ⊤ over Fin m → ℕ is ⊤ because Fin m → ℕ is countable and
      -- singletons are finite intersections of cylinders.
      have hpi_eq_top : @MeasurableSpace.pi (Fin m) (fun _ => ℕ) (fun _ => ⊤) = ⊤ := by
        apply le_antisymm le_top
        intro s _
        have hs_union : s = ⋃ f ∈ s, {f} := by ext f; simp
        rw [hs_union]
        apply MeasurableSet.biUnion (Set.to_countable s)
        intro f _
        have hf_inter : ({f} : Set (Fin m → ℕ)) = ⋂ i : Fin m, (fun g => g i) ⁻¹' {f i} := by
          ext g; simp [funext_iff]
        rw [hf_inter]
        exact MeasurableSet.iInter (fun i =>
          measurable_pi_apply i (MeasurableSpace.measurableSet_top))
      -- In pi of ⊤, singletons are measurable. Since Fin m → ℕ is countable,
      -- pi = ⊤. For the product, singletons {(a,b)} are measurable via
      -- MeasurableSet.prod, so the product sigma-algebra is also ⊤.
      -- We use the singleton argument on the product directly.
      have hmeas_singleton_pi : ∀ (f : Fin m → ℕ),
          @MeasurableSet _ (@MeasurableSpace.pi (Fin m) (fun _ => ℕ) (fun _ => ⊤)) {f} := by
        intro f
        have : ({f} : Set (Fin m → ℕ)) = ⋂ i : Fin m, (fun g => g i) ⁻¹' {f i} := by
          ext g; simp [funext_iff]
        rw [this]
        exact MeasurableSet.iInter (fun i =>
          measurable_pi_apply i (MeasurableSpace.measurableSet_top))
      have hprod_top : (inferInstance : MeasurableSpace ((Fin m → ℕ) × (Fin m → ℕ))) = ⊤ := by
        apply le_antisymm le_top
        intro s _
        have hs_union : s = ⋃ p ∈ s, {p} := by ext p; simp
        rw [hs_union]
        apply MeasurableSet.biUnion (Set.to_countable s)
        intro ⟨a, b⟩ _
        have : ({(a, b)} : Set ((Fin m → ℕ) × (Fin m → ℕ))) = {a} ×ˢ {b} := by
          ext ⟨x, y⟩; simp [Prod.mk.injEq]
        rw [this]
        exact (hmeas_singleton_pi a).prod (hmeas_singleton_pi b)
      have hmeas_all : ∀ s : Set ((Fin m → ℕ) × (Fin m → ℕ)),
          @MeasurableSet _ (inferInstance : MeasurableSpace ((Fin m → ℕ) × (Fin m → ℕ))) s := by
        intro s; rw [hprod_top]; exact MeasurableSpace.measurableSet_top
      exact (hmeas_all _).nullMeasurableSet
    exact vcdim_finite_imp_pac_via_uc' ℕ thresholdClass vcdim_threshold_finite
      (fun _ _ _ _ => MeasurableSpace.measurableSet_top)
      (fun _ _ _ => MeasurableSpace.measurableSet_top)
      hWB
  · -- ¬ OnlineLearnable: LittlestoneDim = ⊤ → ¬ OnlineLearnable
    intro hol
    have hfin := forward_direction ℕ thresholdClass hol
    rw [ldim_threshold_top] at hfin
    exact lt_irrefl _ hfin

/-- EX does not imply PAC.
    Witness: X = ℕ, C = all indicator functions of finite subsets of ℕ.
    EX-learnable: learner outputs "true on everything seen so far" — converges on any text.
    Not PAC-learnable: VCDim = ⊤ (every finite set is shattered). -/
theorem ex_not_implies_pac :
    ∃ (X : Type) (_ : Countable X) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      EXLearnable X C ∧ ¬ PACLearnable X C := by
  -- Witness: X = ℕ, measurable space = ⊤, C = indicator functions of finite subsets
  refine ⟨ℕ, inferInstance, ⊤, { f : ℕ → Bool | Set.Finite { n | f n = true } }, ?_, ?_⟩
  · -- EXLearnable: construct a Gold learner that outputs "true on seen elements"
    refine ⟨⟨fun data => fun x => data.any (fun p => decide (p.1 = x))⟩, ?_⟩
    intro c hcC T
    have hfin : Set.Finite { n : ℕ | c n = true } := hcC
    -- Helper: c x ≠ true implies x never appears in T (by T.correct)
    have never_seen : ∀ x, c x ≠ true → ∀ t, (T.toDataStream.observe t).1 ≠ x := by
      intro x hcx t heq
      exact hcx (heq ▸ T.correct t)
    -- Convergence lemma: for each x, the learner eventually gets x right.
    -- For x in support: T.exhaustive guarantees x appears, then learner sees it.
    -- For x not in support: T.correct ensures x never appears, so learner never claims it.
    -- Since the support is finite, take the max appearance time.
    -- Use Finset.sup on the support to get t₀.
    -- But tmap has dependent type (x ∈ hfin.toFinset), so we project to a total function.
    have hsup : ∀ x ∈ hfin.toFinset, ∃ t, (T.toDataStream.observe t).1 = x := by
      intro x hx; exact T.exhaustive x (hfin.mem_toFinset.mp hx)
    choose tmap htmap using hsup
    -- Build a total function for Finset.sup
    let tmap' : ℕ → ℕ := fun x => if h : x ∈ hfin.toFinset then tmap x h else 0
    refine ⟨hfin.toFinset.sup tmap', fun t ht => ?_⟩
    funext x
    simp only [dataUpTo]
    cases hcxb : c x with
    | true =>
      -- x is in the support, appeared at time tmap x hxfin ≤ t₀ ≤ t
      have hxfin : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hcxb
      have htmap'_eq : tmap' x = tmap x hxfin := dif_pos hxfin
      have htx_le : tmap x hxfin ≤ t := by
        calc tmap x hxfin = tmap' x := htmap'_eq.symm
          _ ≤ hfin.toFinset.sup tmap' := Finset.le_sup hxfin
          _ ≤ t := ht
      -- (T.observe (tmap x hxfin)).1 = x, and tmap x hxfin ≤ t
      -- So ∃ i ∈ range(t+1), (T.observe i).1 = x
      -- Learner returns true for x
      change (((List.range (t + 1)).map T.toDataStream.observe).any
        (fun p => decide (p.1 = x))) = true
      rw [List.any_map, List.any_eq_true]
      exact ⟨tmap x hxfin,
        List.mem_range.mpr (Nat.lt_succ_of_le htx_le),
        by simp [htmap x hxfin]⟩
    | false =>
      -- x not in support, never appears in T
      simp only [List.any_map, Bool.not_eq_true, List.any_eq_false,
        List.mem_range, Function.comp_def]
      intro i _
      simp only [decide_eq_false_iff_not]
      exact fun h => never_seen x (by simp [hcxb]) i h
  · -- ¬PACLearnable: VCDim = ⊤, then apply vcdim_infinite_not_pac
    apply vcdim_infinite_not_pac
    -- Show VCDim ℕ C = ⊤ where C = { f | Set.Finite { n | f n = true } }
    -- Strategy: for any n, Finset.range n is shattered by C, so VCDim ≥ n for all n
    rw [VCDim, iSup₂_eq_top]
    intro b hb
    obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hb)
    refine ⟨Finset.range (n + 1), ?_, ?_⟩
    · -- Shatters: every labeling of Finset.range (n+1) is realized by some c ∈ C
      intro f
      refine ⟨fun x => if h : x ∈ Finset.range (n + 1) then f ⟨x, h⟩ else false, ?_, ?_⟩
      · -- c ∈ C: { x | c x = true } is finite (subset of Finset.range (n+1))
        change Set.Finite { x | (if h : x ∈ Finset.range (n + 1) then f ⟨x, h⟩ else false) = true }
        apply Set.Finite.subset (Finset.range (n + 1)).finite_toSet
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [Finset.mem_coe]
        by_contra hx'
        simp [hx'] at hx
      · -- ∀ x : ↥S, c x = f x
        intro ⟨x, hx⟩
        simp [hx]
    · -- n < (Finset.range (n+1)).card as WithTop ℕ
      simp only [Finset.card_range]
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)

/-- Online learning is strictly stronger than PAC learning. -/
theorem online_strictly_stronger_pac :
    (∀ (X : Type) [MeasurableSpace X] (C : ConceptClass X Bool)
      [MeasurableConceptClass X C],
      OnlineLearnable X Bool C → PACLearnable X C) ∧
    (∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C) :=
  -- Factored: conjunct 1 = online_imp_pac (Generalization.lean)
  --           conjunct 2 = pac_not_implies_online.
  ⟨fun X _ C _ hol => online_imp_pac X C hol, pac_not_implies_online⟩

/-- EX learning is strictly stronger than finite learning. -/
theorem ex_strictly_stronger_finite :
    ∀ (X : Type u) (C : ConceptClass X Bool),
      FiniteLearnable X C → EXLearnable X C := by
  intro X C ⟨L, hL⟩
  exact ⟨L, fun c hcC T => by
    obtain ⟨t₀, ht₀⟩ := hL c hcC T
    exact ⟨t₀, fun t ht => (ht₀ t ht).1⟩⟩

/-- Online-PAC-Gold three-way separation.
    Pl-REPAIR: first conjunct had [Fintype X] which made it false.
    Fixed to match pac_not_implies_online repair. -/
theorem online_pac_gold_separation :
    (∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C) ∧
    (∃ (X : Type) (_ : Countable X) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      EXLearnable X C ∧ ¬ PACLearnable X C) := by
  exact ⟨pac_not_implies_online, ex_not_implies_pac⟩
