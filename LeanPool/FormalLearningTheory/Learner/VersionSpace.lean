/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Core

/-!
# Version Space Learner: Measurable Selection via Countable Enumeration

A version space learner outputs the first hypothesis (in a fixed enumeration)
consistent with the training data. For concept classes with a measurable
enumeration `enum : ℕ → Concept X Bool`, `Nat.find` provides a constructive
measurable selector.

## Main Result

`versionSpaceLearner_measurableBatchLearner`: the version space learner
satisfies `MeasurableBatchLearner`  -  it is a valid RL policy class.

## Proof Architecture

For Y = Bool, the preimage of each singleton under the evaluation map
decomposes as a countable union of measurable rectangles:

  {(S, x) | learn S x = true} = ⋃ n, ({S | firstConsistent = n} ×ˢ {x | enum n x = true})

Measurability follows from `measurable_to_countable'` (Mathlib).

## References

- Mitchell (1982): version spaces in computational learning theory
- Kuratowski-Ryll-Nardzewski: measurable selection (NOT in Mathlib  -  motivates
  the countable restriction)
-/

universe u

open MeasureTheory Set

/-! ## Definitions -/

/-- Consistency: hypothesis h predicts correctly on every example in sample S. -/
def IsSampleConsistent {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) : Prop :=
  ∀ i, h (S i).1 = (S i).2

/-- Decidability of consistency (finite conjunction of Bool equality). -/
instance isSampleConsistentDecidable
    {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) :
    Decidable (IsSampleConsistent h S) :=
  Fintype.decidableForallFintype

/-- The "first consistent index is n" predicate, stated without Nat.find.
    This is the measurability-friendly version: no proof-term dependence. -/
def IsFirstConsistent {X : Type u} (enum : ℕ → Concept X Bool)
    {m : ℕ} (S : Fin m → X × Bool) (n : ℕ) : Prop :=
  IsSampleConsistent (enum n) S ∧ ∀ k, k < n → ¬ IsSampleConsistent (enum k) S

/-- Version space learner: select the first consistent hypothesis in the enumeration.
    Falls back to the zero concept (always false) if no hypothesis is consistent. -/
noncomputable def versionSpaceLearner
    {X : Type u}
    (enum : ℕ → Concept X Bool) : BatchLearner X Bool where
  hypotheses := range enum ∪ {fun _ => false}
  learn S := by
    classical
    exact if h : ∃ n, IsSampleConsistent (enum n) S
      then enum (Nat.find h)
      else fun _ => false
  output_in_H S := by
    classical
    change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
          else fun _ => false) ∈ range enum ∪ {fun _ => false}
    by_cases h : ∃ n, IsSampleConsistent (enum n) S
    · rw [dif_pos h]; exact Or.inl ⟨Nat.find h, rfl⟩
    · rw [dif_neg h]; exact Or.inr rfl

/-! ## Measurability Infrastructure -/

/-- Each "enum n is consistent with S" event is measurable in S. -/
theorem measurableSet_isConsistent
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsSampleConsistent (enum n) S} := by
  unfold IsSampleConsistent
  have : {S : Fin m → X × Bool | ∀ i, enum n (S i).1 = (S i).2}
      = ⋂ i, {S | enum n (S i).1 = (S i).2} := by
    ext S; simp [mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun i => measurableSet_eq_fun ?_ (measurable_pi_apply i).snd
  exact (h_meas n).comp (measurable_pi_apply i).fst

/-- The "first consistent index is n" event is measurable. -/
theorem measurableSet_isFirstConsistent
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsFirstConsistent enum S n} := by
  unfold IsFirstConsistent
  have : {S : Fin m → X × Bool |
      IsSampleConsistent (enum n) S ∧ ∀ k, k < n → ¬IsSampleConsistent (enum k) S}
      = {S | IsSampleConsistent (enum n) S} ∩
        (⋂ k, ⋂ (_ : k < n), {S | IsSampleConsistent (enum k) S}ᶜ) := by
    ext S; simp [mem_inter_iff, mem_iInter, mem_compl_iff, mem_setOf_eq]
  rw [this]
  refine (measurableSet_isConsistent enum h_meas m n).inter ?_
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    (measurableSet_isConsistent enum h_meas m k).compl

/-- Bridge: `Nat.find h = n ↔ IsFirstConsistent`. -/
theorem nat_find_eq_iff_isFirstConsistent
    {X : Type u} (enum : ℕ → Concept X Bool)
    {m : ℕ} (S : Fin m → X × Bool)
    (h : ∃ n, IsSampleConsistent (enum n) S) (n : ℕ) :
    Nat.find h = n ↔ IsFirstConsistent enum S n := by
  simp only [IsFirstConsistent, Nat.find_eq_iff]

/-- The preimage of {true} under the evaluation map is measurable.
    Core lemma: decompose as countable union of measurable rectangles. -/
theorem measurableSet_versionSpace_true
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) :
    MeasurableSet ((fun p : (Fin m → X × Bool) × X =>
      (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true}) := by
  classical
  -- Rewrite as countable union of rectangles
  have key : (fun p : (Fin m → X × Bool) × X =>
      (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true}
      = ⋃ n, ({S : Fin m → X × Bool | IsFirstConsistent enum S n} ×ˢ
               {x : X | enum n x = true}) := by
    ext ⟨S, x⟩
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_prod, mem_setOf_eq]
    constructor
    · intro hlearn
      show ∃ i, IsFirstConsistent enum S i ∧ enum i x = true
      change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
            else fun _ => false) x = true at hlearn
      by_cases hex : ∃ n, IsSampleConsistent (enum n) S
      · simp only [dif_pos hex] at hlearn
        exact ⟨Nat.find hex, (nat_find_eq_iff_isFirstConsistent enum S hex _).mp rfl, hlearn⟩
      · rw [dif_neg hex] at hlearn; simp at hlearn
    · rintro ⟨n, hfirst, henum⟩
      change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
            else fun _ => false) x = true
      have hex : ∃ k, IsSampleConsistent (enum k) S := ⟨n, hfirst.1⟩
      simp only [dif_pos hex]
      have heq : Nat.find hex = n :=
        (nat_find_eq_iff_isFirstConsistent enum S hex n).mpr hfirst
      rw [heq]; exact henum
  rw [key]
  exact .iUnion fun n =>
    (measurableSet_isFirstConsistent enum h_meas m n).prod
      ((h_meas n) (measurableSet_singleton true))

/-! ## Main Theorem -/

/-- **Version space learners are MeasurableBatchLearners.**

    For any measurable enumeration of concepts, the learner that selects
    the first consistent hypothesis satisfies joint measurability.
    This makes version space learners valid RL policy classes.

    Proof: `measurable_to_countable'` reduces to showing each singleton
    preimage is MeasurableSet. For `{true}`, decompose as ⋃ₙ (Aₙ ×ˢ Bₙ).
    For `{false}`, take the complement. -/
theorem versionSpaceLearner_measurableBatchLearner
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n)) :
    MeasurableBatchLearner X (versionSpaceLearner enum) := by
  constructor
  intro m
  apply measurable_to_countable'
  intro b
  rcases b with _ | _
  · -- b = false: complement of the true preimage
    have : (fun p : (Fin m → X × Bool) × X =>
        (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {false}
        = ((fun p : (Fin m → X × Bool) × X =>
          (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true})ᶜ := by
      ext ⟨S, x⟩
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff]
      cases (versionSpaceLearner enum).learn S x <;> simp
    rw [this]
    exact (measurableSet_versionSpace_true enum h_meas m).compl
  · -- b = true: countable union of measurable rectangles
    exact measurableSet_versionSpace_true enum h_meas m
