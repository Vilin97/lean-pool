/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.BorelAnalyticBridge

/-!
# Interpolation of Concept Classes — Measurability Descent

If C₁ and C₂ are concept classes with Borel parameterizations
(StandardBorelSpace parameter spaces, jointly measurable evaluation maps),
their **interpolation** — the class of piecewise concepts agreeing with
h₁ ∈ C₁ on region A and h₂ ∈ C₂ on Aᶜ — satisfies
`WellBehavedVCMeasTarget` (NullMeasurableSet bad events).

The interpolated class may NOT preserve `KrappWirthWellBehaved`
(Borel-measurable ghost gap maps). Measurability can only descend,
not stay at the Borel level.

## Main results

- `interpClassFixed_wellBehaved`: fixed-region interpolation is well-behaved
- `interpClassCountable_wellBehaved`: countable-family interpolation is well-behaved
- `interpClass_wellBehaved_of_routerCode`: conditional interpolation (BorelRouterCode)
- `not_KrappWirth_of_nonBorel_badEvent`: descent — Borel level can fail

## References

- Krapp & Wirth (2024, arXiv:2410.10243)
- BorelAnalyticBridge.lean (this kernel)
-/

universe u

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-! ## Definitions -/

/-- Piecewise concept: agrees with h₁ on A, with h₂ on Aᶜ. -/
noncomputable def piecewiseConcept {X : Type u} [MeasurableSpace X]
    (A : Set X) (h₁ h₂ : Concept X Bool) : Concept X Bool :=
  fun x => if x ∈ A then h₁ x else h₂ x

/-- Router from a single fixed set: maps Unit × X → Bool. -/
noncomputable def routerOfSet {X : Type u} [MeasurableSpace X]
    (A : Set X) : Unit → Concept X Bool :=
  fun _ x => if x ∈ A then true else false

/-- Router from a countable family of sets: maps ℕ × X → Bool. -/
noncomputable def routerOfSetFamily {X : Type u} [MeasurableSpace X]
    (A : ℕ → Set X) : ℕ → Concept X Bool :=
  fun n x => if x ∈ A n then true else false

/-! ## Concept Class Definitions -/

/-- Interpolation with a fixed region A. -/
def interpClassFixed {X : Type u} [MeasurableSpace X]
    (C₁ C₂ : ConceptClass X Bool) (A : Set X) : ConceptClass X Bool :=
  {h | ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂, h = piecewiseConcept A h₁ h₂}

/-- Interpolation with a countable family of regions. -/
def interpClassCountable {X : Type u} [MeasurableSpace X]
    (C₁ C₂ : ConceptClass X Bool) (A : ℕ → Set X) : ConceptClass X Bool :=
  {h | ∃ n, ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂, h = piecewiseConcept (A n) h₁ h₂}

/-- Full interpolation: existential over arbitrary measurable regions. -/
def interpClass {X : Type u} [MeasurableSpace X]
    (C₁ C₂ : ConceptClass X Bool) : ConceptClass X Bool :=
  {h | ∃ A : Set X, MeasurableSet A ∧ ∃ h₁ ∈ C₁, ∃ h₂ ∈ C₂,
    h = piecewiseConcept A h₁ h₂}

/-! ## Router Measurability -/

/-- The router for a fixed measurable set is jointly measurable. -/
theorem routerOfSet_measurable {X : Type u} [MeasurableSpace X]
    {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun p : Unit × X => routerOfSet A p.1 p.2) := by
  simp only [routerOfSet]
  exact Measurable.piecewise (measurable_snd hA) measurable_const measurable_const

/-- The router for a countable measurable family is jointly measurable. -/
theorem routerOfSetFamily_measurable {X : Type u} [MeasurableSpace X]
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    Measurable (fun p : ℕ × X => routerOfSetFamily A p.1 p.2) := by
  simp only [routerOfSetFamily]
  have hS : MeasurableSet {p : ℕ × X | p.2 ∈ A p.1} := by
    have : {p : ℕ × X | p.2 ∈ A p.1} = ⋃ n, {n} ×ˢ A n := by
      ext ⟨n, x⟩
      simp [Set.mem_iUnion, Set.mem_prod]
    rw [this]
    exact MeasurableSet.iUnion (fun n => (measurableSet_singleton n).prod (hA n))
  exact Measurable.piecewise hS measurable_const measurable_const

/-! ## Set-Equality Bridges -/

/-- interpClassFixed equals the range of patchEval with routerOfSet. -/
theorem interpClassFixed_eq_range_patchEval
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSet A)) := by
  ext h
  simp only [interpClassFixed, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨θ₁, rfl⟩, _, ⟨θ₂, rfl⟩, rfl⟩
    refine ⟨(θ₁, θ₂, ()), funext fun x => ?_⟩
    simp only [patchEval, routerOfSet, piecewiseConcept]
    split <;> simp_all
  · rintro ⟨⟨θ₁, θ₂, _⟩, rfl⟩
    refine ⟨e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, funext fun x => ?_⟩
    simp only [patchEval, routerOfSet, piecewiseConcept]
    split <;> simp_all

/-- interpClassCountable equals the range of patchEval with routerOfSetFamily. -/
theorem interpClassCountable_eq_range_patchEval
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : ℕ → Set X) :
    interpClassCountable (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSetFamily A)) := by
  ext h
  simp only [interpClassCountable, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨n, _, ⟨θ₁, rfl⟩, _, ⟨θ₂, rfl⟩, rfl⟩
    refine ⟨(θ₁, θ₂, n), funext fun x => ?_⟩
    simp only [patchEval, routerOfSetFamily, piecewiseConcept]
    split <;> simp_all
  · rintro ⟨⟨θ₁, θ₂, n⟩, rfl⟩
    refine ⟨n, e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, funext fun x => ?_⟩
    simp only [patchEval, routerOfSetFamily, piecewiseConcept]
    split <;> simp_all

/-! ## WellBehaved Theorems -/

/-- Fixed-region interpolation of Borel-parameterized classes is well-behaved. -/
theorem interpClassFixed_wellBehaved
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    {A : Set X} (hA : MeasurableSet A) :
    WellBehavedVCMeasTarget X (interpClassFixed (Set.range e₁) (Set.range e₂) A) := by
  rw [interpClassFixed_eq_range_patchEval]
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ _ he₁ he₂ (routerOfSet_measurable hA)

/-- Countable-family interpolation of Borel-parameterized classes is well-behaved. -/
theorem interpClassCountable_wellBehaved
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    WellBehavedVCMeasTarget X (interpClassCountable (Set.range e₁) (Set.range e₂) A) := by
  rw [interpClassCountable_eq_range_patchEval]
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ _ he₁ he₂
    (routerOfSetFamily_measurable hA)

/-! ## Measurability Descent -/

/-- If the one-sided ghost gap bad event is NOT MeasurableSet,
    then KrappWirthWellBehaved fails. Measurability can only descend. -/
theorem not_KrappWirth_of_nonBorel_badEvent
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ)
    (hC : C.Nonempty)
    (hbad : ¬ MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      oneSidedGhostGap h c m p ≥ ε / 2}) :
    ¬ KrappWirthWellBehaved X C := by
  intro hKW
  apply hbad
  have hV := hKW.V_measurable c m
  rw [wellBehaved_event_eq_preimage_gapSup C c m ε hC]
  exact hV measurableSet_Ici

/-! ## BorelRouterCode: Conditional Interpolation -/

/-- A Borel router code: a StandardBorelSpace parameter space Ρ with a
    jointly measurable evaluation map eval : Ρ × X → Bool.
    This encodes the ability to select regions via a Borel-parameterized family. -/
structure BorelRouterCode (X : Type u) [MeasurableSpace X] where
  /-- The router parameter space -/
  Ρ : Type u
  /-- MeasurableSpace instance on Ρ -/
  instMeasΡ : MeasurableSpace Ρ
  /-- StandardBorelSpace instance on Ρ -/
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  /-- The router evaluation map -/
  eval : Ρ → Concept X Bool
  /-- Joint measurability of the evaluation map -/
  eval_meas : @Measurable (Ρ × X) Bool (instMeasΡ.prod ‹MeasurableSpace X›)
    (⊤ : MeasurableSpace Bool) (fun p => eval p.1 p.2)

/-- The range of patchEval with a BorelRouterCode is contained in interpClass. -/
theorem range_patchEval_sub_interpClass
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (R : BorelRouterCode X) :
    Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval) ⊆
      interpClass (Set.range e₁) (Set.range e₂) := by
  rintro h ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
  simp only [interpClass, Set.mem_setOf_eq]
  refine ⟨{x | R.eval ρ x = true}, ?_, e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, ?_⟩
  · -- MeasurableSet {x | R.eval ρ x = true}
    letI := R.instMeasΡ
    have hm : Measurable (fun x => R.eval ρ x) :=
      R.eval_meas.comp (Measurable.prodMk measurable_const measurable_id)
    exact hm (measurableSet_singleton true)
  · -- patchEval = piecewiseConcept
    funext x
    simp only [patchEval, piecewiseConcept, Set.mem_setOf_eq]
    split <;> rfl

/-- Conditional interpolation via BorelRouterCode is well-behaved:
    the range of patchEval with a Borel router satisfies WellBehavedVCMeasTarget. -/
theorem interpClass_wellBehaved_of_routerCode
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (R : BorelRouterCode X) :
    WellBehavedVCMeasTarget X
      (Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval)) := by
  letI := R.instMeasΡ
  letI := R.instStdΡ
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ R.eval he₁ he₂ R.eval_meas

/-! ## Open Question Definition -/

/-- Whether there exists a BorelRouterCode for X — i.e., whether every measurable
    region can be encoded by a Borel-parameterized router. -/
def HasFullInterpolationRouterCode (X : Type u) [MeasurableSpace X] : Prop :=
  Nonempty (BorelRouterCode X)

attribute [nolint unusedArguments]
  piecewiseConcept
  routerOfSet
  routerOfSetFamily
