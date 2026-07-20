/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Interpolation

/-!
# Amalgamation Preserves WellBehavedVCMeasTarget

Given two Borel-parameterized concept families e₁ : Θ₁ → Concept X Bool and
e₂ : Θ₂ → Concept X Bool, with projection maps π₁ : Θ₁ → S and π₂ : Θ₂ → S
into a common StandardBorelSpace S, the **amalgamation class**  -  the set of
concepts merge(θ₁, θ₂) for (θ₁, θ₂) satisfying π₁ θ₁ = π₂ θ₂  -  satisfies
`WellBehavedVCMeasTarget`.

The proof proceeds by:
1. Showing the agreement relation {(θ₁, θ₂) | π₁ θ₁ = π₂ θ₂} is MeasurableSet
   (via `measurableSet_eq_fun` + `upgradeStandardBorel`)
2. Taking the StandardBorelSpace subtype (via `MeasurableSet.standardBorel`)
3. Reducing to `borel_param_wellBehavedVCMeasTarget` on the subtype

## Main results

- `measurableSet_agreementRel`: the agreement fiber product is MeasurableSet
- `amalgClass_wellBehaved`: amalgamation preserves WellBehavedVCMeasTarget
- `interpClassFixed_subset_amalgClass`: fixed-region interpolation embeds in amalgamation

## References

- BorelAnalyticBridge.lean (bridge theorem)
- Interpolation.lean (piecewise concepts, interpClassFixed)
-/

universe u

open MeasureTheory

/-! ## Definitions -/

/-- The agreement relation: pairs (θ₁, θ₂) where π₁ θ₁ = π₂ θ₂. -/
def agreementRel {Θ₁ Θ₂ S : Type*}
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S) : Set (Θ₁ × Θ₂) :=
  {p | π₁ p.1 = π₂ p.2}

/-- Parameterized sub-class: concepts e(θ) for θ restricted to a subset R. -/
def relParamClass {X : Type u}
    {Θ : Type*} (R : Set Θ) (e : Θ → Concept X Bool) : ConceptClass X Bool :=
  {h | ∃ θ ∈ R, h = e θ}

/-- The amalgamation class: merge(θ₁, θ₂) for (θ₁, θ₂) in the agreement fiber. -/
def amalgClass {X : Type u}
    {Θ₁ Θ₂ S : Type*}
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (merge : Θ₁ × Θ₂ → Concept X Bool) : ConceptClass X Bool :=
  relParamClass (agreementRel π₁ π₂) merge

/-! ## Agreement relation is MeasurableSet -/

/-- The agreement relation is MeasurableSet when projections are measurable
    and the codomain is StandardBorelSpace. -/
theorem measurableSet_agreementRel
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂) :
    MeasurableSet (agreementRel π₁ π₂) := by
  unfold agreementRel
  letI := upgradeStandardBorel S
  exact measurableSet_eq_fun (hπ₁.comp measurable_fst) (hπ₂.comp measurable_snd)

/-! ## Amalgamation preserves WellBehavedVCMeasTarget -/

/-- The amalgamation class satisfies WellBehavedVCMeasTarget when all
    parameter spaces are StandardBorelSpace and merge is jointly measurable. -/
theorem amalgClass_wellBehaved
    {X : Type u}
    [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂)
    (merge : Θ₁ × Θ₂ → Concept X Bool)
    (hmerge : Measurable (fun p : (Θ₁ × Θ₂) × X => merge p.1 p.2)) :
    WellBehavedVCMeasTarget X (amalgClass π₁ π₂ merge) := by
  have hmeas := measurableSet_agreementRel π₁ π₂ hπ₁ hπ₂
  haveI := hmeas.standardBorel
  have hrange : amalgClass π₁ π₂ merge =
      Set.range (fun θ : ↥(agreementRel π₁ π₂) => merge θ.val) := by
    ext h
    simp only [amalgClass, relParamClass, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨θ, hθ, rfl⟩; exact ⟨⟨θ, hθ⟩, rfl⟩
    · rintro ⟨⟨θ, hθ⟩, rfl⟩; exact ⟨θ, hθ, rfl⟩
  have he : Measurable (fun p : ↥(agreementRel π₁ π₂) × X =>
      (fun θ : ↥(agreementRel π₁ π₂) => merge θ.val) p.1 p.2) :=
    hmerge.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  rw [hrange]
  exact borel_param_wellBehavedVCMeasTarget _ he

/-! ## Fixed-region interpolation embeds in amalgamation -/

/-- Fixed-region interpolation is a subset of amalgamation with trivial projections. -/
theorem interpClassFixed_subset_amalgClass
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A ⊆
      amalgClass (fun _ : Θ₁ => ()) (fun _ : Θ₂ => ())
        (fun p => piecewiseConcept A (e₁ p.1) (e₂ p.2)) := by
  intro h hh
  simp only [interpClassFixed, Set.mem_setOf_eq] at hh
  obtain ⟨h₁, ⟨θ₁, rfl⟩, h₂, ⟨θ₂, rfl⟩, rfl⟩ := hh
  simp only [amalgClass, relParamClass, agreementRel, Set.mem_setOf_eq]
  exact ⟨(θ₁, θ₂), trivial, rfl⟩
