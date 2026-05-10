/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Measurability
import LeanPool.FormalLearningTheory.PureMath.AnalyticMeasurability

/-!
# Borel-Analytic Bridge for Statistical Learning Theory

This file proves that NullMeasurableSet is the exactly right level of measurability
for the Fundamental Theorem of Statistical Learning with Borel-parameterized
concept classes over Polish spaces.

## Main results

- `paramWitnessSet_measurable`: the witness graph {(θ, p) | gap(θ, p) ≥ ε/2} is Borel
- `borel_param_badEvent_analytic`: projection to sample space is analytic (Σ₁¹)
- `analyticSet_nullMeasurableSet`: analytic → NullMeasurableSet (DST bridge lemma)
- `borel_param_wellBehavedVCMeasTarget`: Borel parameterization → WellBehavedVCMeasTarget

## The separation

The counterexample (singleton class over analytic non-Borel A ⊆ ℝ) shows the
bad event can be analytic but NOT Borel, hence WellBehavedVCMeasTarget holds
but KrappWirthWellBehaved fails. See Theorem/BorelAnalyticSeparation.lean.

## References

- Suslin (1917): projections of Borel sets are analytic
- Lusin (1925): analytic sets are universally measurable
- Krapp & Wirth (2024, arXiv:2410.10243): MeasurableSet conditions for FTSL
- This kernel: NullMeasurableSet weakening discovered during Lean4 formalization
-/

universe u

open MeasureTheory

/-! ## Core Definitions -/

/-- Ghost sample pairs: two independent samples of size m. -/
abbrev GhostPairs (X : Type u) (m : ℕ) := (Fin m → X) × (Fin m → X)

/-- The witness set in parameter × sample space:
    {(θ, p) | EmpErr(h_θ, ghost, c) - EmpErr(h_θ, train, c) ≥ ε/2}.
    This is Borel when e and c are measurable (Theorem A). -/
def paramWitnessSet
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (Θ × GhostPairs X m) :=
  {q | EmpiricalError X Bool (e q.1) (fun i => (q.2.2 i, c (q.2.2 i))) (zeroOneLoss Bool) -
       EmpiricalError X Bool (e q.1) (fun i => (q.2.1 i, c (q.2.1 i))) (zeroOneLoss Bool) ≥ ε / 2}

/-- The bad event in sample space: projection of the witness set.
    Existential over the parameter: {p | ∃ θ, gap(θ, p) ≥ ε/2}.
    This is analytic when the witness set is Borel (Theorem B). -/
def paramBadEvent
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (GhostPairs X m) :=
  Prod.snd '' paramWitnessSet e c m ε

/-- Patched evaluation: combine two concept families using a region selector.
    patchEval(θ₁, θ₂, ρ)(x) = e₁(θ₁)(x) if r(ρ)(x), else e₂(θ₂)(x).
    Used for the closure principle (Theorem F). -/
def patchEval
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) :
    (Θ₁ × Θ₂ × Ρ) → Concept X Bool :=
  fun θ x => if r θ.2.2 x then e₁ θ.1 x else e₂ θ.2.1 x

/-! ## Theorem A: Measurable witness graph -/

/-- The witness set {(θ, p) | ghost-gap ≥ ε/2} is MeasurableSet
    when the evaluation map e and target c are measurable.
    This is the Borel half of the Borel-analytic bridge. -/
theorem paramWitnessSet_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasurableSet (paramWitnessSet e c m ε) := by
  unfold paramWitnessSet
  -- The set is {q | ε/2 ≤ Δ(q)} where Δ = EmpErr_ghost - EmpErr_train
  -- Suffices to show Δ is measurable, then use measurableSet_le
  -- Helper: measurability of a single zeroOneLoss term for ghost sample
  have ghost_term_meas : ∀ i : Fin m, Measurable fun q : Θ × GhostPairs X m =>
      zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i)) := by
    intro i
    simp only [zeroOneLoss]
    apply Measurable.ite
    · exact measurableSet_eq_fun
        (he.comp (measurable_fst.prodMk
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
        (hc.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))
    · exact measurable_const
    · exact measurable_const
  -- Helper: measurability of a single zeroOneLoss term for train sample
  have train_term_meas : ∀ i : Fin m, Measurable fun q : Θ × GhostPairs X m =>
      zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i)) := by
    intro i
    simp only [zeroOneLoss]
    apply Measurable.ite
    · exact measurableSet_eq_fun
        (he.comp (measurable_fst.prodMk
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))))
        (hc.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    · exact measurable_const
    · exact measurable_const
  -- Helper: each EmpiricalError component is measurable
  have ghost_meas : Measurable fun q : Θ × GhostPairs X m =>
      EmpiricalError X Bool (e q.1) (fun i => (q.2.2 i, c (q.2.2 i))) (zeroOneLoss Bool) := by
    simp only [EmpiricalError]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      exact (Finset.measurable_sum _ (fun i _ => ghost_term_meas i)).div_const _
  have train_meas : Measurable fun q : Θ × GhostPairs X m =>
      EmpiricalError X Bool (e q.1) (fun i => (q.2.1 i, c (q.2.1 i))) (zeroOneLoss Bool) := by
    simp only [EmpiricalError]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      exact (Finset.measurable_sum _ (fun i _ => train_term_meas i)).div_const _
  -- The gap Δ = ghost - train is measurable
  exact measurableSet_le measurable_const (ghost_meas.sub train_meas)

/-! ## Theorem B: Bad event is analytic (Suslin projection) -/

/-- The bad event (projection of witness set) is analytic.
    Projection of a Borel set from a StandardBorelSpace is analytic (Suslin).
    This is the key step: existential quantification over parameters
    produces an analytic (Σ₁¹) set, which may not be Borel. -/
theorem borel_param_badEvent_analytic
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasureTheory.AnalyticSet (paramBadEvent e c m ε) := by
  -- paramBadEvent = Prod.snd '' paramWitnessSet (by definition)
  change MeasureTheory.AnalyticSet (Prod.snd '' paramWitnessSet e c m ε)
  -- paramWitnessSet is MeasurableSet (Theorem A)
  have hW := paramWitnessSet_measurable e he c hc m ε
  -- SecondCountableTopology on range of Prod.snd
  -- range Prod.snd ⊆ GhostPairs X m which is SecondCountableTopology (from PolishSpace X)
  -- Any subtype of a SecondCountableTopology space inherits it
  haveI : SecondCountableTopology (Set.range (Prod.snd : Θ × GhostPairs X m → GhostPairs X m)) :=
    inferInstance
  exact hW.analyticSet_image measurable_snd

/-! ## Theorem C' (F4c): Sample-space specialization -/

noncomputable abbrev GhostPairMeasure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) :
    MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))

/-- Analytic subsets of the ghost sample space `(Fin m → X) × (Fin m → X)` are
`NullMeasurableSet` under the product probability measure. A specialisation of
`analyticSet_nullMeasurableSet` from `PureMath/AnalyticMeasurability.lean` to the type
the symmetrization argument actually consumes. -/
theorem analyticSet_nullMeasurableSet_ghostPairs
    {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {m : ℕ} {s : Set ((Fin m → X) × (Fin m → X))}
    (hs : MeasureTheory.AnalyticSet s)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    MeasureTheory.NullMeasurableSet s (GhostPairMeasure D m) := by
  haveI : MeasureTheory.IsFiniteMeasure (GhostPairMeasure D m) := inferInstance
  exact analyticSet_nullMeasurableSet hs

/-! ## Theorem D: Positive bridge - bad event is NullMeasurableSet -/

/-- Positive bridge. If a concept class is parameterized by a Borel measurable map
`Θ → Concept X` from a standard Borel space `Θ`, then the symmetrization bad event is
analytic, hence `NullMeasurableSet`. The bad event is a Suslin projection of a Borel
witness set (the projection along `Θ` of `{(θ, p) | gap(eval θ, p) ≥ ε / 2}`), and
projections of Borel sets are analytic by definition. This is the entry point through
which Borel parameterization implies the regularity required by the fundamental
theorem. -/
theorem borel_param_nullMeasurableSet_bad_event
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    NullMeasurableSet (paramBadEvent e c m ε) (GhostPairMeasure D m) :=
  analyticSet_nullMeasurableSet_ghostPairs
    (borel_param_badEvent_analytic e he c hc m ε) D

/-! ## Theorem E (F5): Class-level corollary -/

/-- Class-level corollary: every Borel-parameterized concept class with a measurable
evaluation map satisfies `WellBehavedVCMeasTarget`. Composes
`borel_param_nullMeasurableSet_bad_event` over all measurable targets `c`. The
measurable-target variant of `WellBehavedVC` is what the kernel actually proves; the
unrestricted variant remains open and is the subject of the Borel-analytic separation
witness in `Theorem/BorelAnalyticSeparation.lean`. -/
theorem borel_param_wellBehavedVCMeasTarget
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range e) := by
  intro D _ c hc m ε
  have hEq :
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ Set.range e,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = paramBadEvent e c m ε := by
    ext p
    simp only [paramBadEvent, paramWitnessSet, Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    constructor
    · rintro ⟨_, ⟨θ, rfl⟩, hp⟩; exact ⟨θ, p.1, p.2, hp, rfl⟩
    · rintro ⟨θ, s1, s2, hp, heq⟩
      have : (s1, s2) = p := Prod.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
      subst this
      exact ⟨e θ, ⟨θ, rfl⟩, hp⟩
  rw [hEq]
  exact borel_param_nullMeasurableSet_bad_event e he c hc m ε D

/-! ## Theorem F (F6): Closure principle for patching -/

/-- Closure under patching: if `e₁ : Θ₁ → Concept X`, `e₂ : Θ₂ → Concept X`, and a
region selector `r : Ρ → Concept X Bool` are jointly measurable, then so is the
piecewise evaluation
`(θ₁, θ₂, ρ, x) ↦ if r ρ x then e₁ θ₁ x else e₂ θ₂ x`
on the combined parameter space. The basic compositional fact behind
`patch_borel_param_wellBehavedVCMeasTarget`. -/
theorem patchEval_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => patchEval e₁ e₂ r p.1 p.2) := by
  simp only [patchEval]
  have hpred : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => r p.1.2.2 p.2) :=
    hr.comp (Measurable.prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst)) measurable_snd)
  have hleft : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => e₁ p.1.1 p.2) :=
    he₁.comp (Measurable.prodMk
      (measurable_fst.comp measurable_fst) measurable_snd)
  have hright : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => e₂ p.1.2.1 p.2) :=
    he₂.comp (Measurable.prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst)) measurable_snd)
  have hset : MeasurableSet {p : (Θ₁ × Θ₂ × Ρ) × X | r p.1.2.2 p.2 = true} :=
    hpred (measurableSet_singleton true)
  exact Measurable.piecewise hset hleft hright

/-- The patched union of two Borel-parameterized classes (with a measurable region
selector) is itself Borel-parameterized over `Θ₁ × Θ₂ × Ρ`, and therefore satisfies
`WellBehavedVCMeasTarget`. Immediate from `patchEval_measurable` and
`borel_param_wellBehavedVCMeasTarget`. Surfacing this corollary at the class level makes
the closure of the measurable-target hypothesis under amalgamation explicit. -/
theorem patch_borel_param_wellBehavedVCMeasTarget
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace Ρ] [StandardBorelSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range (patchEval e₁ e₂ r)) :=
  borel_param_wellBehavedVCMeasTarget (patchEval e₁ e₂ r)
    (patchEval_measurable e₁ e₂ r he₁ he₂ hr)

attribute [nolint docBlame] GhostPairMeasure
attribute [nolint unusedArguments] paramWitnessSet patchEval
