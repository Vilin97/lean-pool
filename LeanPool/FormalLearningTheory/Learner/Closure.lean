/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Core
import LeanPool.FormalLearningTheory.Complexity.Generalization

/-!
# Closure of Measurable Learners under Combiners and Selection

The algebra of `MeasurableBatchLearner`s is closed under:
- arbitrary Boolean combiners (`combineLearner`)
- majority-vote boosting (`boostLearner`)
- measurable-set interpolation (`interpLearner`)
- countable selection (`concatLearner`)

-/

universe u

attribute [local instance] Classical.propDecidable

/-! ## Part 1: combineLearner -/

/-- Combines `k` learners by a measurable Boolean function. Given learners `L₁, …, Lₖ`
and a jointly measurable combiner `F : X × (Fin k → Bool) → Bool`, returns a learner
whose prediction at `x` is `F` applied to `x` and the vector of base predictions. The
foundational closure operation: every other operation in this file is a special case. -/
noncomputable def combineLearner
    {X : Type u}
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool where
  hypotheses := {h | ∃ hs : Fin k → Concept X Bool,
    (∀ i, hs i ∈ (L i).hypotheses) ∧
    h = fun x => F x (fun i => hs i x)}
  learn := fun {m} S x => F x (fun i => (L i).learn S x)
  output_in_H := fun {m} S => by
    simp only [Set.mem_setOf_eq]
    exact ⟨fun i => (L i).learn S, fun i => (L i).output_in_H S, rfl⟩

/-! ## Part 2: Measurability of combineLearner -/

/-- `combineLearner` preserves `MeasurableBatchLearner` whenever the combiner `F` is
jointly measurable. Factored through measurability of coordinate projections in the
product σ-algebra. -/
theorem measurableBatchLearner_combine
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (hF : Measurable (fun p : X × (Fin k → Bool) => F p.1 p.2))
    (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (combineLearner k F L) where
  eval_measurable m := by
    change Measurable (fun p : (Fin m → X × Bool) × X => F p.2 (fun i => (L i).learn p.1 p.2))
    have hg : Measurable (fun p : (Fin m → X × Bool) × X =>
        (p.2, fun i => (L i).learn p.1 p.2) : (Fin m → X × Bool) × X → X × (Fin k → Bool)) :=
      Measurable.prodMk measurable_snd
        (measurable_pi_lambda _ (fun i => (hL i).eval_measurable m))
    exact hF.comp hg

/-! ## Part 3: Boost learner via majority vote -/

/-- Boosting via majority vote. Runs `k` base learners on the *same* training sample
and outputs the majority of their predictions at each query point. Used in the
`boost_two_thirds_to_pac` reduction that promotes a weak learner with success
probability at least `2 / 3` to a full PAC learner; the quantitative `7 / 12`-Chebyshev
step lives in the proof of that reduction, not in the construction itself. -/
noncomputable def boostLearner
    {X : Type u}
    (k : ℕ) (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner k (fun _ v => majorityVote k v) L

/-- Boosting preserves measurability. Majority vote is a measurable Boolean function of
finitely many inputs, so `boostLearner` inherits measurability via
`measurableBatchLearner_combine`. -/
theorem measurableBatchLearner_boost
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (boostLearner k L) := by
  apply measurableBatchLearner_combine
  · exact (measurable_of_finite (fun v : Fin k → Bool => majorityVote k v)).comp measurable_snd
  · exact hL

/-! ## Part 4: Interpolation learner -/

/-- Spatial interpolation: uses learner `L₁` on a region `A ⊆ X` and learner `L₂` on
its complement. The piecewise selector uses `x ∈ A` directly; measurability of `A` is
not required by the definition and appears only in the accompanying
`measurableBatchLearner_interp` theorem. The constructive content of the
`Complexity/Interpolation.lean` module. -/
noncomputable def interpLearner
    {X : Type u}
    (A : Set X) (L₁ L₂ : BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner 2
    (fun x v => if x ∈ A then v 0 else v 1)
    (fun i => if i = 0 then L₁ else L₂)

/-- `interpLearner` preserves measurability when the region `A` is measurable. The
indicator of `A` composed with `Measurable.ite` and the two component learners gives a
measurable conditional selector. -/
theorem measurableBatchLearner_interp
    {X : Type u} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A)
    (L₁ L₂ : BatchLearner X Bool)
    (h₁ : MeasurableBatchLearner X L₁)
    (h₂ : MeasurableBatchLearner X L₂) :
    MeasurableBatchLearner X (interpLearner A L₁ L₂) := by
  apply measurableBatchLearner_combine
  · change Measurable (fun p : X × (Fin 2 → Bool) => if p.1 ∈ A then p.2 0 else p.2 1)
    exact Measurable.ite (measurable_fst hA) ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 1).comp measurable_snd)
  · intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂

/-! ## Part 5: Uniform measurability for indexed families -/

/-- A family of batch learners indexed by `ℕ` with a *uniform* joint measurability
guarantee: for each `m`, the map `(n, S, x) ↦ (L n).learn S x` on
`ℕ × (Fin m → X × Bool) × X` is measurable. Required wherever a learner construction
selects among infinitely many components, in particular by `concatLearner` and the
monad's `bind`. Pointwise measurability of each individual `L n` is the easier
consequence (`UniformMeasurableBatchFamily.pointwise`); uniformity is the substantive
requirement. -/
class UniformMeasurableBatchFamily {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) : Prop where
  eval_measurable : ∀ (m : ℕ),
    Measurable (fun p : ℕ × (Fin m → X × Bool) × X => (L p.1).learn p.2.1 p.2.2)

/-- A uniform measurable batch family is pointwise measurable: each individual `L n`
belongs to `MeasurableBatchLearner`. The uniform property factors through the constant
index embedding `n ↦ (n, ·)`. -/
theorem UniformMeasurableBatchFamily.pointwise
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) [hL : UniformMeasurableBatchFamily L]
    (n : ℕ) : MeasurableBatchLearner X (L n) where
  eval_measurable m :=
    (hL.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)

/-! ## Part 6: Concat learner with measurable selection -/

/-- Sequential composition via a selector. Given a family of learners and a selector
`sel : {m : ℕ} → (Fin m → X × Bool) → ℕ`, runs `L (sel S)` on sample `S`. The composite
hypothesis space is the union of the component spaces. No measurability requirement on
`sel` is imposed at the definition level; the accompanying
`measurableBatchLearner_concat` theorem adds that hypothesis to derive closure under
the uniform-measurable family. The construction underlying the monadic `bind`. -/
noncomputable def concatLearner
    {X : Type u}
    (L : ℕ → BatchLearner X Bool)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ) : BatchLearner X Bool where
  hypotheses := ⋃ n, (L n).hypotheses
  learn := fun S x => (L (sel S)).learn S x
  output_in_H := fun S => Set.mem_iUnion.mpr ⟨sel S, (L (sel S)).output_in_H S⟩

/-- `concatLearner` preserves measurability when the selector is measurable and the
family is uniformly measurable. Composes the selector's measurability with the
family's uniform measurability to obtain joint measurability of the evaluation map in
`(S, x)`. -/
theorem measurableBatchLearner_concat
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool)
    [hL : UniformMeasurableBatchFamily L]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasurableBatchLearner X (concatLearner L sel) where
  eval_measurable m := by
    change Measurable (fun p : (Fin m → X × Bool) × X => (L (sel p.1)).learn p.1 p.2)
    -- Factor: (hL.eval_measurable m) ∘ (fun p => (sel p.1, p.1, p.2))
    exact (hL.eval_measurable m).comp
      (Measurable.prodMk ((hsel m).comp measurable_fst)
        (Measurable.prodMk measurable_fst measurable_snd))
