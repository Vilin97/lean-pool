/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Learner.Closure
import LeanPool.FormalLearningTheory.PureMath.ReaderMonad

/-!
# Measurable Batch Learner Monad

MeasurableBatchLearner is a measurable instance of the pure ReaderSel monad
(MathLib/ReaderMonad.lean). The algebraic structure (pure, bind, monad laws)
lives in the pure math layer. This file adds the measurability certificate.

- `MeasLearner`: BatchLearner bundled with MeasurableBatchLearner proof
- `MeasLearner.pure`: constant learner (delegates to ReaderSel.pure)
- `MeasLearner.bind`: selection-based composition (delegates to concatLearner)
- Monad laws: inherited from ReaderSel, verified at evaluation level
-/

universe u

/-- A measurable batch learner bundled with its measurability certificate. The carrier
of the learner monad: pairs a `BatchLearner` with a proof of `MeasurableBatchLearner`,
so that monadic composition can automatically preserve measurability without
re-derivation at the call site. -/
structure MeasLearner (X : Type u) [MeasurableSpace X] where
  learner : BatchLearner X Bool
  measurable : MeasurableBatchLearner X learner

/-- Unit of the learner monad. Returns the constant learner that ignores its training
data and always outputs the fixed measurable hypothesis `h`. The hypothesis space is
the singleton `{h}`; measurability is the projection-then-constant pattern. -/
noncomputable def MeasLearner.pure
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (h : Concept X Bool) (hm : Measurable h) : MeasLearner X where
  learner := {
    hypotheses := {h}
    learn := fun _ => h
    output_in_H := fun _ => Set.mem_singleton h
  }
  measurable := ⟨fun _m => hm.comp measurable_snd⟩

/-- Monadic bind for measurable learners. Sequential composition where the second
learner is selected by a measurable function of the training sample, implemented via
`concatLearner` over a `UniformMeasurableBatchFamily` of continuations.

The non-trivial design choice is that `bind` requires a *uniformly* measurable family
of continuations rather than a merely pointwise measurable one. This is the type-level
encoding of the joint-measurability hypothesis without which sequential composition
would not stay inside `MeasurableBatchLearner`. The closure algebra proves the
construction is sound; the type signature makes the necessary hypothesis
non-bypassable. -/
noncomputable def MeasLearner.bind
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasLearner X where
  learner := concatLearner (fun n => (family n).learner) sel
  measurable := measurableBatchLearner_concat _ sel hsel

/-! ## Monad Laws

The algebraic structure is inherited from ReaderSel (MathLib/ReaderMonad.lean).
At the evaluation level, concatLearner.learn S x = (family (sel S)).learner.learn S x,
which is ReaderSel.eval specialized to ι = ℕ, α = Fin m → X × Bool. -/

/-- Left-unit law at the evaluation level: with a constant selector `fun _ => n`, the
`concatLearner` of a family evaluates at `(S, x)` to `(family n).learner.learn S x`.
Holds definitionally (`rfl`): `concatLearner` with a constant selector reduces to
evaluating the selected family member. -/
theorem MeasLearner.left_unit
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (n : ℕ) {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun i => (family i).learner) (fun _ => n)).learn S x =
    (family n).learner.learn S x := by rfl

/-- Right-unit law at the evaluation level: with a constant family `fun _ => L`, the
`concatLearner` collapses under any selector to plain `L.learner.learn S x`. Holds
definitionally (`rfl`). -/
theorem MeasLearner.right_unit
    {X : Type u} [MeasurableSpace X]
    (L : MeasLearner X)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun _ => L.learner) sel).learn S x =
    L.learner.learn S x := by rfl

/-- Associativity at the evaluation level: the `concatLearner` evaluation
`(concatLearner (fun n => (family n).learner) sel).learn S x` reduces definitionally
to `(family (sel S)).learner.learn S x`. Held by `rfl`; the identity is what lets
nested `concatLearner` selections compose into a single selector in downstream
constructions. -/
theorem MeasLearner.assoc
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun n => (family n).learner) sel).learn S x =
    (family (sel S)).learner.learn S x := by rfl

attribute [nolint docBlame] MeasLearner.learner
attribute [nolint unusedArguments] MeasLearner.pure
