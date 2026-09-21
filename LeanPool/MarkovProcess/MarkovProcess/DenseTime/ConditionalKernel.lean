/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Time.DenseTimeHistory
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PrefixKernel
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Conditional kernels for finite dense-time histories

This file augments finite prefix laws by their starting point and disintegrates the joint law of
a prefix and its next observation. It makes no infinite-process or path-regularity claim.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

section

variable {D α : Type*} [MeasurableSpace α]

/-- The law of a finite history, including the deterministic starting point. -/
def augmentedPrefixKernel (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α (DenseTimeHistory α n) :=
  Kernel.mapOfMeasurable
    (Kernel.id ×ₖ denseTimePrefixKernel P e ι n)
    (DenseTimeHistory.historyEquiv n).symm
    (DenseTimeHistory.historyEquiv n).symm.measurable

/-- Mapping an augmented history back to its two components recovers its defining product law. -/
theorem augmentedPrefixKernel_map_historyEquiv (P : SubMarkovKernelSemigroup α)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (augmentedPrefixKernel P e ι n).map (DenseTimeHistory.historyEquiv n) =
      Kernel.id ×ₖ denseTimePrefixKernel P e ι n := by
  rw [augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map, ← Kernel.map_comp_right]
  · have hcomp :
        (DenseTimeHistory.historyEquiv n : DenseTimeHistory α n →
            α × (Fin n → α)) ∘
            (DenseTimeHistory.historyEquiv n).symm = id := by
      funext z
      exact MeasurableEquiv.apply_symm_apply _ z
    rw [hcomp, Kernel.map_id]
  · exact (DenseTimeHistory.historyEquiv n).symm.measurable
  · exact (DenseTimeHistory.historyEquiv n).measurable

/-- The joint law of an `n`-prefix and the next enumerated observation. -/
def nextObservationJoint (P : SubMarkovKernelSemigroup α) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel α ((Fin n → α) × α) :=
  Kernel.mapOfMeasurable (denseTimePrefixKernel P e ι (n + 1))
    (DenseTimeHistory.splitLast n) (DenseTimeHistory.splitLast n).measurable

namespace IsConservative

variable [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
/-- Augmented finite-history laws are Markov kernels under conservativity. -/
theorem isMarkovKernel_augmentedPrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (augmentedPrefixKernel P e ι n) := by
  rw [augmentedPrefixKernel, Kernel.mapOfMeasurable_eq_map]
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.historyEquiv n).symm.measurable

omit [StandardBorelSpace α] [Nonempty α] in
/-- The first marginal of the next-observation joint law is the preceding prefix law. -/
theorem nextObservationJoint_fst (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (nextObservationJoint P e ι n).fst = denseTimePrefixKernel P e ι n := by
  rw [nextObservationJoint, Kernel.mapOfMeasurable_eq_map, Kernel.fst_eq,
    ← Kernel.map_comp_right]
  · change
      (denseTimePrefixKernel P e ι n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
        denseTimePrefixKernel P e ι n
    calc
      (denseTimePrefixKernel P e ι n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
          (denseTimePrefixKernel P e ι n.succ).map
            (FiniteOrderedTimes.restrictPath
              (Fin.castLEOrderEmb (Nat.le_succ n))) := by
        congr 1
        funext path i
        exact DenseTimeHistory.splitLast_fst_apply n path i
      _ = denseTimePrefixKernel P e ι n :=
        (hP.denseTimePrefixKernel_map_restrictPath P e ι (Nat.le_succ n)).symm
  · exact (DenseTimeHistory.splitLast n).measurable
  · exact measurable_fst

/-- A regular conditional law of the next observation given the start and preceding prefix. -/
def observationCondKernel (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (α × (Fin n → α)) α := by
  letI : IsMarkovKernel (nextObservationJoint P e ι n) := by
    rw [nextObservationJoint, Kernel.mapOfMeasurable_eq_map]
    let : IsMarkovKernel (denseTimePrefixKernel P e ι (n + 1)) :=
      hP.isMarkovKernel_denseTimePrefixKernel P e ι (n + 1)
    exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.splitLast n).measurable
  exact (nextObservationJoint P e ι n).condKernel

/-- The conditional next-observation law is Markov. -/
theorem isMarkovKernel_observationCondKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (observationCondKernel P hP e ι n) := by
  rw [observationCondKernel]
  infer_instance

/-- Disintegration exactly reconstructs the next-observation joint law. -/
theorem compProd_observationCondKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    denseTimePrefixKernel P e ι n ⊗ₖ observationCondKernel P hP e ι n =
      nextObservationJoint P e ι n := by
  rw [← nextObservationJoint_fst P hP e ι n]
  rw [observationCondKernel]
  exact Kernel.disintegrate _ _

/-- The conditional next-observation law, viewed as a kernel on finite histories. -/
def denseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (DenseTimeHistory α n) α :=
  Kernel.comap (observationCondKernel P hP e ι n)
    (DenseTimeHistory.historyEquiv n) (DenseTimeHistory.historyEquiv n).measurable

/-- The finite-history next-observation kernel is Markov. -/
theorem isMarkovKernel_denseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (denseStep P hP e ι n) := by
  rw [denseStep]
  let : IsMarkovKernel (observationCondKernel P hP e ι n) :=
    isMarkovKernel_observationCondKernel P hP e ι n
  infer_instance

end IsConservative
end
end SubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
