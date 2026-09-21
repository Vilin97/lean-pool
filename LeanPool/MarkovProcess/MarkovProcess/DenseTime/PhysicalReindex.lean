/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FiniteMarginals

/-!
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/

noncomputable section PortComputability

namespace MarkovProcess

section

namespace DenseTime

open SubMarkovKernelSemigroup

/-- Casting identifies a finite dense-time set with its image in physical nonnegative-real time. -/
def physicalSetEquiv (I : Finset DenseTime) : I ≃ denseTimePhysicalSet I :=
  Equiv.ofBijective
    (fun t ↦ ⟨castOrderEmbedding t, by
      rw [denseTimePhysicalSet, Finset.mem_map]
      exact ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      exact castOrderEmbedding.injective (congrArg Subtype.val h),
    by
      intro t
      have ht := t.property
      change t.val ∈ I.map castOrderEmbedding.toEmbedding at ht
      rw [Finset.mem_map] at ht
      obtain ⟨r, hrI, hrt⟩ := ht
      exact ⟨⟨r, hrI⟩, Subtype.ext hrt⟩⟩

@[simp]
theorem physicalSetEquiv_apply (I : Finset DenseTime) (t : I) :
    (physicalSetEquiv I t : NNReal) = castOrderEmbedding t := rfl

end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}

/-- Reindex a finite path labelled by physical rational times back to dense-time labels. -/
def pullbackPhysicalSet (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) : I → alpha :=
  fun t ↦ path (DenseTime.physicalSetEquiv I t)

@[simp]
theorem pullbackPhysicalSet_apply (I : Finset DenseTime)
    (path : denseTimePhysicalSet I → alpha) (t : I) :
    pullbackPhysicalSet I path t = path (DenseTime.physicalSetEquiv I t) := rfl

variable [MeasurableSpace alpha]

/-- Reindexing a finite physical-time path by its dense labels is measurable. -/
theorem measurable_pullbackPhysicalSet (I : Finset DenseTime) :
    Measurable (pullbackPhysicalSet (alpha := alpha) I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply (DenseTime.physicalSetEquiv I t)

omit [MeasurableSpace alpha] in
/-- Evaluating a continuous path on physical rational times and reindexing gives restriction of
its dense-time path. -/
theorem pullbackPhysicalSet_evaluation (I : Finset DenseTime)
    [TopologicalSpace alpha] (omega : ContinuousPath alpha) :
    pullbackPhysicalSet I
        (fun t : denseTimePhysicalSet I ↦ omega t) =
      I.restrict (ContinuousPath.denseRestriction omega) := by
  funext t
  rfl

end DenseTimePath
end
end MarkovProcess

end PortComputability
