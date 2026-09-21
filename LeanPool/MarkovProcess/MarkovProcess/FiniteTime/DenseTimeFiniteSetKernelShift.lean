/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PhysicalReindex
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteSetKernelShift

/-!
# Translation of finite dense-time kernels

This file transports the finite-set kernel translation law from physical nonnegative-real times
to finite sets of dense times, using the canonical coordinate reindexings.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

section

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]

/-- Translating a finite dense-time observation set is the same as first evolving for the
corresponding physical duration, after both physical and dense coordinates are reindexed. -/
theorem finiteSetKernel_map_pullback_addFinset
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : DenseTime) (I : Finset DenseTime) :
    (finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
        (DenseTimePath.pullbackAddFinset s I ∘
          DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I)) =
      ((finiteSetKernel P (denseTimePhysicalSet I)).map
        (DenseTimePath.pullbackPhysicalSet I)).comp
        (P (DenseTime.castOrderEmbedding s)) := by
  have hsets :
      denseTimePhysicalSet (DenseTime.addFinset s I) =
        finiteSetTranslate (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I) :=
    DenseTime.map_castOrderEmbedding_addFinset s I
  have hsubset :
      finiteSetTranslate (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I) ⊆
        denseTimePhysicalSet (DenseTime.addFinset s I) :=
    hsets.symm.le
  have hcoordinates :
      DenseTimePath.pullbackAddFinset (alpha := alpha) s I ∘
          DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I) =
        (DenseTimePath.pullbackPhysicalSet I ∘
          pullbackFiniteSetTranslate (DenseTime.castOrderEmbedding s)
            (denseTimePhysicalSet I)) ∘
          Finset.restrict₂ (π := fun _ ↦ alpha) hsubset := by
    funext path t
    apply congrArg path
    apply Subtype.ext
    exact DenseTime.castOrderEmbedding_add s t
  rw [hcoordinates, Kernel.map_comp_right]
  · rw [← hP.finiteSetKernel_map_restrict₂ P hsubset, Kernel.map_comp_right]
    · rw [hP.finiteSetKernel_map_pullback_translate P, Kernel.map_comp]
    · exact measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I)
    · exact DenseTimePath.measurable_pullbackPhysicalSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hsubset
  · exact (DenseTimePath.measurable_pullbackPhysicalSet I).comp
      (measurable_pullbackFiniteSetTranslate
        (DenseTime.castOrderEmbedding s) (denseTimePhysicalSet I))

end IsConservative

end
end SubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
