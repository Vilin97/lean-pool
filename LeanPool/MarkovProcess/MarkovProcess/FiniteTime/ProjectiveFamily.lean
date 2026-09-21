/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelRestriction
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl

/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)

/-- Reindexing an ordered coordinate path by its finite set of times is measurable. -/
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) :
    Measurable (orderedPathToFiniteSet (α := α) I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)

/-- The finite-time kernel indexed by a finite set of times. -/
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)

/-- The finite-set kernel agrees with the ordinary kernel map. -/
theorem finiteSetKernel_eq_map (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    finiteSetKernel P I =
      (finiteTimeKernel P (finiteSetTimes I)).map (orderedPathToFiniteSet I) :=
  Kernel.mapOfMeasurable_eq_map _ (measurable_orderedPathToFiniteSet I)

/-- The finite-set law at a starting state. -/
noncomputable def finiteSetLaw (P : SubMarkovKernelSemigroup α) (I : Finset NNReal)
    (x : α) : Measure (I → α) :=
  finiteSetKernel P I x

private noncomputable def inclusionOrderEmb {I J : Finset NNReal} (hJI : J ⊆ I) :
    Fin J.card ↪o Fin I.card :=
  (J.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : J ↦ (⟨t, hJI t.property⟩ : I)) (fun _ _ h ↦ h)) |>.trans
    (I.orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    (finiteSetTimes I).restrict (inclusionOrderEmb hJI) = finiteSetTimes J := by
  apply DFunLike.ext _ _
  intro i
  change (((I.orderIsoOfFin rfl)
      ((I.orderIsoOfFin rfl).symm
        ⟨↑(J.orderIsoOfFin rfl i), hJI (J.orderIsoOfFin rfl i).property⟩) : I) :
      NNReal) = ((J.orderIsoOfFin rfl i : J) : NNReal)
  rw [OrderIso.apply_symm_apply]

omit [MeasurableSpace α] in
private theorem orderedPathToFiniteSet_restrict {I J : Finset NNReal} (hJI : J ⊆ I) :
    Finset.restrict₂ (π := fun _ ↦ α) hJI ∘ orderedPathToFiniteSet (α := α) I =
      orderedPathToFiniteSet J ∘
        FiniteOrderedTimes.restrictPath (inclusionOrderEmb hJI) := by
  funext path t
  change path ((I.orderIsoOfFin rfl).symm ⟨t, hJI t.property⟩) =
    path (inclusionOrderEmb hJI ((J.orderIsoOfFin rfl).symm t))
  simp only [inclusionOrderEmb, RelEmbedding.coe_trans, Function.comp_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

namespace IsConservative

/-- Under conservativity, every finite-set kernel is a Markov kernel. -/
theorem isMarkovKernel_finiteSetKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) : IsMarkovKernel (finiteSetKernel P I) := by
  rw [finiteSetKernel_eq_map]
  let : IsMarkovKernel (finiteTimeKernel P (finiteSetTimes I)) :=
    hP.isMarkovKernel_finiteTimeKernel P (finiteSetTimes I)
  exact Kernel.IsMarkovKernel.map _ (measurable_orderedPathToFiniteSet I)

/-- Under conservativity, every finite-set law is a probability measure. -/
theorem isProbabilityMeasure_finiteSetLaw (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) (x : α) :
    IsProbabilityMeasure (finiteSetLaw P I x) := by
  let : IsMarkovKernel (finiteSetKernel P I) := hP.isMarkovKernel_finiteSetKernel P I
  exact IsMarkovKernel.isProbabilityMeasure x

/-- A finite-set kernel restricted along an inclusion is the kernel on the smaller set. -/
theorem finiteSetKernel_map_restrict₂ (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) {I J : Finset NNReal} (hJI : J ⊆ I) :
    finiteSetKernel P J =
      (finiteSetKernel P I).map (Finset.restrict₂ (π := fun _ ↦ α) hJI) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [orderedPathToFiniteSet_restrict hJI, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I)
          (inclusionOrderEmb hJI), finiteSetTimes_restrict hJI]
    · exact FiniteOrderedTimes.measurable_restrictPath (inclusionOrderEmb hJI)
    · exact measurable_orderedPathToFiniteSet J
  · exact measurable_orderedPathToFiniteSet I
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ α) hJI

/-- The finite-set laws of a conservative semigroup form a projective measure family. -/
theorem isProjectiveMeasureFamily_finiteSetLaw (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (x : α) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal ↦ α)
      (fun I : Finset NNReal ↦ finiteSetLaw P I x) := by
  intro I J hJI
  change finiteSetKernel P J x =
    Measure.map (Finset.restrict₂ (π := fun _ ↦ α) hJI) (finiteSetKernel P I x)
  rw [← Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ α) hJI)]
  exact congrArg (fun K : Kernel α (J → α) ↦ K x)
    (hP.finiteSetKernel_map_restrict₂ P hJI)

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
