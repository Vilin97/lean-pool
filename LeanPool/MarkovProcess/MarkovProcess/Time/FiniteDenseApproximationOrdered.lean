/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.AllTimeFiniteMarginals


/-!
# Ordered form of finite dense approximations

This file expresses a finite dense-approximation kernel as a finite-time kernel at its
increasing physical times. The final coordinate reindexing is the fixed map
`orderedPathToFiniteSet I`; it does not depend on the chosen dense approximation `q`.

The construction also covers `I = ∅`. In that case the ordered time family and both path
coordinate types are empty.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

section

/-- The physical times of a finite dense approximation, listed in the increasing order inherited
from the original finite set. For an empty finite set this is the empty ordered family. -/
def finiteDenseApproximationOrderedTimes {I : Finset NNReal} (q : I ↪o DenseTime) :
    FiniteOrderedTimes I.card :=
  ((I.orderIsoOfFin rfl).toOrderEmbedding.trans q).trans DenseTime.castOrderEmbedding

@[simp]
theorem finiteDenseApproximationOrderedTimes_apply {I : Finset NNReal}
    (q : I ↪o DenseTime) (i : Fin I.card) :
    finiteDenseApproximationOrderedTimes q i =
      DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)) :=
  rfl

private theorem approximation_mem {I : Finset NNReal} (q : I ↪o DenseTime) (t : I) :
    DenseTime.castOrderEmbedding (q t) ∈ finiteDenseApproximationPhysicalSet q := by
  rw [finiteDenseApproximationPhysicalSet, denseTimePhysicalSet, Finset.mem_map]
  refine ⟨q t, ?_, rfl⟩
  rw [finiteDenseApproximationIndexSet, Finset.mem_map]
  exact ⟨t, Finset.mem_univ t, rfl⟩

private def finiteDenseApproximationOrderEmb {I : Finset NNReal} (q : I ↪o DenseTime) :
    Fin I.card ↪o Fin (finiteDenseApproximationPhysicalSet q).card :=
  (I.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (OrderEmbedding.ofStrictMono
      (fun t : I => (⟨DenseTime.castOrderEmbedding (q t), approximation_mem q t⟩ :
        finiteDenseApproximationPhysicalSet q))
        (fun _ _ h => DenseTime.castOrderEmbedding.strictMono (q.strictMono h))) |>.trans
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl).symm.toOrderEmbedding

private theorem finiteSetTimes_restrict_approximationOrderEmb
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    (finiteSetTimes (finiteDenseApproximationPhysicalSet q)).restrict
        (finiteDenseApproximationOrderEmb q) =
      finiteDenseApproximationOrderedTimes q := by
  apply DFunLike.ext _ _
  intro i
  change finiteSetTimes (finiteDenseApproximationPhysicalSet q)
      (finiteDenseApproximationOrderEmb q i) = _
  simp only [finiteSetTimes, finiteDenseApproximationOrderEmb,
    finiteDenseApproximationOrderedTimes, RelEmbedding.trans_apply]
  exact congrArg Subtype.val
    ((finiteDenseApproximationPhysicalSet q).orderIsoOfFin rfl |>.apply_symm_apply
      ⟨DenseTime.castOrderEmbedding (q (I.orderIsoOfFin rfl i)),
        approximation_mem q (I.orderIsoOfFin rfl i)⟩)

private theorem reindex_comp_orderedPathToFiniteSet
    {gamma : Type*} {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationReindex (γ := gamma) q ∘
        orderedPathToFiniteSet (finiteDenseApproximationPhysicalSet q) =
      orderedPathToFiniteSet I ∘
        FiniteOrderedTimes.restrictPath (finiteDenseApproximationOrderEmb q) := by
  funext path t
  simp only [Function.comp_apply, finiteDenseApproximationReindex,
    orderedPathToFiniteSet, FiniteOrderedTimes.restrictPath,
    finiteDenseApproximationOrderEmb, RelEmbedding.trans_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply]
  rfl

/-- A conservative finite dense-approximation kernel is the finite-time kernel at its canonical
ordered physical times, mapped by the fixed, `q`-independent reindexing to `I`-indexed paths.
The statement includes the empty finite set. -/
theorem finiteDenseApproximationKernel_eq_map_finiteTimeKernel
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {I : Finset NNReal} (q : I ↪o DenseTime) :
    finiteDenseApproximationKernel P q =
      (finiteTimeKernel P (finiteDenseApproximationOrderedTimes q)).map
        (orderedPathToFiniteSet I) := by
  rw [finiteDenseApproximationKernel, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
  · rw [reindex_comp_orderedPathToFiniteSet q, Kernel.map_comp_right]
    · rw [hP.finiteTimeKernel_map_restrictPath P,
        finiteSetTimes_restrict_approximationOrderEmb q]
    · exact FiniteOrderedTimes.measurable_restrictPath _
    · exact measurable_orderedPathToFiniteSet _
  · exact measurable_orderedPathToFiniteSet _
  · exact measurable_finiteDenseApproximationReindex q

/-- Coordinatewise convergence of dense approximations gives convergence of each coordinate of
their canonical ordered physical-time families. This is vacuous when `I` is empty. -/
theorem tendsto_finiteDenseApproximationOrderedTimes
    {I : Finset NNReal} (q : ℕ → I ↪o DenseTime)
    (hq : ∀ t, Tendsto (fun k ↦ DenseTime.castOrderEmbedding (q k t)) atTop
      (nhds (t : NNReal))) (i : Fin I.card) :
    Tendsto (fun k ↦ finiteDenseApproximationOrderedTimes (q k) i) atTop
      (nhds (finiteSetTimes I i)) := by
  change Tendsto
    (fun k ↦ DenseTime.castOrderEmbedding (q k (I.orderIsoOfFin rfl i))) atTop
    (nhds ((I.orderIsoOfFin rfl i : I) : NNReal))
  exact hq (I.orderIsoOfFin rfl i)

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
