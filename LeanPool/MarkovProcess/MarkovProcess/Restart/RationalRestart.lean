/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Restart.RationalRestrictedRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.FinitePastRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.MixedPastFuture
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import LeanPool.MarkovProcess.MarkovProcess.Kernel.CompProdReindex
import LeanPool.MarkovProcess.MarkovProcess.Path.MixedFiniteMarginals

/-!
# The rational-time restart kernel and its joint law

This file merges the following former modules, one section each:

* `RationalJointKernel`: The rational past/future restart kernel
* `RationalRestartFiniteMarginals`: Finite marginals of the rational restart kernel
* `RationalJointLaw`: Rational-time joint restart law
-/

namespace MarkovProcess

section RationalJointKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- The complete rational-past restriction is Borel measurable. -/
theorem measurable_densePastRestriction (S : DenseTime) :
    Measurable (densePastRestriction (alpha := alpha) S) := by
  apply Measurable.of_comap_le
  rw [comap_densePastRestriction_eq_canonicalFiltration]
  exact (canonicalFiltration (alpha := alpha)).le (DenseTime.castOrderEmbedding S)

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- Encoding the complete rational past and the dense coordinates of the shifted future is the
existing mixed past/future coordinate map. -/
@[simp]
theorem finitePastDenseFuture_densePastRestriction_shift
    (S : DenseTime) (omega : ContinuousPath alpha) :
    Kernel.finitePastDenseFuture
        (densePastRestriction S omega,
          shift (DenseTime.castOrderEmbedding S) omega) =
      mixedPastShiftedCoordinates S omega := by
  funext i
  rcases i with r | t
  · rfl
  · rfl

/-- The kernel which samples the rational past and then an independent future trajectory started
from the terminal state of that past. -/
def rationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) (S : DenseTime) :
    Kernel alpha ((Set.Iic S → alpha) × ContinuousPath alpha) :=
  Q.map (densePastRestriction S) ⊗ₖ
    Kernel.prodMkLeft alpha
      (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S))

/-- If `Q` is a Markov path kernel, then so is its rational past/future restart kernel. -/
instance instIsMarkovKernelRationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q] (S : DenseTime) :
    IsMarkovKernel (rationalPastFutureRestartKernel Q S) := by
  unfold rationalPastFutureRestartKernel
  let : IsMarkovKernel (Q.map (densePastRestriction S)) :=
    Kernel.IsMarkovKernel.map Q (measurable_densePastRestriction S)
  infer_instance

/-- At a starting point, the rational past/future restart kernel is the measure composition
product of the rational-past marginal and the path kernel started from its terminal state. -/
theorem rationalPastFutureRestartKernel_apply
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (S : DenseTime) (x : alpha) :
    rationalPastFutureRestartKernel Q S x =
      ((Q x).map (densePastRestriction S)) ⊗ₘ
        Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S) := by
  ext A hA
  rw [rationalPastFutureRestartKernel, Kernel.compProd_apply hA,
    Measure.compProd_apply hA,
    Kernel.map_apply Q (measurable_densePastRestriction S) x]
  congr with history

end
end ContinuousPath

end RationalJointKernel

section RationalRestartFiniteMarginals

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal


noncomputable section

namespace MixedPastFuture

private def restrictPastWithTerminal {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (path : Set.Iic S → alpha) :
    pastWithTerminalFinset S I → alpha :=
  fun r ↦ path ⟨r, le_terminal_of_mem_pastWithTerminalFinset S I r.property⟩

private def restrictPositiveFuture {alpha : Type*} [TopologicalSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : ContinuousPath alpha) : positiveFutureFinset S I → alpha :=
  fun t ↦ path (DenseTime.castOrderEmbedding t)

private def reindexCutPast {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : Fin (pastPredecessorCard S I + 1) → alpha) :
    pastWithTerminalFinset S I → alpha :=
  fun r ↦ path (pastCutOrderIndex S I r)

private def reindexPositiveFuture {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : Fin (positiveFutureFinset S I).card → alpha) :
    positiveFutureFinset S I → alpha :=
  fun t ↦ path (positiveFutureOrderIndex S I t)

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

omit [MetricSpace alpha] [BorelSpace alpha] in
private theorem measurable_restrictPastWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (restrictPastWithTerminal (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply _

private theorem measurable_restrictPositiveFuture (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (restrictPositiveFuture (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro t
  exact ContinuousPath.measurable_coordinateProcess _

omit [MetricSpace alpha] [BorelSpace alpha] in
private theorem measurable_reindexCutPast (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (reindexCutPast (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply _

omit [MetricSpace alpha] [BorelSpace alpha] in
private theorem measurable_reindexPositiveFuture (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (reindexPositiveFuture (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply _

omit [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] in
private theorem restrictPast_terminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (fun z : pastWithTerminalFinset S I → alpha ↦
      z ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩) ∘
        restrictPastWithTerminal S I = ContinuousPath.densePastTerminal S := by
  funext path
  rfl

omit [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] in
private theorem reindexCutPast_terminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (fun z : pastWithTerminalFinset S I → alpha ↦
      z ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩) ∘
        reindexCutPast S I =
      (fun path : Fin (pastPredecessorCard S I + 1) → alpha ↦
        path (Fin.last (pastPredecessorCard S I))) := by
  funext path
  apply congrArg path
  apply (cutPastOrderedPhysicalTimes S I).injective
  rw [cutPastOrderedPhysicalTimes_pastCutOrderIndex,
    cutPastOrderedPhysicalTimes_last]

end MixedPastFuture

namespace SubMarkovKernelSemigroup.IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem map_restrictPastWithTerminal
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    ((continuousPathTrajectory P hP default).map
      (ContinuousPath.densePastRestriction S)).map
        (MixedPastFuture.restrictPastWithTerminal S I) =
      (finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)).map
        (MixedPastFuture.reindexCutPast S I) := by
  rw [← Kernel.map_comp_right]
  · let J := MixedPastFuture.pastWithTerminalFinset S I
    let E : ContinuousPath alpha → denseTimePhysicalSet J → alpha :=
      fun path t ↦ path t
    have hE : Measurable E := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess t
    have hfun :
        MixedPastFuture.restrictPastWithTerminal S I ∘
            ContinuousPath.densePastRestriction S =
          DenseTimePath.pullbackPhysicalSet J ∘ E := by
      funext path r
      rfl
    rw [hfun, Kernel.map_comp_right]
    · rw [continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK J]
      rw [finiteSetKernel_eq_map]
      let e : Fin (MixedPastFuture.pastPredecessorCard S I + 1) ↪o
          Fin (MixedPastFuture.pastPhysicalFinsetWithTerminal S I).card :=
        (Fin.castOrderIso (by
          rw [MixedPastFuture.pastPhysicalFinsetWithTerminal,
            denseTimePhysicalSet, Finset.card_map,
            MixedPastFuture.card_pastWithTerminalFinset])).toOrderEmbedding
      rw [show MixedPastFuture.cutPastOrderedPhysicalTimes S I =
          (finiteSetTimes (MixedPastFuture.pastPhysicalFinsetWithTerminal S I)).restrict e
        from rfl,
        ← hP.finiteTimeKernel_map_restrictPath P _ e,
        ← Kernel.map_comp_right, ← Kernel.map_comp_right]
      · congr 1
      · exact FiniteOrderedTimes.measurable_restrictPath e
      · exact MixedPastFuture.measurable_reindexCutPast S I
      · exact measurable_orderedPathToFiniteSet _
      · exact DenseTimePath.measurable_pullbackPhysicalSet J
    · exact hE
    · exact DenseTimePath.measurable_pullbackPhysicalSet J
  · exact ContinuousPath.measurable_densePastRestriction S
  · exact MixedPastFuture.measurable_restrictPastWithTerminal S I

private theorem map_restrictPositiveFuture
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (continuousPathTrajectory P hP default).map
        (MixedPastFuture.restrictPositiveFuture S I) =
      (finiteTimeKernel P
        (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).map
          (MixedPastFuture.reindexPositiveFuture S I) := by
  let J := MixedPastFuture.positiveFutureFinset S I
  let E : ContinuousPath alpha → denseTimePhysicalSet J → alpha :=
    fun path t ↦ path t
  have hE : Measurable E := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess t
  have hfun : MixedPastFuture.restrictPositiveFuture S I =
      DenseTimePath.pullbackPhysicalSet J ∘ E := by
    funext path t
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [continuousPathTrajectory_map_finiteDenseTimeSet P hP default hK J]
    rw [finiteSetKernel_eq_map]
    let e : Fin (MixedPastFuture.positiveFutureFinset S I).card ↪o
        Fin (denseTimePhysicalSet J).card :=
      (Fin.castOrderIso (by
        simp only [J, denseTimePhysicalSet, Finset.card_map])).toOrderEmbedding
    rw [show MixedPastFuture.positiveFutureOrderedPhysicalTimes S I =
        (finiteSetTimes (denseTimePhysicalSet J)).restrict e from rfl,
      ← hP.finiteTimeKernel_map_restrictPath P _ e,
      ← Kernel.map_comp_right, ← Kernel.map_comp_right]
    · congr 1
    · exact FiniteOrderedTimes.measurable_restrictPath e
    · exact MixedPastFuture.measurable_reindexPositiveFuture S I
    · exact measurable_orderedPathToFiniteSet _
    · exact DenseTimePath.measurable_pullbackPhysicalSet J
  · exact hE
  · exact DenseTimePath.measurable_pullbackPhysicalSet J

omit [CompleteSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem rationalRestart_map_restrict_eq_cutPullback
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (hzero : ∀ x, ∀ᵐ path ∂Q x,
      path (0 : NNReal) = x) :
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (I.restrict ∘ Kernel.finitePastDenseFuture) =
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          Prod.map (MixedPastFuture.restrictPastWithTerminal S I)
            (MixedPastFuture.restrictPositiveFuture S I)) := by
  let F := I.restrict ∘
    Kernel.finitePastDenseFuture (index := Set.Iic S) (alpha := alpha)
  let H := MixedPastFuture.pullbackCutCoordinates (alpha := alpha) S I ∘
    Prod.map (MixedPastFuture.restrictPastWithTerminal S I)
      (MixedPastFuture.restrictPositiveFuture S I)
  have hF : Measurable F :=
    (Finset.measurable_restrict I).comp Kernel.measurable_finitePastDenseFuture
  have hH : Measurable H :=
    (MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
      ((MixedPastFuture.measurable_restrictPastWithTerminal S I).prodMap
        (MixedPastFuture.measurable_restrictPositiveFuture S I))
  change (ContinuousPath.rationalPastFutureRestartKernel Q S).map F =
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map H
  ext x A hA
  rw [Kernel.map_apply' _ hF x hA, Kernel.map_apply' _ hH x hA,
    ContinuousPath.rationalPastFutureRestartKernel,
    Kernel.compProd_apply (hA.preimage hF),
    Kernel.compProd_apply (hA.preimage hH)]
  congr with history
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply']
  apply Filter.EventuallyEq.measure_eq
  filter_upwards [hzero (ContinuousPath.densePastTerminal S history)] with path hpath
  apply congrArg (fun z ↦ z ∈ A)
  funext i
  rcases i with ⟨i, hi⟩
  rcases i with r | t
  ·
      simp [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
        MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
        MixedPastFuture.restrictPastWithTerminal, Prod.map_apply]
  ·
      by_cases ht : t = 0
      · subst t
        have hpath' : path (DenseTime.castOrderEmbedding (0 : DenseTime)) =
            ContinuousPath.densePastTerminal S history := by
          convert hpath using 1
          norm_num [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply]
        simpa [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
          MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
          MixedPastFuture.restrictPastWithTerminal, Prod.map_apply,
          ContinuousPath.densePastTerminal, ContinuousPath.denseRestriction_apply]
          using hpath'
      · simp [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
          MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
          MixedPastFuture.restrictPositiveFuture, Prod.map_apply, ht,
          ContinuousPath.denseRestriction_apply]

/-- Mapping the rational restart kernel to any finite set of mixed past/future coordinates gives
the cut-factorized finite-time kernel, reindexed back to the original mixed labels. -/
theorem rationalPastFutureRestartKernel_map_finitePastDenseFuture_restrict
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (ContinuousPath.rationalPastFutureRestartKernel
      (continuousPathTrajectory P hP default) S).map
        (I.restrict ∘ Kernel.finitePastDenseFuture) =
      ((finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)) ⊗ₖ
        (finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (splitPastTerminal (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            measurable_splitPastTerminal).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.orderedSplitToCutCoordinates S I) := by
  let Q := continuousPathTrajectory P hP default
  let f := MixedPastFuture.restrictPastWithTerminal (alpha := alpha) S I
  let g := MixedPastFuture.restrictPositiveFuture (alpha := alpha) S I
  let terminal' : (MixedPastFuture.pastWithTerminalFinset S I → alpha) → alpha :=
    fun path ↦ path ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩
  have hterminal' : Measurable terminal' := measurable_pi_apply _
  have hcompat : terminal' ∘ f = ContinuousPath.densePastTerminal S :=
    MixedPastFuture.restrictPast_terminal S I
  have hrestartSplit :
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map (Prod.map f g) =
        ((Q.map (ContinuousPath.densePastRestriction S)).map f) ⊗ₖ
          Kernel.prodMkLeft alpha ((Q.map g).comap terminal' hterminal') := by
    rw [ContinuousPath.rationalPastFutureRestartKernel]
    exact Kernel.map_compProd_prodMkLeft_comap
      (Q.map (ContinuousPath.densePastRestriction S)) Q
      (ContinuousPath.densePastTerminal S) terminal' hterminal' f
      (MixedPastFuture.measurable_restrictPastWithTerminal S I) g
      (MixedPastFuture.measurable_restrictPositiveFuture S I) hcompat
  let Kp := finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)
  let Kf := finiteTimeKernel P
    (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)
  let : IsMarkovKernel Kp :=
    hP.isMarkovKernel_finiteTimeKernel P
      (MixedPastFuture.cutPastOrderedPhysicalTimes S I)
  let : IsMarkovKernel Kf :=
    hP.isMarkovKernel_finiteTimeKernel P
      (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)
  let rp := MixedPastFuture.reindexCutPast (alpha := alpha) S I
  let rf := MixedPastFuture.reindexPositiveFuture (alpha := alpha) S I
  let last : (Fin (MixedPastFuture.pastPredecessorCard S I + 1) → alpha) → alpha :=
    fun path ↦ path (Fin.last (MixedPastFuture.pastPredecessorCard S I))
  have hlast : Measurable last := measurable_pi_apply _
  have hrcompat : terminal' ∘ rp = last :=
    MixedPastFuture.reindexCutPast_terminal S I
  have hfactorSplit :
      (Kp ⊗ₖ (Kf.comap
        (splitPastTerminal (alpha := alpha)
          (m := MixedPastFuture.pastPredecessorCard S I))
        measurable_splitPastTerminal)).map
          (MixedPastFuture.orderedSplitToCutCoordinates S I) =
        (Kp.map rp) ⊗ₖ
          Kernel.prodMkLeft alpha ((Kf.map rf).comap terminal' hterminal') := by
    change
      (Kp ⊗ₖ Kernel.prodMkLeft alpha (Kf.comap last hlast)).map
          (Prod.map rp rf) = _
    exact Kernel.map_compProd_prodMkLeft_comap Kp Kf last terminal'
      hterminal' rp (MixedPastFuture.measurable_reindexCutPast S I)
      rf (MixedPastFuture.measurable_reindexPositiveFuture S I) hrcompat
  have hsplit :
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map (Prod.map f g) =
        (Kp ⊗ₖ (Kf.comap
          (splitPastTerminal (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I))
          measurable_splitPastTerminal)).map
            (MixedPastFuture.orderedSplitToCutCoordinates S I) := by
    rw [hrestartSplit,
      map_restrictPastWithTerminal P hP default hK S I,
      map_restrictPositiveFuture P hP default hK S I,
      hfactorSplit]
  have hzero : ∀ x, ∀ᵐ path ∂Q x, path (0 : NNReal) = x := by
    intro x
    let evalZero : ContinuousPath alpha → alpha := fun path ↦ path 0
    have hEvalZero : Measurable evalZero :=
      ContinuousPath.measurable_coordinateProcess 0
    have hmap : Measure.map evalZero (Q x) = Measure.dirac x := by
      have h := congrArg (fun K : Kernel alpha alpha ↦ K x)
        (continuousPathTrajectory_map_eval P hP default hK 0)
      have hcast : DenseTime.castOrderEmbedding (0 : DenseTime) = (0 : NNReal) := by
        norm_num [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply]
      rw [hcast, P.zero] at h
      change (Q.map evalZero) x = Kernel.id x at h
      rw [Kernel.id_apply, Kernel.map_apply Q hEvalZero x] at h
      exact h
    let : IsProbabilityMeasure (Q x) := IsMarkovKernel.isProbabilityMeasure x
    apply (mem_ae_iff_prob_eq_one
      (hEvalZero (MeasurableSet.singleton x))).mpr
    rw [← Measure.map_apply hEvalZero (MeasurableSet.singleton x), hmap]
    simp
  rw [rationalRestart_map_restrict_eq_cutPullback Q S I hzero]
  calc
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘ Prod.map f g) =
      ((ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (Prod.map f g)).map (MixedPastFuture.pullbackCutCoordinates S I) := by
        exact Kernel.map_comp_right _
          ((MixedPastFuture.measurable_restrictPastWithTerminal S I).prodMap
            (MixedPastFuture.measurable_restrictPositiveFuture S I))
          (MixedPastFuture.measurable_pullbackCutCoordinates S I)
    _ = ((Kp ⊗ₖ (Kf.comap
          (splitPastTerminal (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I))
          measurable_splitPastTerminal)).map
            (MixedPastFuture.orderedSplitToCutCoordinates S I)).map
        (MixedPastFuture.pullbackCutCoordinates S I) := by rw [hsplit]
    _ = _ := (Kernel.map_comp_right _
      (MixedPastFuture.measurable_orderedSplitToCutCoordinates S I)
      (MixedPastFuture.measurable_pullbackCutCoordinates S I)).symm

end SubMarkovKernelSemigroup.IsConservative
end

end RationalRestartFiniteMarginals

section RationalJointLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

/-- The complete rational past and shifted future of the canonical continuous trajectory have
the rational restart-kernel law. -/
theorem continuousPathTrajectory_map_densePastRestriction_prod_shift
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) :
    (continuousPathTrajectory P hP default).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      ContinuousPath.rationalPastFutureRestartKernel
        (continuousPathTrajectory P hP default) S := by
  apply Kernel.eq_of_map_finitePastDenseFutureRestriction_eq default
  intro I
  rw [← Kernel.map_comp_right]
  · have hcoordinates :
        (I.restrict ∘ Kernel.finitePastDenseFuture
          (index := Set.Iic S) (alpha := alpha)) ∘ (fun omega ↦
            (ContinuousPath.densePastRestriction S omega,
              ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
          I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S := by
        funext omega
        exact congrArg I.restrict
          (ContinuousPath.finitePastDenseFuture_densePastRestriction_shift S omega)
    rw [hcoordinates]
    rw [continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
      P hP default hK S I]
    rw [finiteSetKernel_map_pullbackAbsolutePhysical_eq_cutFactorized P hP S I]
    exact (rationalPastFutureRestartKernel_map_finitePastDenseFuture_restrict
      P hP default hK S I).symm
  · exact (ContinuousPath.measurable_densePastRestriction S).prodMk
      (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))
  · exact (Finset.measurable_restrict I).comp
      (Kernel.measurable_finitePastDenseFuture
        (index := Set.Iic S) (alpha := alpha))

end
end IsConservative
end SubMarkovKernelSemigroup

end RationalJointLaw

end MarkovProcess
