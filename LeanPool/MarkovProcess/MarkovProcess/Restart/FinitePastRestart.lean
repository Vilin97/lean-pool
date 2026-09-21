/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.KernelIdentification
import LeanPool.MarkovProcess.MarkovProcess.Kernel.FiniteRestrictionIdentification

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Encode a finite-coordinate past and the dense restriction of a continuous future as one path
indexed by the disjoint union of the past and future coordinate types. -/
def finitePastDenseFuture
    (z : (index → alpha) × ContinuousPath alpha) : index ⊕ DenseTime → alpha
  | Sum.inl i => z.1 i
  | Sum.inr t => ContinuousPath.denseRestriction z.2 t

omit [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)] in
theorem measurable_finitePastDenseFuture :
    Measurable (finitePastDenseFuture (index := index) (alpha := alpha)) := by
  rw [measurable_pi_iff]
  rintro (i | t)
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply t).comp
      (ContinuousPath.measurable_denseRestriction.comp measurable_snd)

private def finitePastContinuousFuture
    (default : ContinuousPath alpha) (z : index ⊕ DenseTime → alpha) :
    (index → alpha) × ContinuousPath alpha :=
  (fun i ↦ z (Sum.inl i),
    ContinuousPath.continuousExtension default (fun t ↦ z (Sum.inr t)))

private theorem measurable_finitePastContinuousFuture (default : ContinuousPath alpha) :
    Measurable (finitePastContinuousFuture (index := index) (alpha := alpha) default) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (Sum.inl i)
  · exact ContinuousPath.measurable_continuousExtension default |>.comp
      (measurable_pi_iff.mpr fun t ↦ measurable_pi_apply (Sum.inr t))

omit [MeasurableSpace alpha] [BorelSpace alpha]
  [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)] in
private theorem finitePastContinuousFuture_comp_finitePastDenseFuture
    (default : ContinuousPath alpha) :
    finitePastContinuousFuture (index := index) default ∘
        finitePastDenseFuture (index := index) (alpha := alpha) = id := by
  funext z
  apply Prod.ext
  · funext i
    rfl
  · exact ContinuousPath.continuousExtension_denseRestriction default z.2

/-- Two finite kernels on a finite-past/continuous-future space agree if every joint finite
coordinate restriction agrees.  The finite set may contain coordinates from both the past and
future summands; retaining only future coordinates would not determine their dependence. -/
theorem eq_of_map_finitePastDenseFutureRestriction_eq
    (default : ContinuousPath alpha)
    (kappa eta : Kernel beta ((index → alpha) × ContinuousPath alpha))
    [IsFiniteKernel kappa]
    (h : ∀ I : Finset (index ⊕ DenseTime),
      kappa.map (I.restrict ∘ finitePastDenseFuture) =
        eta.map (I.restrict ∘ finitePastDenseFuture)) :
    kappa = eta := by
  have hDense :
      kappa.map finitePastDenseFuture = eta.map finitePastDenseFuture := by
    apply eq_of_map_finiteRestriction_eq
    intro I
    rw [← Kernel.map_comp_right kappa measurable_finitePastDenseFuture
        (Finset.measurable_restrict I),
      ← Kernel.map_comp_right eta measurable_finitePastDenseFuture
        (Finset.measurable_restrict I)]
    exact h I
  calc
    kappa = (kappa.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default
    _ = (eta.map finitePastDenseFuture).map
        (finitePastContinuousFuture (index := index) default) := by rw [hDense]
    _ = eta := by
      rw [← Kernel.map_comp_right]
      · rw [finitePastContinuousFuture_comp_finitePastDenseFuture, Kernel.map_id]
      · exact measurable_finitePastDenseFuture
      · exact measurable_finitePastContinuousFuture default

end
end Kernel
end MarkovProcess
