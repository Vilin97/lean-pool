/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DenseRestrictionMarginals
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.RationalConditional
import LeanPool.MarkovProcess.MarkovProcess.Time.DenseTimeApproximationFromAbove
import LeanPool.MarkovProcess.MarkovProcess.Path.ShiftCompactTestConvergence
import LeanPool.MarkovProcess.MarkovProcess.Feller.DensePhysicalFiniteSetContinuity
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification
import LeanPool.MarkovProcess.MarkovProcess.Path.MeasureIdentification


/-!
# Event-restricted deterministic restart for the Feller trajectory

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the deterministic-time canonical filtration. The proof approaches the
time strictly from above by dense times, identifies every finite dense future marginal by compact
tests, and then uses measure identification on dense restrictions.

The time here is deterministic. The strong Markov property at a finite stopping time is in
`Trajectory/FellerStoppingRestart.lean`.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

omit [CompleteSpace alpha] [LocallyCompactSpace alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
private theorem map_denseRestriction_restrict_integral
    (nu : Measure (ContinuousPath alpha)) (J : Finset DenseTime)
    (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂((nu.map ContinuousPath.denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (ContinuousPath.denseRestriction omega)) ∂nu := by
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

private theorem composed_denseRestriction_integral
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (r : NNReal) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂(((Kernel.comap (continuousPathTrajectory P hP default)
          (ContinuousPath.coordinateProcess (alpha := alpha) r)
          (ContinuousPath.measurable_coordinateProcess r) ∘ₘ mu).map
        ContinuousPath.denseRestriction).map J.restrict) =
      MeasureTheory.integral mu (fun omega ↦
        MeasureTheory.integral
          (((finiteSetKernel P (denseTimePhysicalSet J)).map
            (DenseTimePath.pullbackPhysicalSet J)) (omega r)) f) := by
  let Q := continuousPathTrajectory P hP default
  let KJ := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  have heval := ContinuousPath.measurable_coordinateProcess (alpha := alpha) r
  have hdense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  have hQJ : (Q.map ContinuousPath.denseRestriction).map J.restrict = KJ := by
    exact IsConservative.continuousPathTrajectory_map_denseRestriction_map_restrict
      P hP default hK J
  have hkernel :
      ((Kernel.comap Q (ContinuousPath.coordinateProcess r) heval).map
          ContinuousPath.denseRestriction).map J.restrict =
        Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval := by
    rw [← Kernel.comap_map_comm Q heval hdense,
      ← Kernel.comap_map_comm (Q.map ContinuousPath.denseRestriction) heval hrestrict,
      hQJ]
  have hmeasure :
      (((Kernel.comap Q (ContinuousPath.coordinateProcess r) heval ∘ₘ mu).map
          ContinuousPath.denseRestriction).map J.restrict) =
        Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu := by
    rw [Measure.map_comp mu _ hdense, Measure.map_comp mu _ hrestrict, hkernel]
  rw [hmeasure, Measure.comp_eq_comp_const_apply]
  let : IsMarkovKernel KJ := by
    dsimp only [KJ]
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsMarkovKernel
      (Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval) := inferInstance
  let : IsFiniteMeasure
      ((Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu)) := inferInstance
  have hfint : Integrable f
      (Kernel.comap KJ (ContinuousPath.coordinateProcess r) heval ∘ₘ mu) :=
    f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hfint
  have hi := Kernel.integral_comp hfint
  simpa only [Kernel.const_apply, Kernel.comap_apply, ContinuousPath.coordinateProcess_apply,
    Q, KJ] using hi

/-- Restricting the Feller trajectory to a deterministic-past event and then shifting gives
the trajectory kernel restarted from the state at that deterministic time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_restrict_map_shift
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (s : NNReal) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A →
        ((((continuousPathTrajectory P hP default) x).restrict A).map
            (ContinuousPath.shift s)) =
          Kernel.comap (continuousPathTrajectory P hP default)
              (ContinuousPath.coordinateProcess (alpha := alpha) s)
              (ContinuousPath.measurable_coordinateProcess s) ∘ₘ
            (((continuousPathTrajectory P hP default) x).restrict A) := by
  intro A hA
  let Q := continuousPathTrajectory P hP default
  let mu := (Q x).restrict A
  obtain ⟨q, _, hqAbove, hq⟩ := exists_denseTime_seq_strictAnti_tendsto s
  have hAq (n : ℕ) : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha)
      (DenseTime.castOrderEmbedding (q n))] A :=
    (ContinuousPath.canonicalFiltration (alpha := alpha)).mono
      (le_of_lt (hqAbove n)) A hA
  have hr (n : ℕ) :
      mu.map (ContinuousPath.shift (DenseTime.castOrderEmbedding (q n))) =
        Kernel.comap Q (ContinuousPath.coordinateProcess (alpha := alpha)
          (DenseTime.castOrderEmbedding (q n)))
          (ContinuousPath.measurable_coordinateProcess
            (DenseTime.castOrderEmbedding (q n))) ∘ₘ mu := by
    exact continuousPathTrajectory_restrict_map_shift_denseTime
      P hP default hK x (q n) A (hAq n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let L : Kernel alpha (J → alpha) :=
    (finiteSetKernel P (denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J)
  let g : alpha → ℝ := fun y ↦ ∫ z, f z ∂L y
  have hg_cont : Continuous g := by
    exact hFeller.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet hP J f
  let C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖
  have hg_bound (y : alpha) : ‖g y‖ ≤ C := by
    exact hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hright := tendsto_integral_continuousPath_eval_of_tendsto
    mu s q hq g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    mu s q hq J f
  have heq (n : ℕ) :
      (∫ omega, f (fun j : J ↦ omega
          (DenseTime.castOrderEmbedding (q n) + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (DenseTime.castOrderEmbedding (q n))) ∂mu := by
    have hm := congrArg (fun rho : Measure (ContinuousPath alpha) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hr n)
    have hi := congrArg (fun rho : Measure (J → alpha) ↦ ∫ z, f z ∂rho) hm
    rw [map_denseRestriction_restrict_integral,
      composed_denseRestriction_integral P hP default hK] at hi
    have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
        f (J.restrict (ContinuousPath.denseRestriction omega))) :=
      (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
        (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
    rw [integral_map
      (ContinuousPath.measurable_shift_fixed
        (DenseTime.castOrderEmbedding (q n))).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [g, L, ContinuousPath.denseRestriction_apply,
      ContinuousPath.shift_apply] using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦ omega (s + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega s) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [map_denseRestriction_restrict_integral,
    composed_denseRestriction_integral P hP default hK]
  have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  rw [integral_map (ContinuousPath.measurable_shift_fixed s).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply,
    ContinuousPath.shift_apply] using! hlimits

end
end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
