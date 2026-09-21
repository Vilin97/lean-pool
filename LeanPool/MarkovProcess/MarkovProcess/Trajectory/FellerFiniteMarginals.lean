/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteDenseApproximationContinuity

/-!
# Arbitrary-time finite marginals of Feller trajectories

This file removes the compact-test convergence premise from the earlier arbitrary-time
finite-marginal reduction. For a conservative Feller kernel semigroup whose dense trajectory has
the stated Kolmogorov control, every finite family of continuous-path coordinates has exactly the
finite-set-kernel law.

The theorem is stated for an arbitrary such semigroup; no particular semigroup is singled out,
and no Hunt-process property is asserted.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace MarkovProcess

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

namespace SubMarkovKernelSemigroup

open IsConservative

variable [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- A conservative Feller trajectory with the required Kolmogorov control has the prescribed
finite-dimensional law at every finite set of nonnegative-real times. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_map_finiteTimeSet
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (I : Finset NNReal) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.finiteEvaluation (fun t : I ↦ (t : NNReal))) =
      finiteSetKernel P I := by
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  apply IsConservative.continuousPathTrajectory_map_finiteTimeSet_of_integral_tendsto
    P hP default hK I q hq
  intro x f
  exact hFeller.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
    hP q hq f x

end SubMarkovKernelSemigroup

end

end MarkovProcess

end PortComputability
