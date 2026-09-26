/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.TrajectoryMarginals
public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.DenseTimeTrajectory


/-!
# One-time marginals of parameterized dense-time trajectories

This file identifies every coordinate marginal of the jointly measurable parameterized
trajectory kernel.  No standard-Borel assumption is imposed on the parameter space.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

/-- Every coordinate marginal of the parameterized dense-time trajectory is the jointly
measurable transition kernel at its embedded physical time. -/
theorem parameterizedDenseTimeTrajectory_map_eval
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map (fun path ↦ path d) =
      P.parameterStateKernel (iota d) := by
  let k : ℕ := e.symm d
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : e i = d := by
    change e (e.symm d) = d
    exact e.apply_symm_apply d
  have hfun :
      (fun path : Fin (k + 1) → alpha ↦ path i) ∘
          SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e (k + 1) =
        fun path : D → alpha ↦ path d := by
    funext path
    change path (e i) = path d
    rw [hcoord]
  rw [← hfun, Kernel.map_comp_right]
  · rw [P.parameterizedDenseTimeTrajectory_map_prefix hP e iota (k + 1)]
    apply Kernel.ext
    rintro ⟨theta, x⟩
    rw [Kernel.map_apply _ (measurable_pi_apply i),
      parameterizedDenseTimePrefixKernel_apply, parameterStateKernel_apply]
    let Q := P.toSubMarkovKernelSemigroup theta
    have hmarg :=
      SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_eval
        Q (hP theta) e iota d
    rw [← hfun, Kernel.map_comp_right] at hmarg
    · rw [SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix] at hmarg
      have hx := congrArg (fun K : Kernel alpha alpha ↦ K x) hmarg
      change ((Q.denseTimePrefixKernel e iota (k + 1)).map
        (fun path ↦ path i)) x = Q (iota d) x at hx
      rw [Kernel.map_apply _ (measurable_pi_apply i)] at hx
      simpa only [Q, toSubMarkovKernelSemigroup_apply] using hx
    · exact
        SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e (k + 1)
    · exact measurable_pi_apply i
  · exact
      SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e (k + 1)
  · exact measurable_pi_apply i

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
