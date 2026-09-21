/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.CemeterySemigroup
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.DenseTimeTrajectoryMarginals

/-!
# Cemetery marginals of parameterized dense-time trajectories

This file proves a one-time marginal identity.  It makes no simultaneous path-support or
lifetime claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

/-- From a live starting state, every coordinate of the parameterized cemetery trajectory has
zero cemetery mass when the original parameter slices are conservative. -/
theorem parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) (d : D) :
    ((P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota).map
      (fun path ↦ path d)) (theta, Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [parameterizedDenseTimeTrajectory_map_eval, parameterStateKernel_apply,
    cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  have hmass := hP theta (iota d) x
  change P theta (iota d) x Set.univ = 1 at hmass
  rw [hmass]
  exact tsub_self 1

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess
