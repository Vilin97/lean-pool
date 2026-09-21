/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.CemeterySemigroup
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.TrajectoryMarginals

/-!
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]

/-- Every dense-time coordinate of the cemetery trajectory started from a live state has zero
cemetery mass when the original semigroup is conservative. -/
theorem cemeteryDenseTimeTrajectory_map_eval_alive_delta
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) (x : alpha) :
    ((denseTimeTrajectory P.cemeterySemigroup P.isConservative_cemeterySemigroup e iota).map
        (fun path ↦ path d)) (Cemetery.alive x) {Cemetery.delta} = 0 := by
  rw [denseTimeTrajectory_map_eval]
  rw [cemeterySemigroup_apply, Kernel.cemeteryExtension_alive_singleton_delta]
  rw [hP (iota d) x, tsub_self]

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
