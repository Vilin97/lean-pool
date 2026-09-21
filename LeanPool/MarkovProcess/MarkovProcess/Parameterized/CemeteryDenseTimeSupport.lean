/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.CemeteryDenseTimeMarginals

/-!
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section

/-- A cemetery-valued path is live at every point of its index set. -/
def IsLiveAtEveryTime {D alpha : Type*} (path : D → Cemetery alpha) : Prop :=
  ∀ d, path d ≠ Cemetery.delta

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

/-- From a live starting state, the parameterized cemetery trajectory is almost surely live at
all enumerated dense times simultaneously. -/
theorem ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    ∀ᵐ path ∂P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x),
      IsLiveAtEveryTime path := by
  let mu := P.cemeterySemigroup.parameterizedDenseTimeTrajectory
    P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x)
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery alpha)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr :
        MeasurableSet (Set.range (Sum.inr : Unit → alpha ⊕ Unit)))
  have hcoordinate : ∀ n : ℕ, ∀ᵐ path ∂mu, path (e n) ≠ Cemetery.delta := by
    intro n
    have hzero :=
      P.parameterizedCemeteryDenseTimeTrajectory_map_eval_singleton_delta
        hP e iota theta x (e n)
    rw [Kernel.map_apply _ (measurable_pi_apply (e n)),
      Measure.map_apply (measurable_pi_apply (e n)) hdelta] at hzero
    rw [ae_iff]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, not_ne_iff] using! hzero
  filter_upwards [ae_all_iff.mpr hcoordinate] with path hpath
  intro d
  simpa only [e.apply_symm_apply] using hpath (e.symm d)

end ParameterizedSubMarkovKernelSemigroup

end
end MarkovProcess
