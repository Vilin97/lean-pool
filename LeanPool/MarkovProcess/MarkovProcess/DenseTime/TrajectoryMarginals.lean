/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.Trajectory


/-!
# One-time marginals of the dense-time trajectory

This file identifies every coordinate marginal of the dense-time trajectory kernel with the
corresponding transition kernel.  The result is derived from the exact finite-prefix identity.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
private theorem finiteTimeKernel_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    {n : ℕ} (times : FiniteOrderedTimes n) (i : Fin n) :
    (finiteTimeKernel P times).map (fun path ↦ path i) = P (times i) := by
  let select : Fin 1 ↪o Fin n :=
    { toFun := fun _ ↦ i
      inj' := fun a b _ ↦ Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        constructor
        · intro _
          rw [Subsingleton.elim a b]
        · intro _
          exact le_rfl }
  have hfun :
      (fun path : Fin 1 → α ↦ path 0) ∘ FiniteOrderedTimes.restrictPath select =
        fun path : Fin n → α ↦ path i := by
    funext path
    rfl
  rw [← hfun, Kernel.map_comp_right]
  · rw [hP.finiteTimeKernel_map_restrictPath P times select]
    simpa only using! finiteTimeKernel_one_map_eval P (times.restrict select)
  · exact FiniteOrderedTimes.measurable_restrictPath select
  · exact measurable_pi_apply 0

/-- Every coordinate marginal of the dense-time trajectory is the transition kernel at its
embedded physical time. -/
theorem denseTimeTrajectory_map_eval
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (d : D) :
    (denseTimeTrajectory P hP e ι).map (fun path ↦ path d) = P (ι d) := by
  let k : ℕ := e.symm d
  let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcoord : e i = d := by
    change e (e.symm d) = d
    exact e.apply_symm_apply d
  have hfun :
      (fun path : Fin (k + 1) → α ↦ path i) ∘
          denseTimeTrajectoryPrefix e (k + 1) =
        fun path : D → α ↦ path d := by
    funext path
    change path (e i) = path d
    rw [hcoord]
  rw [← hfun, Kernel.map_comp_right]
  · rw [denseTimeTrajectory_map_prefix P hP e ι (k + 1)]
    rw [denseTimePrefixKernel_eq_map, ← Kernel.map_comp_right]
    · have ht : ι (e i) ∈ denseTimePhysicalPrefix e ι (k + 1) := by
        rw [denseTimePhysicalPrefix, Finset.mem_map]
        refine ⟨e i, ?_, rfl⟩
        rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
        exact i.isLt
      let t : denseTimePhysicalPrefix e ι (k + 1) := ⟨ι (e i), ht⟩
      have hprefix :
          (fun path : Fin (k + 1) → α ↦ path i) ∘
              denseTimePrefixReindex e ι (k + 1) =
            fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t := by
        rfl
      rw [hprefix, finiteSetKernel_eq_map, ← Kernel.map_comp_right]
      · let j : Fin (denseTimePhysicalPrefix e ι (k + 1)).card :=
          ((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl).symm t
        have hordered :
            (fun path : denseTimePhysicalPrefix e ι (k + 1) → α ↦ path t) ∘
                orderedPathToFiniteSet (denseTimePhysicalPrefix e ι (k + 1)) =
              fun path : Fin (denseTimePhysicalPrefix e ι (k + 1)).card → α ↦ path j := by
          rfl
        rw [hordered, finiteTimeKernel_map_eval P hP _ j]
        have hjtime :
            finiteSetTimes (denseTimePhysicalPrefix e ι (k + 1)) j = ι (e i) := by
          change ((((denseTimePhysicalPrefix e ι (k + 1)).orderIsoOfFin rfl) j :
            denseTimePhysicalPrefix e ι (k + 1)) : NNReal) = ι (e i)
          dsimp only [j]
          rw [OrderIso.apply_symm_apply]
        rw [hjtime, hcoord]
      · exact measurable_orderedPathToFiniteSet
          (denseTimePhysicalPrefix e ι (k + 1))
      · exact measurable_pi_apply t
    · exact measurable_denseTimePrefixReindex e ι (k + 1)
    · fun_prop
  · exact measurable_denseTimeTrajectoryPrefix e (k + 1)
  · fun_prop

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
