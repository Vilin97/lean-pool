/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import LeanPool.MarkovProcess.MarkovProcess.Kernel.KernelSemigroup

/-!
# Trajectory laws on a fixed ordered time grid

This file applies the Ionescu--Tulcea theorem to a conservative sub-Markov
kernel semigroup on one fixed nondecreasing `NNReal`-valued time grid.  The
result is only a discrete trajectory law on `ℕ → α` for that grid.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- A fixed nondecreasing grid of nonnegative times. -/
structure OrderedGrid where
  /-- The time assigned to each discrete index. -/
  time : ℕ → NNReal
  /-- Grid times are nondecreasing. -/
  monotone_time : Monotone time

namespace OrderedGrid

/-- The time increment from index `n` to index `n + 1`. -/
def increment (grid : OrderedGrid) (n : ℕ) : NNReal :=
  grid.time (n + 1) - grid.time n

end OrderedGrid

/-- The singleton history at index zero determined by a starting state. -/
def initialHistory (x : α) : Finset.Iic 0 → α :=
  fun _ => x

/-- The singleton-history map is measurable. -/
theorem measurable_initialHistory : Measurable (initialHistory : α → Finset.Iic 0 → α) :=
  measurable_pi_iff.mpr fun _ => measurable_id

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

private def lastIndex (n : ℕ) : Finset.Iic n :=
  ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The history-dependent Ionescu--Tulcea step kernel on `grid`.

Only the current state, the last coordinate of the supplied history, is used.
-/
def orderedGridStepKernel (grid : OrderedGrid) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  (P (grid.increment n)).comap
    (fun history => history (lastIndex n))
    (measurable_pi_apply (lastIndex n))

/-- Conservativity makes every ordered-grid step kernel a Markov kernel. -/
theorem IsConservative.isMarkovKernel_orderedGridStepKernel
    (hP : P.IsConservative) (grid : OrderedGrid) (n : ℕ) :
    IsMarkovKernel (orderedGridStepKernel P grid n) := by
  let : IsMarkovKernel (P (grid.increment n)) := hP.isMarkovKernel (grid.increment n)
  rw [orderedGridStepKernel]
  infer_instance

/-- The Ionescu--Tulcea kernel from a starting state to trajectories on one
fixed ordered grid. -/
noncomputable def orderedGridTrajectoryKernel
    (hP : P.IsConservative) (grid : OrderedGrid) : Kernel α (ℕ → α) := by
  letI (n : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid n) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid n
  exact (Kernel.traj (orderedGridStepKernel P grid) 0).comap
    initialHistory measurable_initialHistory

/-- The ordered-grid trajectory kernel is a Markov kernel. -/
theorem IsConservative.isMarkovKernel_orderedGridTrajectoryKernel
    (hP : P.IsConservative) (grid : OrderedGrid) :
    IsMarkovKernel (orderedGridTrajectoryKernel P hP grid) := by
  let (n : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid n) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid n
  rw [orderedGridTrajectoryKernel]
  infer_instance

/-- The trajectory law on one fixed ordered grid, started from `x`. -/
noncomputable def orderedGridTrajectoryLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) : Measure (ℕ → α) :=
  orderedGridTrajectoryKernel P hP grid x

/-- The ordered-grid trajectory law is a probability measure. -/
theorem IsConservative.isProbabilityMeasure_orderedGridTrajectoryLaw
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    IsProbabilityMeasure (orderedGridTrajectoryLaw P hP grid x) := by
  let : IsMarkovKernel (orderedGridTrajectoryKernel P hP grid) :=
    IsConservative.isMarkovKernel_orderedGridTrajectoryKernel P hP grid
  exact IsMarkovKernel.isProbabilityMeasure x

/-- Every finite prefix of the ordered-grid law is the corresponding finite
Ionescu--Tulcea trajectory law. -/
theorem IsConservative.orderedGridTrajectoryLaw_map_frestrictLe
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) (n : ℕ) :
    (orderedGridTrajectoryLaw P hP grid x).map
        (fun path : ℕ → α => fun i : Finset.Iic n => path i) =
      Kernel.partialTraj (X := fun _ => α) (orderedGridStepKernel P grid) 0 n
        (initialHistory x) := by
  let (k : ℕ) : IsMarkovKernel (orderedGridStepKernel P grid k) :=
    IsConservative.isMarkovKernel_orderedGridStepKernel P hP grid k
  exact Kernel.traj_map_frestrictLe_apply
    (X := fun _ => α) (κ := orderedGridStepKernel P grid) 0 n (initialHistory x)

/-- The prefix consisting of the zeroth coordinate is the deterministic
singleton history at the starting state. -/
theorem IsConservative.orderedGridTrajectoryLaw_map_frestrictLe_zero
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    (orderedGridTrajectoryLaw P hP grid x).map
        (fun path : ℕ → α => fun i : Finset.Iic 0 => path i) =
      Measure.dirac (initialHistory x) := by
  simpa only [Kernel.partialTraj_self, Kernel.id_apply] using
    IsConservative.orderedGridTrajectoryLaw_map_frestrictLe P hP grid x 0

end SubMarkovKernelSemigroup

end MarkovProcess
