/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.KillAtExit
public import LeanPool.MarkovProcess.MarkovProcess.Killed.Semigroup


/-!
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath

/-- Reading a lifetime path at a family of fixed times is measurable. -/
theorem measurable_coordinateFamily {beta : Type*} [TopologicalSpace beta]
    [MeasurableSpace beta] {iota : Type*} (tau : iota → NNReal) :
    Measurable fun omega : LifetimePath beta ↦ fun i ↦ coordinate (tau i) omega :=
  Measurable.of_eval fun i ↦ measurable_coordinate (tau i)

end LifetimePath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- **The process killed at the exit of `U`.**  The continuous-path process of `P`, started at a
point of the open set `U` and killed when it leaves `U`, as a law on lifetime paths in the
carrier `U`. -/
noncomputable def IsConservative.killedProcess : Kernel U (LifetimePath U) :=
  Kernel.mapOfMeasurable
    ((IsConservative.continuousProcess P hP).comap Subtype.val measurable_subtype_coe)
    (ContinuousPath.killAtExit U) (ContinuousPath.measurable_killAtExit U hU)

/-- The killed process is the image of the continuous-path process under killing at the exit
time, pulled back to the carrier `U`. -/
theorem IsConservative.killedProcess_eq_map :
    IsConservative.killedProcess P hP U hU =
      ((IsConservative.continuousProcess P hP).comap Subtype.val measurable_subtype_coe).map
        (ContinuousPath.killAtExit U) :=
  Kernel.mapOfMeasurable_eq_map _ (ContinuousPath.measurable_killAtExit U hU)

/-- The killed process is a Markov kernel: killing loses no mass, it only moves it to the
cemetery. -/
instance IsConservative.isMarkovKernel_killedProcess :
    IsMarkovKernel (IsConservative.killedProcess P hP U hU) := by
  rw [IsConservative.killedProcess_eq_map]
  exact Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_killAtExit U hU)

/-- The killed process started at `x ∈ U` is the law of the process started at `x`, pushed forward
by killing at the exit time of `U`. -/
theorem IsConservative.killedProcess_apply (x : U) :
    IsConservative.killedProcess P hP U hU x =
      (IsConservative.continuousProcess P hP (x : alpha)).map (ContinuousPath.killAtExit U) := by
  rw [IsConservative.killedProcess_eq_map,
    Kernel.map_apply _ (ContinuousPath.measurable_killAtExit U hU), Kernel.comap_apply]

/-- **The lifetime law of the killed process is the law of the exit time.** -/
theorem IsConservative.killedProcess_map_lifetime (x : U) :
    (IsConservative.killedProcess P hP U hU x).map LifetimePath.lifetime =
      (IsConservative.continuousProcess P hP (x : alpha)).map (ContinuousPath.exitTime U) := by
  rw [IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map LifetimePath.measurable_lifetime
      (ContinuousPath.measurable_killAtExit U hU)]
  rfl

/-- The law of the killed process, read through the coordinate at a fixed time. -/
theorem IsConservative.killedProcess_map_coordinate_eq (t : NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map (LifetimePath.coordinate t) =
      (IsConservative.continuousProcess P hP (x : alpha)).map
        (fun omega ↦ LifetimePath.coordinate t (ContinuousPath.killAtExit U omega)) := by
  rw [IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map (LifetimePath.measurable_coordinate t)
      (ContinuousPath.measurable_killAtExit U hU)]
  rfl

/-- The total mass of the killed transition kernel on `U` is the survival probability. -/
theorem IsConservative.killedKernelOn_univ_eq_continuousProcess (t : NNReal) (x : U) :
    IsConservative.killedKernelOn P hP U hU t x Set.univ =
      IsConservative.continuousProcess P hP (x : alpha)
        {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} := by
  have hsum : IsConservative.killedKernel P hP U hU t (x : alpha) U +
      IsConservative.killedKernel P hP U hU t (x : alpha) Uᶜ =
        IsConservative.killedKernel P hP U hU t (x : alpha) Set.univ :=
    measure_add_measure_compl hU.measurableSet
  rw [IsConservative.killedKernel_apply_compl P hP U hU t (x : alpha), add_zero,
    IsConservative.killedKernel_apply_univ P hP U hU t (x : alpha)] at hsum
  rw [IsConservative.killedKernelOn_apply_univ P hP U hU t x, hsum]

/-- **The one-time marginal of the killed process.**  At every fixed time the coordinate of the
killed process has the law of the cemetery extension of the killed transition kernel on `U`: the
live part is the killed kernel `killedKernelOn P hP U hU t x`, and the cemetery carries the mass
`1 - Q x {t < τ_U}` lost by time `t`. -/
theorem IsConservative.killedProcess_map_coordinate (t : NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension (IsConservative.killedKernelOn P hP U hU t)
        (Cemetery.alive x) := by
  rw [IsConservative.killedProcess_map_coordinate_eq P hP U hU t x]
  refine Measure.ext fun S hS ↦ ?_
  have hC : MeasurableSet (Cemetery.alive ⁻¹' S : Set U) := measurable_inl hS
  have hlive : IsConservative.continuousProcess P hP (x : alpha) {omega : ContinuousPath alpha |
      (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
      omega t ∈ Subtype.val '' (Cemetery.alive ⁻¹' S)} =
      IsConservative.killedKernelOn P hP U hU t x (Cemetery.alive ⁻¹' S) :=
    (IsConservative.killedKernelOn_apply_eq_continuousProcess P hP U hU t x hC).symm
  have hdead : IsConservative.continuousProcess P hP (x : alpha) {omega : ContinuousPath alpha |
      ¬ (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} =
      1 - IsConservative.killedKernelOn P hP U hU t x Set.univ := by
    rw [IsConservative.killedKernelOn_univ_eq_continuousProcess P hP U hU t x]
    exact prob_compl_eq_one_sub (ContinuousPath.measurableSet_lt_exitTime U hU t)
  rw [Measure.map_apply (ContinuousPath.measurable_coordinate_killAtExit U hU t) hS,
    Kernel.cemeteryExtension_alive_apply' _ x hS]
  by_cases hdelta : (Cemetery.delta : Cemetery U) ∈ S
  · rw [ContinuousPath.preimage_coordinate_killAtExit_of_mem U t hdelta,
      Set.indicator_of_mem hdelta, Pi.one_apply, mul_one]
    have hdisj : Disjoint
        {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
          omega t ∈ Subtype.val '' (Cemetery.alive ⁻¹' S)}
        {omega : ContinuousPath alpha | ¬ (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} :=
      Set.disjoint_left.mpr fun omega homega hbad ↦ hbad homega.1
    rw [measure_union hdisj
      ((ContinuousPath.measurableSet_lt_exitTime U hU t).compl), hlive, hdead]
  · rw [ContinuousPath.preimage_coordinate_killAtExit_of_notMem U t hdelta,
      Set.indicator_of_notMem hdelta, mul_zero, add_zero, hlive]

end SubMarkovKernelSemigroup

end MarkovProcess
