/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTimeShift
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DynkinStopping
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StoppingLtTop

/-!
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The truncated exit time is the generic truncation of the `WithTop`-valued exit time. -/
theorem exitTimeTrunc_eq_truncTime (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    exitTimeTrunc U K omega = StoppingTime.truncTime (exitTimeTop U) K omega := by
  apply WithTop.coe_injective
  rw [coe_exitTimeTrunc, StoppingTime.coe_truncTime]

/-- The truncated exit time, read in `ℝ≥0∞`, is the minimum of the exit time and the horizon. -/
theorem coe_exitTimeTrunc_ennreal (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) = min (exitTime U omega) (K : ℝ≥0∞) :=
  coe_exitTimeTrunc U K omega

/-- Truncations at the natural horizons increase to the exit time. -/
theorem iSup_exitTimeTrunc (U : Set alpha) (omega : ContinuousPath alpha) :
    ⨆ n : ℕ, ((exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) = exitTime U omega := by
  have hmin : ∀ n : ℕ, ((exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) =
      min (exitTime U omega) (n : ℝ≥0∞) := by
    intro n
    rw [coe_exitTimeTrunc_ennreal, ENNReal.coe_natCast]
  simp only [hmin]
  apply le_antisymm
  · exact iSup_le fun n ↦ min_le_left _ _
  · rcases eq_or_ne (exitTime U omega) ⊤ with htop | hne
    · rw [htop]
      simp only [le_top, min_eq_right, ENNReal.iSup_natCast]
    · obtain ⟨n, hn⟩ := exists_nat_ge (exitTime U omega).toNNReal
      refine le_iSup_of_le n (le_of_eq ?_)
      rw [min_eq_left]
      rw [← ENNReal.coe_toNNReal hne, ← ENNReal.coe_natCast, ENNReal.coe_le_coe]
      exact_mod_cast hn

/-- Truncations at the natural horizons are monotone in the horizon. -/
theorem monotone_exitTimeTrunc (U : Set alpha) (omega : ContinuousPath alpha) :
    Monotone fun n : ℕ ↦ ((exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) := by
  intro m n hmn
  simp only [coe_exitTimeTrunc_ennreal, ENNReal.coe_natCast]
  exact min_le_min_left _ (Nat.cast_le.mpr hmn)

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha] in
/-- The truncated exit time is measurable on path space. -/
theorem measurable_coe_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal) :
    Measurable fun omega : ContinuousPath alpha ↦
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp
    (ContinuousPath.measurable_of_isStoppingTime _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))

omit [LocallyCompactSpace alpha] in
/-- The `ℝ≥0∞`-valued expectation of the truncated exit time is the `ofReal` of its real
expectation. -/
theorem lintegral_exitTimeTrunc_eq (hP : P.IsConservative) (U : Set alpha) (hU : IsOpen U)
    (K : NNReal) (x : alpha) :
    ∫⁻ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞)
        ∂(IsConservative.continuousProcess P hP x) =
      ENNReal.ofReal (∫ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x)) := by
  have hmeas : Measurable fun omega : ContinuousPath alpha ↦
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) :=
    measurable_coe_nnreal_real.comp
      (ContinuousPath.measurable_of_isStoppingTime _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))
  have hint : Integrable (fun omega : ContinuousPath alpha ↦
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ))
      (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun omega ↦ ?_)
    rw [Real.norm_of_nonneg NNReal.zero_le_coe]
    exact NNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le U K omega)
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun omega ↦ NNReal.zero_le_coe)]
  refine lintegral_congr fun omega ↦ ?_
  rw [ENNReal.ofReal_coe_nnreal]

/-- **The expected exit time is bounded, without truncation.**  If `L f ≤ -1` on the open set `U`
and `f ≥ m`, then the exit time from `U` has expectation at most `f x - m` from every starting
point, as an `ℝ≥0∞`-valued integral. -/
theorem IsFellerKernelSemigroup.lintegral_exitTime_le (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) {m : ℝ}
    (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) ≤
      ENNReal.ofReal ((f : C₀(alpha, ℝ)) x - m) := by
  have hsup : (fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega) =
      fun omega ↦ ⨆ n : ℕ, ((ContinuousPath.exitTimeTrunc U n omega : NNReal) : ℝ≥0∞) :=
    funext fun omega ↦ (ContinuousPath.iSup_exitTimeTrunc U omega).symm
  rw [hsup, lintegral_iSup (fun n ↦ measurable_coe_exitTimeTrunc U hU n)
    (fun m n hmn omega ↦ ContinuousPath.monotone_exitTimeTrunc U omega hmn)]
  refine iSup_le fun n ↦ ?_
  rw [lintegral_exitTimeTrunc_eq hP U hU n x]
  exact ENNReal.ofReal_le_ofReal (hFeller.integral_exitTimeTrunc_le hP hK f U hU hLf hm n x)

/-- Under the hypotheses of the expected exit time bound, the exit time from `U` is almost surely
finite from every starting point. -/
theorem IsFellerKernelSemigroup.ae_exitTime_lt_top (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) {m : ℝ}
    (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (x : alpha) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x), ContinuousPath.exitTime U omega < ⊤ :=
  ae_lt_top (ContinuousPath.measurable_exitTime U hU)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hFeller.lintegral_exitTime_le hP hK f U hU hLf hm x))

end SubMarkovKernelSemigroup

end MarkovProcess
