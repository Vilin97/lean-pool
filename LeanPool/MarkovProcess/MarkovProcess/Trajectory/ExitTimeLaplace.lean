/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.Resolvent
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Resolvent
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitLaw


/-!
# The Laplace transform of an exit time

For the continuous-path process of a conservative semigroup, this file identifies the Laplace
transform of the finite exit time from an open set with one minus the killed resolvent of the
constant function one.  It also gives the resulting Chernoff bound on the early-exit event
`{exitTime U ≤ t}`.

Main results: `IsConservative.lintegral_exp_neg_exitTime` and
`IsConservative.measure_exitTime_le_le`.

No moment bound or almost-sure finiteness of the exit time is asserted.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

section

/-- The integral of a decaying exponential over a finite interval. -/
private theorem integral_exp_neg_mul_Ioc_zero (lam : ℝ) (hlam : 0 < lam) (A : ℝ)
    (hA : 0 ≤ A) :
    ∫ t in Set.Ioc (0 : ℝ) A, Real.exp (-lam * t) =
      (1 - Real.exp (-lam * A)) / lam := by
  rw [← intervalIntegral.integral_of_le hA]
  have hn : -lam ≠ 0 := neg_ne_zero.mpr hlam.ne'
  have h := intervalIntegral.integral_comp_mul_left
    (f := Real.exp) (a := 0) (b := A) hn
  rw [mul_zero, integral_exp] at h
  rw [show (fun t : ℝ ↦ Real.exp (-lam * t)) =
      fun t ↦ Real.exp ((-lam) * t) by funext t; rw [neg_mul], h]
  simp only [smul_eq_mul, Real.exp_zero]
  field_simp
  ring

/-- The improper integral of a decaying exponential on the positive half-line. -/
private theorem integral_exp_neg_mul_Ioi_zero (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = lam⁻¹ :=
  Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam

/-- The `ℝ≥0∞` integral of a decaying exponential over a finite interval. -/
private theorem lintegral_exp_neg_mul_Ioc_zero (lam : ℝ) (hlam : 0 < lam) (A : ℝ)
    (hA : 0 ≤ A) :
    ∫⁻ t in Set.Ioc (0 : ℝ) A, ENNReal.ofReal (Real.exp (-lam * t)) =
      ENNReal.ofReal ((1 - Real.exp (-lam * A)) / lam) := by
  rw [← integral_exp_neg_mul_Ioc_zero lam hlam A hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Ioc)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)).symm

/-- The `ℝ≥0∞` integral of a decaying exponential on the positive half-line. -/
private theorem lintegral_exp_neg_mul_Ioi_zero (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) =
      ENNReal.ofReal lam⁻¹ := by
  rw [← integral_exp_neg_mul_Ioi_zero lam hlam]
  exact (ofReal_integral_eq_lintegral_ofReal
    (exp_neg_integrableOn_Ioi 0 hlam)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)).symm

/-- Multiplying the discounted occupation time below an extended horizon by the discount rate
gives one minus the discounted terminal weight, with the latter set to zero at infinity. -/
private theorem ofReal_mul_lintegral_exp_neg_mul_indicator (lam : ℝ) (hlam : 0 < lam)
    (tau : ℝ≥0∞) :
    ENNReal.ofReal lam *
        (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator 1 t) =
      1 - ({tau | tau < ⊤} : Set ℝ≥0∞).indicator
        (fun tau ↦ ENNReal.ofReal (Real.exp (-lam * tau.toReal))) tau := by
  let S : Set ℝ := {t | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}
  have hS : MeasurableSet S := measurableSet_lt
    (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  have hfun : (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) * S.indicator 1 t) =
      S.indicator (fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))) := by
    funext t
    by_cases ht : t ∈ S
    · simp only [neg_mul, Set.indicator_of_mem ht, Pi.one_apply, mul_one]
    · simp only [neg_mul, Set.indicator_of_notMem ht, mul_zero]
  rw [hfun, setLIntegral_indicator hS]
  by_cases htau : tau = ⊤
  · rw [ContinuousPath.survivalSet tau, ite_eq_left htau,
      lintegral_exp_neg_mul_Ioi_zero lam hlam]
    subst tau
    have hnot : (⊤ : ℝ≥0∞) ∉ {tau | tau < ⊤} := by
      simp only [mem_ofPred_eq, lt_self_iff_false, not_false_eq_true]
    rw [Set.indicator_of_notMem hnot, tsub_zero]
    rw [← ENNReal.ofReal_mul hlam.le]
    simp only [mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]
  · rw [ContinuousPath.survivalSet tau, ite_eq_right htau]
    rw [show volume.restrict (Set.Ioo (0 : ℝ) tau.toReal) =
        volume.restrict (Set.Ioc 0 tau.toReal) from
      Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [lintegral_exp_neg_mul_Ioc_zero lam hlam tau.toReal ENNReal.toReal_nonneg]
    have hmem : tau ∈ {tau | tau < ⊤} := lt_top_iff_ne_top.mpr htau
    rw [Set.indicator_of_mem hmem]
    rw [← ENNReal.ofReal_mul hlam.le, mul_div_cancel₀ _ hlam.ne',
      ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed resolvent of one is the expected discounted occupation time before exit. -/
private theorem killedResolvent_one_eq_lintegral (lam : ℝ) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime U omega}.indicator 1 t)
        ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU lam measurable_const x]
  refine lintegral_congr fun omega ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [Set.indicator_apply, Pi.one_apply]

/-- **The Laplace transform of the exit time.**  The discounted mass of paths which leave the
open set in finite time is one minus the discount rate times the killed resolvent of one. -/
theorem IsConservative.lintegral_exp_neg_exitTime (lam : ℝ) (hlam : 0 < lam) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
        ∂(IsConservative.continuousProcess P hP x) =
      1 - ENNReal.ofReal lam *
        IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let S : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := S.indicator fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))
  let H : ContinuousPath alpha → ℝ≥0∞ := fun omega ↦
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega}.indicator 1 t
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  have hS : MeasurableSet S := measurableSet_lt hExit measurable_const
  have hW : Measurable W := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp hExit)))).indicator hS
  have hJoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) *
        {p : ℝ × ContinuousPath alpha |
          ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime U p.2}.indicator 1 p) := by
    have hset : MeasurableSet {p : ℝ × ContinuousPath alpha |
        ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
      measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
        (hExit.comp measurable_snd)
    exact (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul (measurable_const.indicator hset)
  have hH : Measurable H := by
    exact hJoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))
  have hWle : W ≤ fun _ ↦ 1 := by
    intro omega
    by_cases homega : omega ∈ S
    · change S.indicator (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega ≤ 1
      rw [Set.indicator_of_mem homega]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((Real.exp_le_one_iff).mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le) ENNReal.toReal_nonneg))
    · change S.indicator (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega ≤ 1
      rw [Set.indicator_of_notMem homega]
      exact zero_le
  have hWint : ∫⁻ omega, W omega ∂Q ≤ 1 := by
    calc
      ∫⁻ omega, W omega ∂Q ≤ ∫⁻ _omega, 1 ∂Q := lintegral_mono hWle
      _ = 1 := by simp only [lintegral_one, measure_univ]
  have hWtop : ∫⁻ omega, W omega ∂Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hWint
  have hSub : ∫⁻ omega, 1 - W omega ∂Q = 1 - ∫⁻ omega, W omega ∂Q := by
    rw [lintegral_sub hW hWtop (Eventually.of_forall hWle)]
    simp only [lintegral_one, measure_univ]
  change ∫⁻ omega, W omega ∂Q =
    1 - ENNReal.ofReal lam * IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x
  rw [killedResolvent_one_eq_lintegral P hP U hU lam x]
  change ∫⁻ omega, W omega ∂Q = 1 - ENNReal.ofReal lam * ∫⁻ omega, H omega ∂Q
  rw [← lintegral_const_mul _ hH]
  have hKey : (fun omega ↦ ENNReal.ofReal lam * H omega) = fun omega ↦ 1 - W omega := by
    funext omega
    exact ofReal_mul_lintegral_exp_neg_mul_indicator lam hlam
      (ContinuousPath.exitTime U omega)
  rw [hKey, hSub]
  exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top hWint).symm

include hU in
/-- The early-exit event satisfies a Chernoff bound by the discounted finite-exit mass. -/
theorem IsConservative.measure_exitTime_le_le (lam : ℝ) (hlam : 0 ≤ lam)
    (t : NNReal) (x : alpha) :
    IsConservative.continuousProcess P hP x
        {omega | ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) *
        ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦ ENNReal.ofReal
            (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let A : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞)}
  let S : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := S.indicator fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  have hA : MeasurableSet A := measurableSet_le hExit measurable_const
  have hS : MeasurableSet S := measurableSet_lt hExit measurable_const
  have hW : Measurable W := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp hExit)))).indicator hS
  change Q A ≤ ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * ∫⁻ omega, W omega ∂Q
  rw [← lintegral_indicator_one hA, ← lintegral_const_mul _ hW]
  refine lintegral_mono fun omega ↦ ?_
  by_cases homega : omega ∈ A
  · rw [Set.indicator_of_mem homega]
    have htauTop : ContinuousPath.exitTime U omega ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top homega
    have homegaS : omega ∈ S := lt_top_iff_ne_top.mpr htauTop
    change 1 ≤ ENNReal.ofReal (Real.exp (lam * (t : ℝ))) *
      S.indicator (fun omega ↦ ENNReal.ofReal
        (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
    rw [Set.indicator_of_mem homegaS, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    have htau : (ContinuousPath.exitTime U omega).toReal ≤ (t : ℝ) := by
      exact (ENNReal.toReal_le_toReal htauTop ENNReal.coe_ne_top).mpr homega
    calc
      0 ≤ lam * ((t : ℝ) - (ContinuousPath.exitTime U omega).toReal) :=
        mul_nonneg hlam (sub_nonneg.mpr htau)
      _ = lam * (t : ℝ) + -lam * (ContinuousPath.exitTime U omega).toReal := by ring
  · rw [Set.indicator_of_notMem homega]
    exact zero_le

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
