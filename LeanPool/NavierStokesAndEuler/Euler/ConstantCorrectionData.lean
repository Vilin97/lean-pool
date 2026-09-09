/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftBudget
public import LeanPool.NavierStokesAndEuler.Euler.GevreyUniformConstants

@[expose] public section

/-! Actual constant coefficient towers for the ordinary Euler correction
equation: identity pressure metric, zero lower-order coefficients, spatial
scale one and angular direction zero. No solution is included in the data. -/

noncomputable section

namespace EulerConstantCorrection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerAllOrderCorrectionData EulerCorrectionEnergyData EulerJetProductBounds
  EulerH6Pressure EulerSobolevGevreyOperators EulerMetricTransport
  EulerTransportDerivatives EulerGevreyUniformConstants EulerEnergyMetricPaths
  EulerVolterraConvolution
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (LiftTangent →L[ℝ] Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (LiftTangent →L[ℝ] Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (LiftTangent →L[ℝ] LiftTangent →L[ℝ] Space →L[ℝ] Space)
  := inferInstance
private local instance : NormedSpace ℝ (LiftTangent →L[ℝ] LiftTangent →L[ℝ] Space →L[ℝ] Space) :=
  inferInstance

def coefficient (A : Space →L[ℝ] Space) : SmoothCoefficient P where
  coefficient _ := A
  smooth _ := contDiff_const
  bound := ‖A‖₊
  norm_bound _ := le_rfl
  firstBound := 0
  norm_first _ := by
    change ‖fderiv ℝ (fun _ : LiftTangent => A) 0‖ ≤ 0
    simp only [fderiv_const_apply,norm_zero,le_refl]
  secondBound := 0
  norm_second _ y := by
    change ‖fderiv ℝ (fderiv ℝ (fun _ : LiftTangent => A)) y‖ ≤ 0
    simp only [fderiv_fun_const,fderiv_zero,Pi.zero_apply,norm_zero,le_refl]

def jet (A : Space →L[ℝ] Space) :
    (q : ℕ) → EulerSpatialSobolevInverse.CoefficientJet P standardDirection q (coefficient P A)
  | 0 => .zero _
  | q+1 => .succ (fun _ => coefficient P 0) (fun _ => jet 0 q)
      (fun i _ => by
        change (0 : Space →L[ℝ] Space)=(fderiv ℝ (fun _ : LiftTangent => A) 0) (standardDirection i)
        simp)

omit [Fact (0 < P)] in
theorem jet_boundLevel (A : Space →L[ℝ] Space) (q r : ℕ) :
    boundLevel P (jet P A q) r = if r=0 then ‖A‖ else 0 := by
  induction q generalizing A r with
  | zero => cases r <;> simp [jet,boundLevel,coefficient]
  | succ q ih =>
    cases r with
    | zero => simp [jet, boundLevel, coefficient]
    | succ r =>
      simp only [jet]
      rw [boundLevel]
      simp [ih]

omit [Fact (0 < P)] in
theorem jet_zero_coefficientBlock (q b n : ℕ) :
    coefficientBlock P (jet P (0 : Space →L[ℝ] Space) q) b n=0 := by
  simp only [coefficientBlock,jet_boundLevel,norm_zero,ite_self,Finset.sum_const_zero,mul_zero]

omit [Fact (0 < P)] in
theorem jet_positive_coefficientBlock (A : Space →L[ℝ] Space) (q b n : ℕ) (hn : 0 < n) :
    coefficientBlock P (jet P A q) b n=0 := by
  unfold coefficientBlock
  have hz (r : ℕ) : boundLevel P (jet P A q) (n+r)=0 := by
    rw [jet_boundLevel,ite_eq_right (by omega)]
  simp only [hz,Finset.sum_const_zero,mul_zero]

omit [Fact (0 < P)] in
theorem jet_zero_weightedCoefficient (q b N : ℕ) (ρ : ℝ) :
    weightedCoefficient P (jet P (0 : Space →L[ℝ] Space) q) b N ρ=0 := by
  simp only [weightedCoefficient,jet_zero_coefficientBlock,mul_zero,Finset.sum_const_zero]

theorem coefficient_operator_id :
    (coefficient P (ContinuousLinearMap.id ℝ Space)).operator=ContinuousLinearMap.id ℝ (LiftL2 P)
      := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(coefficient P (ContinuousLinearMap.id ℝ Space)).operator_ae u] with x hx
  exact hx

theorem coefficient_operator_zero :
    (coefficient P (0 : Space →L[ℝ] Space)).operator=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(coefficient P (0 : Space →L[ℝ] Space)).operator_ae u,
    Lp.coeFn_zero Space 2 (liftMeasure P)] with x hx hz
  exact hx.trans hz.symm

def tower (T : ℝ) (A : Space →L[ℝ] Space) : CoefficientTower P T where
  coefficient _ := coefficient P A
  jet q _ := jet P A q
  continuous _ := continuous_const

def data {T : ℝ} (F R : FieldTower P T) : EulerAllOrderCorrectionData.Data P T where
  κ := 1
  direction := 0
  scale_bound := by norm_num
  direction_bound := by simp only [norm_zero,zero_le_one]
  metric := tower P T (ContinuousLinearMap.id ℝ Space)
  metric_continuous := by
    change Continuous (fun _ : Icc (0 : ℝ) T => (coefficient P (ContinuousLinearMap.id ℝ
      Space)).operator)
    exact continuous_const
  coercivity := 1
  coercivity_pos := zero_lt_one
  metric_pos _ _ v := by
    change 1*‖v‖^2 ≤ ⟪v,v⟫_ℝ
    simp only [one_mul,real_inner_self_eq_norm_sq,le_refl]
  linear := tower P T 0
  quadratic _ := tower P T 0
  approximation := F
  residual := R

def metricBudget {T : ℝ} (hT : 0 ≤ T) (F R : FieldTower P T) :
    MetricBudget P T hT ((data P F R).atOrder P 1) where
  metric _ := coefficient P (ContinuousLinearMap.id ℝ Space)
  continuous := continuous_const
  derivative := 0
  hasDeriv t _ := by
    change HasDerivAt (fun _ => (coefficient P (ContinuousLinearMap.id ℝ Space)).operator) 0 t
    exact hasDerivAt_const t _
  c := 1
  c_pos := zero_lt_one
  symmetric _ _ _ _ := rfl
  coercive _ _ v := by simp only
    [coefficient,id_apply,one_pow,one_mul,real_inner_self_eq_norm_sq,le_refl]
  inverse _ _ v := by change v=v; rfl
  bound := 1
  first := 0
  time := 0
  bound_nonneg := zero_le_one
  first_nonneg := le_rfl
  time_nonneg := le_rfl
  bound_le _ := by simp only [coefficient,coe_nnnorm]; exact norm_id_le
  first_le _ := le_rfl
  time_le _ := by simp only [ContinuousMap.zero_apply,norm_zero,le_refl]

def pressureBound : ℝ := 9^729

theorem pressureBound_one_le : 1 ≤ pressureBound :=
  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)

omit [Fact (0 < P)] in
theorem identity_base (q r : ℕ) :
    boundLevel P (jet P (ContinuousLinearMap.id ℝ Space) q) r ≤ 1 := by
  rw [jet_boundLevel]
  split_ifs
  · exact norm_id_le
  · exact zero_le_one

omit [Fact (0 < P)] in
theorem identity_pressure (q : ℕ) (hq : 6 ≤ q) :
    (EulerH6Pressure.CoefficientJet.restrict (jet P (ContinuousLinearMap.id ℝ Space) q)
      5 (by omega)).pressureConstant 1 ≤ pressureBound ∧
    (EulerH6Pressure.CoefficientJet.restrict (jet P (ContinuousLinearMap.id ℝ Space) q)
      6 hq).pressureConstant 1 ≤ pressureBound := by
  simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq
    (jet P (ContinuousLinearMap.id ℝ Space) q) 1 1 zero_lt_one le_rfl (by norm_num)
    (fun r _ => identity_base P q r)

end EulerConstantCorrection
