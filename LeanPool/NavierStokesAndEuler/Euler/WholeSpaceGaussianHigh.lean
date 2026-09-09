/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianFields
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The small-time heat remainder from genuine third spatial L² derivatives. -/

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerOrdinarySobolev EulerVectorCalculus
open scoped ContDiff ENNReal RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The heat remainder of one actual spatial derivative is O(ε^(1/4))
times the third spatial L² tensor. No Hölder or heat estimate is assumed. -/
theorem derivative_high_remainder (A : SmoothL2Field V) (j : Fin 3) (x : Space)
    {ε : ℝ} (hε : 0 < ε) :
    ‖fderiv ℝ A.field x (axis j) -
        average ε (A.directionalField (axis j)).field x‖ ≤
      3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ := by
  let D := A.directionalField (axis j)
  let F : ℝ → V := fun t => scaledAverage t D.field x
  let B : ℝ → ℝ := fun t => (3/4:ℝ)*t^(-(3:ℝ)/4)*‖A.jetLp 3‖
  have hc : Continuous F := scaledAverage_continuous D.field D.smooth.continuous
    ‖finiteField D‖ (field_sup_bound D) x
  have hd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      HasDerivAt F ((1/4:ℝ) • secondAverage t D.field x) t :=
    scaledAverage_field_hasDerivAt ht.1 D x
  have hb (t : ℝ) (ht : t ∈ Ioo 0 ε) : ‖deriv F t‖ ≤ B t := by
    rw [(hd t ht).deriv, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
    have h := mul_le_mul_of_nonneg_left (secondAverage_directional_bound ht.1 A j x)
      (by norm_num : (0:ℝ) ≤ 1/4)
    exact h.trans_eq (by dsimp [B]; ring)
  have hbi : IntervalIntegrable B volume 0 ε :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(3:ℝ)/4)).const_mul
      (3/4:ℝ)).mul_const ‖A.jetLp 3‖
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hε.le hc.continuousOn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall hb) hbi
  have he : (∫ t in (0:ℝ)..ε, B t) = 3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ := by
    dsimp [B]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(3:ℝ)/4))]
    rw [show -(3:ℝ)/4+1=(1:ℝ)/4 by norm_num,
      Real.zero_rpow (by norm_num : (1:ℝ)/4 ≠ 0)]
    ring
  rw [he] at h
  change ‖scaledAverage ε D.field x-scaledAverage 0 D.field x‖ ≤ _ at h
  rw [scaledAverage_eq hε, scaledAverage_zero, norm_sub_rev] at h
  exact h

end EulerWholeSpaceGaussian
