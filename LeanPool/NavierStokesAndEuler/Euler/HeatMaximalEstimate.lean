/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import LeanPool.NavierStokesAndEuler.Euler.HeatGradientEnergy
import LeanPool.NavierStokesAndEuler.Euler.HeatGradientIntegral
import LeanPool.NavierStokesAndEuler.Euler.SobolevEllipticBound
import Mathlib.Algebra.Order.Star.Real

/-! A genuine L²-time H² estimate for regularized heat solutions, with only L² forcing. -/

@[expose] public section


noncomputable section

namespace EulerHeatMaximalEstimate

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerSobolevHeatGenerator EulerHeatGradientEnergy EulerSobolevEllipticBound EulerTimeLp
  EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual gradient energy is bounded by four times the complete H¹ norm squared. -/
theorem gradientEnergy_bound (u : SobolevSpace period 1) : gradientEnergy period u ≤ 4*‖u‖^2 := by
  unfold gradientEnergy
  calc
    _ ≤ ∑ _i : Fin 4, ‖u‖^2 := Finset.sum_le_sum fun i _ => by
      have h := (value_norm_le period (derivativeOperator period 0 i u)).trans
          (derivativeOperator_bound period i u)
      nlinarith [norm_nonneg (value period (derivativeOperator period 0 i u)), norm_nonneg u]
    _ = _ := by simp

omit [Fact (0 < period)] in
/-- Integrating a continuous scalar upper bound by a constant plus another continuous function. -/
theorem integral_le_constant_add (f g : ℝ → ℝ) (c T : ℝ) (hT : 0 ≤ T)
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ t ∈ Icc 0 T, f t ≤ c + g t) :
    (∫ t in (0 : ℝ)..T, f t) ≤ T*c + ∫ t in (0 : ℝ)..T, g t := by
  have h := intervalIntegral.integral_mono_on hT (hf.intervalIntegrable (μ := volume) 0 T)
    (((continuous_const (y := c)).add hg).intervalIntegrable (μ := volume) 0 T) hfg
  change (∫ t in (0 : ℝ)..T, f t) ≤ ∫ t in (0 : ℝ)..T, c + g t at h
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (hg.intervalIntegrable (μ := volume)
      0 T),
    intervalIntegral.integral_const] at h
  simpa only [sub_zero, smul_eq_mul] using h

/-- The actual pointwise elliptic estimate with the lower Sobolev path norm as a uniform bound. -/
theorem path_H2_point_bound (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) (t :
    ℝ) :
    ‖truncateOperator period 2 (extendPath T hT u t)‖^2 ≤
      ‖(restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        ‖laplacianEvaluation period 3 (by norm_num) (extendPath T hT u t)‖^2 := by
  let low := (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have h := H2_norm_sq_le_laplacian period (extendPath T hT u t)
  have hl := extendPath_norm_le T hT low t
  change ‖restrictOperator period (by norm_num : 1 ≤ 3) (extendPath T hT u t)‖ ≤ ‖low‖ at hl
  change _ ≤ ‖low‖^2 + _
  nlinarith [norm_nonneg (restrictOperator period (by
      norm_num : 1 ≤ 3) (extendPath T hT u t)), norm_nonneg low]

/-- The actual H² time norm is bounded by the H¹ path norm and the genuine Laplacian time integral.
-/
theorem time_H2_elliptic_bound (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    ‖pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 ≤
      T * ‖(restrictOperator period (by
          norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        ∫ t in (0 : ℝ)..T, ‖laplacianEvaluation period 3 (by
            norm_num) (extendPath T hT u t)‖^2 := by
  let high := (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have hhigh : Continuous (fun t => ‖extendPath T hT high t‖^2) :=
    ((extendPath_continuous T hT high).norm).pow 2
  have hLap : Continuous (fun t => ‖laplacianEvaluation period 3 (by
      norm_num) (extendPath T hT u t)‖^2) :=
    (((laplacianEvaluation period 3 (by
        norm_num)).continuous.comp (extendPath_continuous T hT u)).norm).pow 2
  rw [pathLp_norm_sq]
  exact integral_le_constant_add _ _ _ T hT hhigh hLap (fun t _ => path_H2_point_bound period T hT
      u t)

/-- The true heat PDE bounds the full L²-time H² norm by H¹ data and undifferentiated L² forcing. -/
theorem heat_time_H2_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ t ∈ Ioo 0 T, ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t))) t) :
    ‖pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 ≤
      (T + 4*ν⁻¹) * ‖(restrictOperator period (by
          norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        (ν⁻¹)^2 * ‖pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)‖^2
            := by
  let low := (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  let source := (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f
  let L := ∫ t in (0 : ℝ)..T, ‖laplacianEvaluation period 3 (by norm_num) (extendPath T hT u t)‖^2
  have he := heat_laplacian_integral_bound period (extendPath T hT u) (extendPath T hT f) ν 0 T hν
      hT
    (extendPath_continuous T hT u).continuousOn (extendPath_continuous T hT f).continuousOn hd
  have hb := gradientEnergy_bound period (restrictOperator period (by
      norm_num : 1 ≤ 3) (extendPath T hT u 0))
  have hl := extendPath_norm_le T hT low 0
  change ‖restrictOperator period (by norm_num : 1 ≤ 3) (extendPath T hT u 0)‖ ≤ ‖low‖ at hl
  have hinit : gradientEnergy period (restrictOperator period (by
      norm_num : 1 ≤ 3) (extendPath T hT u 0)) ≤ 4*‖low‖^2 := by
    nlinarith [norm_nonneg (restrictOperator period (by
        norm_num : 1 ≤ 3) (extendPath T hT u 0)), norm_nonneg low]
  have hs : (∫ t in (0 : ℝ)..T, ‖value period (extendPath T hT f t)‖^2) = ‖pathLp T hT source‖^2 :=
    (pathLp_norm_sq T hT source).symm
  rw [hs] at he
  have hL : L ≤ 4*ν⁻¹*‖low‖^2 + (ν⁻¹)^2*‖pathLp T hT source‖^2 := by
    calc
      L = ν⁻¹*(ν*L) := by rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      _ ≤ ν⁻¹*(4*‖low‖^2 + ν⁻¹*‖pathLp T hT source‖^2) :=
        mul_le_mul_of_nonneg_left (he.trans (add_le_add hinit le_rfl)) (inv_nonneg.mpr hν.le)
      _ = _ := by ring
  have hb2 := time_H2_elliptic_bound period T hT u
  change _ ≤ T*‖low‖^2 + L at hb2
  change _ ≤ (T+4*ν⁻¹)*‖low‖^2 + (ν⁻¹)^2*‖pathLp T hT source‖^2
  nlinarith

end EulerHeatMaximalEstimate
