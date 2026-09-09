/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Integration in time for the heat-kernel Hessian

The reciprocal substitution reduces the inverse-time Gaussian integrals to
the ordinary Gamma integral. These estimates are uniform in the spatial
indices and give the inverse-cube kernel bound in three dimensions.
-/


noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem inverseTimeGamma_transform (a p s : ℝ) (hs : 0 < s) :
    (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
        ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) =
      s ^ (-(p + 1)) * Real.exp (-a / s) := by
  norm_num only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul hs.le, ← mul_assoc, ← Real.rpow_add hs]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    simp only [div_eq_mul_inv, neg_mul]

/-- The inverse-time Gaussian power is integrable for every positive shape
parameter and positive spatial scale. -/
theorem integrableOn_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    IntegrableOn (fun s : ℝ => s ^ (-(p + 1)) * Real.exp (-a / s)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
      (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := p - 1) (b := a) (by linarith) (by norm_num) ha)
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
    (p := (-1 : ℝ)) (by norm_num)).mpr hg
  exact h.congr_fun (fun s hs => inverseTimeGamma_transform a p s hs) measurableSet_Ioi

/-- Reciprocal substitution evaluates the inverse-time Gamma integral. -/
theorem integral_inverseTimeGamma {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
      a ^ (-p) * Real.Gamma p := by
  calc
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-a / s)) =
        ∫ s : ℝ in Ioi 0, (|(-1 : ℝ)| * s ^ ((-1 : ℝ) - 1)) •
          ((s ^ (-1 : ℝ)) ^ (p - 1) * Real.exp (-(a * s ^ (-1 : ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact (inverseTimeGamma_transform a p s hs).symm
    _ = ∫ t : ℝ in Ioi 0, t ^ (p - 1) * Real.exp (-(a * t)) :=
      integral_comp_rpow_Ioi (fun t : ℝ => t ^ (p - 1) * Real.exp (-(a * t)))
        (by norm_num : (-1 : ℝ) ≠ 0)
    _ = (1 / a) ^ p * Real.Gamma p :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hp ha
    _ = a ^ (-p) * Real.Gamma p := by
      rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]

private theorem square_quarter_rpow (r p : ℝ) (hr : 0 < r) :
    (r ^ 2 / 4) ^ (-p) = 4 ^ p * r ^ (-2 * p) := by
  rw [Real.div_rpow (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul]
  convert! mul_comm (r ^ ((2 : ℝ) * -p)) (4 ^ p) using 1
  congr 1
  ring_nf

/-- The scale occurring in the heat kernel gives the expected homogeneous
power after integration in time. -/
theorem integral_inverseTimeGamma_square_scale {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    (∫ s : ℝ in Ioi 0, s ^ (-(p + 1)) * Real.exp (-(r ^ 2 / 4) / s)) =
      4 ^ p * r ^ (-2 * p) * Real.Gamma p := by
  rw [integral_inverseTimeGamma (by positivity) hp, square_quarter_rpow r p hr]

/-- A common, nonnegative majorant of the nine coordinate Hessians. -/
def heatKernelSecondTimeEnvelope (r s : ℝ) : ℝ :=
  (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
    (r ^ 2 / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) * Real.exp (-(r ^ 2 / 4) / s)) +
      1 / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) * Real.exp (-(r ^ 2 / 4) / s)))

/-- One universal constant for the time-integrated three dimensional heat
kernel Hessian. Its exact value is immaterial to the commutator estimate. -/
def heatKernelTimeConstant : ℝ :=
  (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
    (4 ^ (5 / 2 : ℝ) / 4 * Real.Gamma (5 / 2) +
      4 ^ (3 / 2 : ℝ) / 2 * Real.Gamma (3 / 2))

theorem heatKernelTimeConstant_pos : 0 < heatKernelTimeConstant := by
  unfold heatKernelTimeConstant
  positivity

theorem heatKernelSecondTimeEnvelope_nonneg {s : ℝ} (r : ℝ) (hs : 0 ≤ s) :
    0 ≤ heatKernelSecondTimeEnvelope r s := by
  unfold heatKernelSecondTimeEnvelope
  positivity

theorem heatKernelSecondTimeEnvelope_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (heatKernelSecondTimeEnvelope r) (Ioi 0) := by
  have ha : 0 < r ^ 2 / 4 := by positivity
  exact (((integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)).const_mul
    (r ^ 2 / 4)).add
      ((integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
        (1 / 2))).const_mul _

theorem integral_heatKernelSecondTimeEnvelope {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in Ioi 0, heatKernelSecondTimeEnvelope r s) =
      heatKernelTimeConstant * r ^ (-3 : ℝ) := by
  have ha : 0 < r ^ 2 / 4 := by positivity
  have hfive := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)
  have hthree := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)
  have hpow : r ^ 2 * r ^ (-5 : ℝ) = r ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
    norm_num
  simp only [heatKernelSecondTimeEnvelope, integral_const_mul,
    integral_add (hfive.const_mul (r ^ 2 / 4)) (hthree.const_mul (1 / 2))]
  rw [integral_inverseTimeGamma_square_scale hr (by norm_num : (0 : ℝ) < 5 / 2),
    integral_inverseTimeGamma_square_scale hr (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num only [show (-2 : ℝ) * (5 / 2) = -5 by norm_num,
    show (-2 : ℝ) * (3 / 2) = -3 by norm_num]
  unfold heatKernelTimeConstant
  calc
    _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (4 ^ (5 / 2 : ℝ) / 4 * Real.Gamma (5 / 2) * (r ^ 2 * r ^ (-5 : ℝ)) +
          4 ^ (3 / 2 : ℝ) / 2 * Real.Gamma (3 / 2) * r ^ (-3 : ℝ)) := by ring
    _ = _ := by rw [hpow]; ring

private theorem heatKernel_invTime_decomposition {s : ℝ} (hs : 0 < s)
    (z : Space) (a b : ℝ) :
    (a / (4 * s ^ 2) + b / (2 * s)) * heatKernel s z =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (a / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s)) +
        b / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s))) := by
  have hfive : s ^ (-((5 / 2 : ℝ) + 1)) = s ^ (-(3 / 2 : ℝ)) / s ^ 2 := by
    rw [show -((5 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) - (2 : ℕ) by norm_num]
    exact Real.rpow_sub_natCast hs.ne' _ _
  have hthree : s ^ (-((3 / 2 : ℝ) + 1)) = s ^ (-(3 / 2 : ℝ)) / s := by
    rw [show -((3 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) - 1 by norm_num]
    exact Real.rpow_sub_one hs.ne' _
  have he : Real.exp (-(‖z‖ ^ 2) / (4 * s)) =
      Real.exp (-(‖z‖ ^ 2 / 4) / s) := by
    congr 1
    simp only [neg_div, div_div]
  unfold heatKernel
  rw [hfive, hthree, Real.mul_rpow (show 0 ≤ (4 : ℝ) * Real.pi by positivity) hs.le, he]
  field_simp [hs.ne']


/-- The Gaussian coordinate Hessian is the difference of two integrable
inverse-time Gamma terms. -/
theorem heatKernelSecond_inverseTime_decomposition {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    heatKernelSecond s i j z =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        (z i * z j / 4 * (s ^ (-((5 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s)) -
        (if i = j then 1 else 0) / 2 * (s ^ (-((3 / 2 : ℝ) + 1)) *
          Real.exp (-(‖z‖ ^ 2 / 4) / s))) := by
  simpa only [heatKernelSecond, neg_div, neg_mul, sub_eq_add_neg] using
    heatKernel_invTime_decomposition hs z (z i * z j) (-(if i = j then 1 else 0))

theorem heatKernelSecondTimeEnvelope_eq {s : ℝ} (hs : 0 < s) (z : Space) :
    heatKernelSecondTimeEnvelope ‖z‖ s =
      (‖z‖ ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * heatKernel s z :=
  (heatKernel_invTime_decomposition hs z (‖z‖ ^ 2) 1).symm

theorem norm_heatKernelSecond_le_timeEnvelope {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    ‖heatKernelSecond s i j z‖ ≤ heatKernelSecondTimeEnvelope ‖z‖ s := by
  rw [heatKernelSecondTimeEnvelope_eq hs z]
  exact norm_heatKernelSecond_le hs i j z

/-- Away from the spatial origin, every Hessian component is integrable in
positive time. -/
theorem heatKernelSecond_integrable_time (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    IntegrableOn (fun s : ℝ => heatKernelSecond s i j z) (Ioi 0) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ha : 0 < ‖z‖ ^ 2 / 4 := by positivity
  have hfive := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 5 / 2)
  have hthree := integrableOn_inverseTimeGamma ha (by norm_num : (0 : ℝ) < 3 / 2)
  have h := ((hfive.const_mul (z i * z j / 4)).sub
    (hthree.const_mul ((if i = j then (1 : ℝ) else 0) / 2))).const_mul
      ((4 * Real.pi) ^ (-(3 / 2 : ℝ)))
  refine h.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact (heatKernelSecond_inverseTime_decomposition hs i j z).symm

/-- The positive-time integral of the absolute Hessian kernel has the
inverse-cube decay needed for the pressure commutator. -/
theorem heatKernelSecond_integral_norm_le (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    (∫ s : ℝ in Ioi 0, ‖heatKernelSecond s i j z‖) ≤
      heatKernelTimeConstant * ‖z‖ ^ (-3 : ℝ) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    (∫ s : ℝ in Ioi 0, ‖heatKernelSecond s i j z‖) ≤
        ∫ s : ℝ in Ioi 0, heatKernelSecondTimeEnvelope ‖z‖ s := by
      refine integral_mono_ae (heatKernelSecond_integrable_time i j hz).norm
        (heatKernelSecondTimeEnvelope_integrable hr) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact norm_heatKernelSecond_le_timeEnvelope hs i j z
    _ = _ := integral_heatKernelSecondTimeEnvelope hr

theorem heatKernelSecond_integral_abs_le (i j : Fin 3) {z : Space} (hz : z ≠ 0) :
    (∫ s : ℝ in Ioi 0, |heatKernelSecond s i j z|) ≤
      heatKernelTimeConstant * ‖z‖ ^ (-3 : ℝ) := by
  simpa only [Real.norm_eq_abs] using heatKernelSecond_integral_norm_le i j hz

end NavierStokesR3.Comparison
