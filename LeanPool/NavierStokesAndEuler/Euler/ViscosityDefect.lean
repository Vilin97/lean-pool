/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatGenerator
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! The actual viscous term vanishes uniformly for a uniformly Sobolev-bounded approximation
  family. -/

noncomputable section

namespace EulerViscosityDefect

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
open scoped Topology

/-- A concrete strictly positive sequence of viscosities tending to zero. -/
def viscositySequence (n : ℕ) : ℝ := 1/((n : ℝ)+1)

/-- Each concrete approximation viscosity is strictly positive. -/
theorem viscositySequence_pos (n : ℕ) : 0 < viscositySequence n := by
  unfold viscositySequence
  positivity

/-- Each concrete approximation viscosity lies in the fixed unit interval. -/
theorem viscositySequence_le_one (n : ℕ) : viscositySequence n ≤ 1 := by
  unfold viscositySequence
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The actual chosen viscosity sequence converges to zero. -/
theorem viscositySequence_tendsto : Filter.Tendsto viscositySequence Filter.atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable (period : ℝ) [Fact (0 < period)]

/-- The literal viscosity times the spatial Laplacian, as a continuous L² time path. -/
def viscousDefect {q : ℕ} (hq : 2 ≤ q) (ν T : ℝ)
    (e : C(Icc (0 : ℝ) T,SobolevSpace period q)) : C(Icc (0 : ℝ) T,LiftL2 period) :=
  ν • (laplacianEvaluation period q hq).compLeftContinuous ℝ (Icc (0 : ℝ) T) e

/-- The actual viscous PDE term is uniformly bounded by the complete Sobolev path norm. -/
theorem viscousDefect_bound {q : ℕ} (hq : 2 ≤ q) (ν T : ℝ)
    (e : C(Icc (0 : ℝ) T,SobolevSpace period q)) :
    ‖viscousDefect period hq ν T e‖ ≤ 4 * |ν| * ‖e‖ := by
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 4 * |ν| * ‖e‖)).mpr
  intro t
  change ‖ν • laplacianEvaluation period q hq (e t)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |ν| * (4*‖e t‖) := mul_le_mul_of_nonneg_left (laplacianEvaluation_bound period hq (e t))
      (abs_nonneg ν)
    _ ≤ |ν| * (4*‖e‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (e.norm_coe_le_norm
      t) (by norm_num)) (abs_nonneg ν)
    _ = _ := by ring

/-- Every uniformly bounded genuine Sobolev approximation family has a uniformly vanishing viscous PDE defect. -/
theorem viscousDefect_tendsto_zero {q : ℕ} (hq : 2 ≤ q) (T M : ℝ)
    (e : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period q)) (he : ∀ n, ‖e n‖ ≤ M) :
    Filter.Tendsto (fun n => viscousDefect period hq (viscositySequence n) T (e n)) Filter.atTop (𝓝
      0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (show Filter.Tendsto (fun n => 4*viscositySequence n*M) Filter.atTop (𝓝 0) from by
      simpa only [mul_zero,zero_mul] using (viscositySequence_tendsto.const_mul 4).mul_const M)
  have h := viscousDefect_bound period hq (viscositySequence n) T (e n)
  rw [abs_of_pos (viscositySequence_pos n)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (he n)
    (mul_nonneg (by norm_num) (viscositySequence_pos n).le))

end EulerViscosityDefect
