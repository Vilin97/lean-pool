/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionDerivativeBound
import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Symmetric compact smooth approximate identities on ordinary spatial L². -/

@[expose] public section


noncomputable section

namespace EulerOrdinaryMollifier

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerNoncompactTransport EulerLpTranslation.SmoothL2Field
open scoped ContDiff Topology Convolution

/-- Bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
def bump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := cutoffScale n
  rOut := 2*cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

/-- Kernel, given by `(bump n).normed volume`. -/
def kernel (n : ℕ) : Space → ℝ := (bump n).normed volume

theorem kernel_smooth (n : ℕ) : ContDiff ℝ ∞ (kernel n) := (bump n).contDiff_normed
theorem kernel_compact (n : ℕ) : HasCompactSupport (kernel n) := (bump n).hasCompactSupport_normed
theorem kernel_nonneg (n : ℕ) (x : Space) : 0 ≤ kernel n x := (bump n).nonneg_normed x
theorem kernel_integral (n : ℕ) : ∫ x, kernel n x = 1 := (bump n).integral_normed
theorem kernel_integrable (n : ℕ) : Integrable (kernel n) := (bump n).integrable_normed
theorem kernel_neg (n : ℕ) (x : Space) : kernel n (-x)=kernel n x := (bump n).normed_neg x

/-- Smooth orbit, given by `convolution (kernel n) (fun a => translation a u)
(ContinuousLinearMap.lsmul ℝ ℝ) volume`. -/
def smoothOrbit (n : ℕ) (u : L2) : Space → L2 :=
  convolution (kernel n) (fun a => translation a u) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Mollify, given by `smoothOrbit n u 0`. -/
def mollify (n : ℕ) (u : L2) : L2 := smoothOrbit n u 0

theorem smoothOrbit_contDiff (n : ℕ) (u : L2) : ContDiff ℝ ∞ (smoothOrbit n u) :=
  (kernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_smooth n) (EulerMeanTimeTranslation.translation_continuous u).locallyIntegrable

theorem mollify_tendsto (u : L2) : Tendsto (fun n => mollify n u) atTop (𝓝 u) := by
  have hr : Tendsto (fun n => (bump n).rOut) atTop (𝓝 (0 : ℝ)) := by
    simpa only [bump,mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Space)) hr (EulerMeanTimeTranslation.translation_continuous u) 0
  simpa only [translation_zero,mollify,smoothOrbit,kernel] using h

theorem mollify_eq_integral (n : ℕ) (u : L2) :
    mollify n u=∫ y : Space, kernel n y • translation (-y) u := by
  simp only [mollify,smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply,zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (u : L2) :
    Integrable (fun y : Space => kernel n y • translation (-y) u) :=
  ((kernel_smooth n).continuous.smul
    ((EulerMeanTimeTranslation.translation_continuous u).comp
        continuous_neg)).integrable_of_hasCompactSupport
      (kernel_compact n).smul_right

theorem mollify_norm_le (n : ℕ) (u : L2) : ‖mollify n u‖ ≤ ‖u‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le ((kernel_integrable n).mul_const ‖u‖)
    (f := fun y : Space => kernel n y • translation (-y) u) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  exact Eventually.of_forall (fun y => by
    rw [norm_smul,LinearIsometry.norm_map,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)])

theorem mollify_add (n : ℕ) (u v : L2) : mollify n (u+v)=mollify n u+mollify n v := by
  simp only [mollify_eq_integral,map_add,smul_add]
  exact integral_add (kernel_orbit_integrable n u) (kernel_orbit_integrable n v)

theorem mollify_smul (n : ℕ) (c : ℝ) (u : L2) : mollify n (c • u)=c • mollify n u := by
  simp only [mollify_eq_integral,map_smul]
  simp_rw [smul_comm (kernel n _) c]
  exact integral_smul c _

/-- Mollifier linear, bundling `toFun`, `map_add`, `map_smul`. -/
def mollifierLinear (n : ℕ) : L2 →ₗ[ℝ] L2 where
  toFun := mollify n
  map_add' := mollify_add n
  map_smul' := mollify_smul n

/-- Mollifier, given by `(mollifierLinear n).mkContinuous 1 (fun u => by change ‖mollify n u‖ ≤
1*‖u‖ simpa only [one_mul] using mollify_norm_le n u)`. -/
def mollifier (n : ℕ) : L2 →L[ℝ] L2 :=
  (mollifierLinear n).mkContinuous 1 (fun u => by
    change ‖mollify n u‖ ≤ 1*‖u‖
    simpa only [one_mul] using mollify_norm_le n u)

@[simp] theorem mollifier_apply (n : ℕ) (u : L2) : mollifier n u=mollify n u := rfl

theorem mollify_translation (n : ℕ) (a : Space) (u : L2) :
    translation a (mollify n u)=mollify n (translation a u) := by
  rw [mollify_eq_integral,mollify_eq_integral]
  change (translation a).toContinuousLinearMap
    (∫ y : Space, kernel n y • translation (-y) u)=_
  rw [← (translation a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap]
    rw [translation_add,translation_add,add_comm a])

theorem smoothOrbit_eq (n : ℕ) (u : L2) (x : Space) :
    smoothOrbit n u x=translation x (mollify n u) := by
  rw [mollify_eq_integral]
  change _=(translation x).toContinuousLinearMap
    (∫ y : Space, kernel n y • translation (-y) u)
  rw [← (translation x).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  simp only [smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap,translation_add,sub_eq_add_neg])

theorem mollify_smooth (n : ℕ) (u : L2) :
    ContDiff ℝ ∞ (fun a => translation a (mollify n u)) := by
  convert smoothOrbit_contDiff n u using 1
  exact funext (fun a => (smoothOrbit_eq n u a).symm)

theorem translation_inner_shift (a : Space) (u v : L2) :
    ⟪translation a u,v⟫_ℝ=⟪u,translation (-a) v⟫_ℝ := by
  calc
    _=⟪translation a u,translation a (translation (-a) v)⟫_ℝ := by
      rw [translation_add,add_neg_cancel,translation_zero]
    _=_ := (translation a).inner_map_map _ _

theorem mollify_symmetric (n : ℕ) (u v : L2) :
    ⟪mollify n u,v⟫_ℝ=⟪u,mollify n v⟫_ℝ := by
  rw [mollify_eq_integral,mollify_eq_integral]
  rw [real_inner_comm v _,← integral_inner (kernel_orbit_integrable n u) v,
    ← integral_inner (kernel_orbit_integrable n v) u]
  rw [← integral_neg_eq_self (fun y : Space => ⟪v,kernel n y • translation (-y) u⟫_ℝ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [kernel_neg,neg_neg,real_inner_smul_right,real_inner_smul_right,
      real_inner_comm _ v,translation_inner_shift])

theorem translation_increment (A : EulerLpTranslation.SmoothL2Field Space) (a : Space) :
    ‖translation a A.toLp-A.toLp‖ ≤ ‖A.derivative.toLp‖*‖a‖ := by
  have h := A.translation_hasFDerivAt 0
  simp only [EulerLpTranslation.translation_zero] at h
  exact (EulerIsometricAction.norm_sub_le_of_hasFDerivAt translation translation_add
      translation_zero
    A.toLp _ h a).trans (mul_le_mul_of_nonneg_right
      (EulerLpDerivative.derivativeMap_norm_le _ _) (norm_nonneg _))

theorem mollify_error (n : ℕ) (A : EulerLpTranslation.SmoothL2Field Space) :
    ‖mollify n A.toLp-A.toLp‖ ≤ (2*cutoffScale n)*‖A.derivative.toLp‖ := by
  have he : mollify n A.toLp-A.toLp =
      ∫ y : Space, kernel n y • (translation (-y) A.toLp-A.toLp) := by
    simp only [smul_sub,integral_sub (kernel_orbit_integrable n A.toLp)
      ((kernel_integrable n).smul_const A.toLp),integral_smul_const,kernel_integral,
      one_smul,mollify_eq_integral]
  rw [he]
  have h := norm_integral_le_of_norm_le
    ((kernel_integrable n).mul_const ((2*cutoffScale n)*‖A.derivative.toLp‖))
    (f := fun y : Space => kernel n y • (translation (-y) A.toLp-A.toLp)) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  apply Eventually.of_forall
  intro y
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)]
  by_cases hy : kernel n y=0
  · simp only [hy,zero_mul,le_refl]
  apply mul_le_mul_of_nonneg_left _ (kernel_nonneg n y)
  apply (translation_increment A (-y)).trans
  rw [norm_neg,mul_comm (2*cutoffScale n)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hs : y ∈ Function.support ((bump n).normed volume) := hy
  rw [(bump n).support_normed_eq,Metric.mem_ball,dist_zero_right] at hs
  exact hs.le

end EulerOrdinaryMollifier
