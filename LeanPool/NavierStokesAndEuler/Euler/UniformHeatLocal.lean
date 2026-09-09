/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal

@[expose] public section

/-! A uniform positive restart time for bounded data in the actual viscous Sobolev equation. -/

noncomputable section

namespace EulerUniformHeatLocal

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerQuadraticSource
open scoped Topology

/-- A translated compact time window inside the prescribed coefficient interval. -/
def timeWindow {S : ℝ} (a T : ℝ) (ha : 0 ≤ a) (haT : a+T ≤ S) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨a+t.val, by linarith [t.property.1], by linarith [t.property.2]⟩
  continuous_toFun := (continuous_const.add continuous_subtype_val).subtype_mk _

/-- The mass of the actual parabolic kernel bound is monotone in nonnegative time. -/
theorem parabolic_mass_mono (ν s t : ℝ) (hst : s ≤ t) :
    s + 2 * parabolicConstant ν * Real.sqrt s ≤ t + 2 * parabolicConstant ν * Real.sqrt t := by
  have hC := parabolicConstant_nonneg ν
  have hroot := Real.sqrt_le_sqrt hst
  nlinarith

variable (period : ℝ) [Fact (0 < period)]

/-- Uniformly bounded initial Sobolev data have genuine local solutions on every time window of one fixed positive length.
The length depends only on the compact coefficient bounds and the data bound, not on the restart
  time or state. -/
theorem exists_uniform_restart_time (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (R : ℝ) (hR : 0 ≤ R)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q+1)) (SobolevSpace period q)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a+T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace period (q+1), ‖u₀‖ ≤ R →
          ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
            ‖u‖ ≤ R+1 ∧ u ⟨0, le_rfl, hT⟩ = u₀ ∧
            ∀ t : Icc (0 : ℝ) T, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
              ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
                (C.apply (timeWindow a T ha haT (projIcc 0 T hT (t.val-r)))
                  (u (projIcc 0 T hT (t.val-r)))) := by
  have hR1 : 0 ≤ R+1 := by linarith
  obtain ⟨δ, hδ, hδS, hb, hl⟩ := exists_positive_time_budget ν
    (C.ballBound (R+1)) (C.ballLipschitz (R+1)) 1 S (by norm_num) hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro a T ha hT haT hTδ u₀ hu₀
  let D := C.comp (timeWindow a T ha haT)
  have hmass := parabolic_mass_mono ν T δ hTδ
  have hM := C.ballBound_nonneg (R+1) hR1
  have hL := C.ballLipschitz_nonneg (R+1) hR1
  have hbudget : ‖u₀‖ + (T+2*parabolicConstant ν*Real.sqrt T)*C.ballBound (R+1) ≤ R+1 := by
    have hh := mul_le_mul_of_nonneg_right hmass hM
    linarith
  have hsmall : (T+2*parabolicConstant ν*Real.sqrt T)*C.ballLipschitz (R+1) < 1 :=
    (mul_le_mul_of_nonneg_right hmass hL).trans_lt hl
  obtain ⟨u, hu, hsol⟩ := exists_viscous_mild_solution period q ν hν T hT u₀ D.apply D.continuous
    (R+1) (C.ballBound (R+1)) (C.ballLipschitz (R+1)) hR1 hM hL
    (fun t x hx => C.apply_bound (R+1) hR1 (timeWindow a T ha haT t) x hx)
    (fun t x y hx hy => C.apply_sub_bound (R+1) hR1 (timeWindow a T ha haT t) x y hx hy)
    hbudget hsmall
  refine ⟨u, hu, ?_, hsol⟩
  have hzero := hsol ⟨0, le_rfl, hT⟩
  simpa only [mul_zero, Real.toNNReal_zero, heatOperator_zero, intervalIntegral.integral_same,
    add_zero] using hzero

end EulerUniformHeatLocal
