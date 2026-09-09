/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolterraFixedPoint
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel

@[expose] public section

/-! Uniqueness, initial traces, and genuine positive time budgets for the Volterra construction. -/

noncomputable section

namespace EulerVolterraConvolution

open MeasureTheory Set
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
variable (hk : IntegrableOn k (Ioc 0 T)) (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
variable (hbound : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

include hK hk hk0 hbound in
/-- Two actual mild solutions in the contraction ball agree as continuous paths. -/
theorem mild_solution_unique (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R L : ℝ) (hL : 0 ≤ L)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (hsmall : kernelMass T k * L < 1)
    (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hsolu : ∀ t : Icc (0 : ℝ) T, u t = a t + ∫ r in (0 : ℝ)..t.val,
      K r (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r)))))
    (hsolv : ∀ t : Icc (0 : ℝ) T, v t = a t + ∫ r in (0 : ℝ)..t.val,
      K r (F (projIcc 0 T hT (t.val - r)) (v (projIcc 0 T hT (t.val - r))))) : u = v := by
  have hfix (z : C(Icc (0 : ℝ) T, X))
      (hz : ∀ t : Icc (0 : ℝ) T, z t = a t + ∫ r in (0 : ℝ)..t.val,
        K r (F (projIcc 0 T hT (t.val - r)) (z (projIcc 0 T hT (t.val - r))))) :
      picard T hT K k hK hk hk0 hbound a F hF z = z := by
    ext t
    change a t + convolution T hT K k hK hk hk0 hbound (pathNonlinearity T F hF z) t = z t
    rw [convolution_eq_interval T hT K k hK hk hk0 hbound]
    exact (hz t).symm
  have h := picard_sub_bound T hT K k hK hk hk0 hbound a F hF R L hL hFL u v hu hv
  rw [hfix u hsolu, hfix v hsolv] at h
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The actual Volterra integral vanishes at time zero, giving the prescribed initial trace. -/
theorem mild_solution_initial (a u : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hsol : ∀ t : Icc (0 : ℝ) T, u t = a t + ∫ r in (0 : ℝ)..t.val,
      K r (F (projIcc 0 T hT (t.val - r)) (u (projIcc 0 T hT (t.val - r))))) :
    u ⟨0, le_rfl, hT⟩ = a ⟨0, le_rfl, hT⟩ := by
  simpa only [intervalIntegral.integral_same, add_zero] using hsol ⟨0, le_rfl, hT⟩

end EulerVolterraConvolution

namespace EulerSobolevHeat

open Set
open scoped Topology

/-- The viscosity-dependent coefficient in the parabolic kernel bound is nonnegative. -/
theorem parabolicConstant_nonneg (ν : ℝ) : 0 ≤ parabolicConstant ν :=
  div_nonneg (EulerGaussianCylinderHeat.gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _)

/-- The explicit parabolic kernel mass is continuous at zero and vanishes there. -/
theorem parabolic_mass_continuous (ν : ℝ) :
    Continuous (fun T : ℝ => T + 2 * parabolicConstant ν * Real.sqrt T) :=
  continuous_id.add (continuous_const.mul Real.continuous_sqrt)

/-- The actual parabolic kernel has a strictly positive interval satisfying both Picard budgets. -/
theorem exists_positive_time_budget (ν M L margin Tmax : ℝ) (hmargin : 0 < margin) (hTmax : 0 <
  Tmax) :
    ∃ T : ℝ, 0 < T ∧ T ≤ Tmax ∧
      (T + 2 * parabolicConstant ν * Real.sqrt T) * M < margin ∧
      (T + 2 * parabolicConstant ν * Real.sqrt T) * L < 1 := by
  have hM : Filter.Tendsto (fun T : ℝ => (T + 2 * parabolicConstant ν * Real.sqrt T) * M)
      (𝓝 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_add, zero_mul] using
      ((parabolic_mass_continuous ν).mul_const M).continuousAt.tendsto (x := (0 : ℝ))
  have hL : Filter.Tendsto (fun T : ℝ => (T + 2 * parabolicConstant ν * Real.sqrt T) * L)
      (𝓝 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_add, zero_mul] using
      ((parabolic_mass_continuous ν).mul_const L).continuousAt.tendsto (x := (0 : ℝ))
  have he : {T : ℝ | T < Tmax ∧
      (T + 2 * parabolicConstant ν * Real.sqrt T) * M < margin ∧
      (T + 2 * parabolicConstant ν * Real.sqrt T) * L < 1} ∈ 𝓝 (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hTmax, hM.eventually (Iio_mem_nhds hmargin),
      hL.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht hm hl
    exact ⟨ht, hm, hl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  obtain ⟨ht, hm, hl⟩ := hball hb
  exact ⟨ε / 2, by positivity, ht.le, hm, hl⟩

end EulerSobolevHeat
