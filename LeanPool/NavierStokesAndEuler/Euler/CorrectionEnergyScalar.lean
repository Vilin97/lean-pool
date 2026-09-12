/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionMildEnergy
import LeanPool.NavierStokesAndEuler.Euler.GevreyDifferentiatedEquation
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.EnergyBootstrap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Related estimates used together by the same construction modules. -/

section

/-! The actual correction energy right-hand side has the scalar shrinking-radius form, including its
exact zero initial trace. -/

@[expose] public section

noncomputable section

namespace EulerCorrectionEnergyScalar

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
      EulerCorrectionMildEnergy
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerNonlinearEnergyConstants
      EulerTimeLpSubintervalBound
  EulerTimeLp EulerVolterraConvolution EulerSobolevHeat EulerGevreyMetricComparison
      EulerGevreyDifferentiatedEquation
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual scalar correction right-hand side is bounded by the source's nonlinear
shrinking-radius expression. -/
theorem correctionRhs_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)} {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : SpatialBudget period hq D N R) (hN : N + 6 ≤ q + 1) {hT : 0 ≤ T} (K : MetricBudget period
        T hT
        D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 :
        ℝ)
        T) :
    let X := energyPath period N hN T R (K.operatorPath period) e t
    let Y := lossPath period N hN T R (K.operatorPath period) e t
    let C := combinedConstant period S K
    correctionRhs period S hN K Rdot e t ≤ C*(X+X^2+S.residual) +
      (Rdot t/R t+C*((R t)⁻¹+S.Rc)*(S.B0+X))*Y := by
  obtain ⟨hg0,hg1,hk⟩ := K.constants_nonneg period S.B0 S.B0_nonneg
  exact actual_scalar_bound period (K.growth0 period S.B0) (K.growth1 period) (K.multiplier period)
    S.B S.M S.B0 S.B1 S.A0 S.A2 K.c S.Rc (R t) S.residual
    (energyPath period N hN T R (K.operatorPath period) e t)
    (lossPath period N hN T R (K.operatorPath period) e t) (Rdot t/R t)
    hg0 hg1 hk S.B_nonneg (zero_le_one.trans S.M_one_le) S.B0_nonneg S.B1_nonneg S.A0_nonneg
        S.A2_nonneg K.c_pos
    S.Rc_nonneg (S.radius_pos t) S.residual_pos.le (energy_nonneg period S hN K e t) (loss_nonneg
        period S hN K e t)

/-- Zero is exactly zero in the genuine finite metric energy. -/
theorem energyNorm_zero {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) : energyNorm period N hN ρ K (0 : SobolevSpace period
        q) = 0 := by
  unfold energyNorm weightedMetricSum
  apply Finset.sum_eq_zero
  intro I _
  have hzero : energyValues period 6 N hN (0 : SobolevSpace period q) I = fun _ => 0 := by
    funext a
    rw [← energyWordOperator_apply, map_zero]
  rw [hzero]
  simp [familyMetricNorm, familyEnergy]

/-- The actual zero-initial mild formula has zero trace, without a separately assumed initial-value
identity. -/
theorem zero_mild_trace {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q +
        1)))
    (hsol : ∀ t : Icc (0 : ℝ) T, e t = heatOperator period (q+1) (2*ν*t.val).toNNReal 0 +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    e ⟨0,le_rfl,hT⟩ = 0 := by
  have h := hsol ⟨0,le_rfl,hT⟩
  simpa only [map_zero, intervalIntegral.integral_same, add_zero] using h

/-- A prescribed affine radius has its genuine time derivative at every interior point after clamped
extension. -/
theorem affine_radius_derivative (T : ℝ) (hT : 0 ≤ T) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (ρ0 A : ℝ) (hR : ∀ t, R t = ρ0 - A * t.val) (hRdot : ∀ t, Rdot t = -A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t := by
  have hm : HasDerivAt (fun r : ℝ => A*r) A t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul A
  have ha : HasDerivAt (fun r : ℝ => ρ0-A*r) (-A) t := HasDerivAt.const_sub ρ0 hm
  have he : extendPath T hT R =ᶠ[𝓝 t] fun r => ρ0-A*r := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    change R (projIcc 0 T hT r) = _
    rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
    exact hR ⟨r,hr.1.le,hr.2.le⟩
  exact (ha.congr_of_eventuallyEq he).congr_deriv (hRdot (projIcc 0 T hT t)).symm

end EulerCorrectionEnergyScalar

end
end

end

section

/-! Shrinking-radius Gevrey bootstrap from actual integral energy inequalities, including zero
norms. -/

@[expose] public section

noncomputable section

namespace EulerIntegralEnergyBootstrap

open MeasureTheory Set Real EulerEnergyBootstrap
open scoped Topology

/-- An all-subinterval integral upper bound gives the genuine right Dini slope bound.
The energy itself need only be continuous, and may vanish. -/
theorem liminf_slope_le_of_integral (X A : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b))
    (hineq : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → X y - X x ≤ ∫ s in x..y, A s)
    (x : ℝ) (hx : x ∈ Ico a b) (r : ℝ) (hr : A x < r) :
    ∃ᶠ y in 𝓝[>] x, slope X x y < r := by
  let g : ℝ → ℝ := fun t => A (projIcc a b hab t).val
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hA).comp continuous_projIcc
  have hgx : g x = A x := by simp only [g, projIcc_of_mem hab ⟨hx.1, hx.2.le⟩]
  let H : ℝ → ℝ := fun t => ∫ s in x..t, g s
  have hd : HasDerivAt H (A x) x := by
    have h := (hg.integral_hasStrictDerivAt x x).hasDerivAt
    rwa [hgx] at h
  have hs := hd.hasDerivWithinAt (s := Ioi x) |>.limsup_slope_le' (lt_irrefl x) hr
  have he : ∀ᶠ y in 𝓝[>] x, slope X x y < r := by
    filter_upwards [hs, Ioc_mem_nhdsGT hx.2] with y hys hy
    have hxy := hineq x ⟨hx.1, hx.2.le⟩ y ⟨hx.1.trans hy.1.le, hy.2⟩ hy.1.le
    have hi : (∫ s in x..y, A s) = ∫ s in x..y, g s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with s hs
      rw [uIoc_of_le hy.1.le] at hs
      simp only [g, projIcc_of_mem hab ⟨hx.1.trans hs.1.le, hs.2.trans hy.2⟩]
    rw [hi] at hxy
    have hcomp : slope X x y ≤ slope H x y := by
      rw [slope_def_field, slope_def_field]
      simp only [H, intervalIntegral.integral_same, sub_zero]
      exact div_le_div_of_nonneg_right hxy (sub_nonneg.mpr hy.1.le)
    exact hcomp.trans_lt hys
  exact he.frequently

/-- The source's nonlinear shrinking-radius bootstrap closes directly from the all-subinterval
integral energy bound. -/
theorem close_integral_energy_estimate
    (X A Y : ℝ → ℝ) (C B Δ r ρ₀ S R₀ : ℝ)
    (hC : 0 < C) (hB : 0 ≤ B) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : 0 < r) (hρ : 0 < ρ₀) (hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (hsmall : 2 * r * exp (3 * C * S) ≤ Δ / 2)
    (hcont : ContinuousOn X (Icc 0 S)) (hAcont : ContinuousOn A (Icc 0 S)) (hinit : X 0 ≤ 2 * r)
    (hint : ∀ s ∈ Icc 0 S, ∀ t ∈ Icc 0 S, s ≤ t → X t - X s ≤ ∫ u in s..t, A u)
    (hY : ∀ t ∈ Ico 0 S, 0 ≤ Y t)
    (hineq : ∀ t ∈ Ico 0 S,
      A t ≤ C * (X t + (X t) ^ 2 + r) +
        ((-2 * C * (B + Δ)) / (ρ₀ - 2 * C * (B + Δ) * t) +
          C * ((ρ₀ - 2 * C * (B + Δ) * t)⁻¹ + R₀) * (B + X t)) * Y t) :
    ∀ t ∈ Icc 0 S, X t ≤ 2 * r * exp (3 * C * t) ∧ X t ≤ Δ / 2 := by
  let F : ℝ → ℝ := fun t => 2 * r * exp (3 * C * t)
  have hF (t : ℝ) : HasDerivAt F (3 * C * F t) t := by
    have hlin : HasDerivAt (fun s : ℝ => 3 * C * s) (3 * C) t := by
      simpa using (hasDerivAt_id t).const_mul (3 * C)
    change HasDerivAt (fun s => 2 * r * exp (3 * C * s))
      (3 * C * (2 * r * exp (3 * C * t))) t
    exact (hlin.exp.const_mul (2 * r)).congr_deriv (by ring)
  have hFle (t : ℝ) (ht : t ∈ Icc 0 S) : F t ≤ Δ / 2 := by
    calc
      F t ≤ 2 * r * exp (3 * C * S) := by dsimp [F]; gcongr; exact ht.2
      _ ≤ _ := hsmall
  have hFp (t : ℝ) : 0 < F t := by dsimp [F]; positivity
  have hFbase (t : ℝ) (ht : 0 ≤ t) : 2 * r ≤ F t := by
    have he : 1 ≤ exp (3 * C * t) := one_le_exp_iff.mpr (by positivity)
    dsimp [F]
    nlinarith
  have hbound : ∀ t ∈ Icc 0 S, X t ≤ F t := by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hcont
      (fun t ht r hr => liminf_slope_le_of_integral X A 0 S hS hAcont hint t ht r hr)
    · simpa only [F, mul_zero, exp_zero, mul_one] using hinit
    · exact hF
    · intro t ht hXF
      have htc : t ∈ Icc 0 S := ⟨ht.1, ht.2.le⟩
      have hrad := radius_bounds C B Δ ρ₀ S R₀ hC.le hB hΔ.le hρ hS hR hdecay hscale t htc
      have hloss := shrinking_radius_cancels_loss C B Δ _ R₀ (X t)
        hC.le hB hΔ.le hrad.2.1 hR hrad.2.2 (by rw [hXF]; linarith [hFle t htc])
      have hlossY := mul_nonpos_of_nonpos_of_nonneg hloss (hY t ht)
      have hmain := hineq t ht
      have hFt := hFp t
      have hFΔ := hFle t htc
      have hFr := hFbase t ht.1
      rw [hXF] at hmain hlossY
      have hFsq : (F t) ^ 2 ≤ F t := by nlinarith
      have hCsq := mul_le_mul_of_nonneg_left hFsq hC.le
      have hCr := mul_le_mul_of_nonneg_left hFr hC.le
      have hpos := mul_pos hC hFt
      nlinarith
  intro t ht
  exact ⟨hbound t ht, (hbound t ht).trans (hFle t ht)⟩

end EulerIntegralEnergyBootstrap

end
end

end
