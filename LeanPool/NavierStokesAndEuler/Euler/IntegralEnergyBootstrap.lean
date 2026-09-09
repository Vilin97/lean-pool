/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Shrinking-radius Gevrey bootstrap from actual integral energy inequalities, including zero
  norms. -/

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

/-- The source's nonlinear shrinking-radius bootstrap closes directly from the all-subinterval integral energy bound. -/
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
