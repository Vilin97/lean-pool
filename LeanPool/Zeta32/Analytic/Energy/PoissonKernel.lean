/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.Analysis.Complex.JensenFormula

/-! Poisson-kernel integrals on the unit circle, in the interval-integral form used by
the component potentials of the proof notes (8′). `PK w θ` is the Poisson kernel
`Re((e^{iθ}+w)/(e^{iθ}−w))`.
The three facts: `∫₀^{2π} PK w = 2π`, `∫₀^{2π} PK w · log|e^{iθ} − q| = 2π log|w − q|` for `|q|
≥ 1`, and
`∫₀^{2π} log|e^{iθ} − q| = 2π log⁺|q|`; all from Mathlib's Poisson/Jensen formulas. -/

public section

open Real MeasureTheory Metric InnerProductSpace

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- The Poisson kernel of the unit disc at `w`, on the unit circle. -/
def PK (w : ℂ) (θ : ℝ) : ℝ := (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re

theorem circleAverage_eq_integral (f : ℂ → ℝ) :
    Real.circleAverage f 0 1 = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, f (circleMap 0 1 θ) := by
  rw [Real.circleAverage_def, smul_eq_mul]

theorem continuous_PK {w : ℂ} (hw : ‖w‖ < 1) : Continuous (PK w) := by
  have hne : ∀ θ : ℝ, circleMap 0 1 θ - 0 - (w - 0) ≠ 0 := by
    intro θ h
    have : circleMap 0 1 θ = w := by simpa [sub_eq_zero] using h
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by simp
    rw [this] at h1; linarith
  have e : PK w = fun θ => ((circleMap 0 1 θ - 0 + (w - 0)) / (circleMap 0 1 θ - 0 - (w -
    0))).re := by
    funext θ; simp only [PK, herglotzRieszKernel_def]
  rw [e]
  exact Complex.continuous_re.comp
    (((continuous_circleMap 0 1).sub continuous_const).add continuous_const |>.div
      (((continuous_circleMap 0 1).sub continuous_const).sub continuous_const) hne)

theorem integral_PK {w : ℂ} (hw : ‖w‖ < 1) : ∫ θ in (0:ℝ)..2 * π, PK w θ = 2 * π := by
  have h := HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (f := fun _ : ℂ => (1:ℝ)) (c := 0) (R := 1) (w := w) (harmonicOnNhd_const 1)
    (by simpa using hw)
  rw [circleAverage_eq_integral] at h
  have e : (fun θ => ((Complex.re ∘ herglotzRieszKernel 0 w) • fun _ : ℂ => (1:ℝ)) (circleMap 0
    1 θ))
      = PK w := by
    funext θ; simp [PK]
  rw [e] at h
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at h
  linarith

/-- Poisson formula for `log|· − q|`, `|q| = 1`. -/
theorem integral_PK_log_sphere {w q : ℂ} (hw : ‖w‖ < 1) (hq : ‖q‖ = 1) :
    ∫ θ in (0:ℝ)..2 * π, PK w θ * Real.log ‖circleMap 0 1 θ - q‖ = 2 * π * Real.log ‖w - q‖ := by
  have h := circleAverage_re_herglotzRieszKernel_mul_log (w := w) (ρ := q) (c := 0) (R := 1)
    (by simpa using hq) (by simpa using hw)
  rw [circleAverage_eq_integral] at h
  have hpi : (2 * π) ≠ 0 := by positivity
  have e : (fun θ => ((Complex.re ∘ herglotzRieszKernel 0 w) * fun z => Real.log ‖z - q‖)
      (circleMap 0 1 θ)) = fun θ => PK w θ * Real.log ‖circleMap 0 1 θ - q‖ := by
    funext θ; simp [PK]
  rw [e] at h
  field_simp at h
  linarith

/-- Poisson formula for `log|· − q|`, `|q| > 1` (harmonic on a neighbourhood of the closed disc). -/
theorem integral_PK_log_out {w q : ℂ} (hw : ‖w‖ < 1) (hq : 1 < ‖q‖) :
    ∫ θ in (0:ℝ)..2 * π, PK w θ * Real.log ‖circleMap 0 1 θ - q‖ = 2 * π * Real.log ‖w - q‖ := by
  have hharm : HarmonicOnNhd (fun z : ℂ => Real.log ‖z - q‖) (closedBall 0 1) := by
    intro z hz
    apply AnalyticAt.harmonicAt_log_norm (f := fun z => z - q) (by fun_prop)
    intro h
    have : z = q := by simpa [sub_eq_zero] using h
    rw [this, mem_closedBall, dist_zero_right] at hz
    linarith
  have h := HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul hharm
    (w := w) (by simpa using hw)
  rw [circleAverage_eq_integral] at h
  have hpi : (2 * π) ≠ 0 := by positivity
  have e : (fun θ => ((Complex.re ∘ herglotzRieszKernel 0 w) • fun z => Real.log ‖z - q‖)
      (circleMap 0 1 θ)) = fun θ => PK w θ * Real.log ‖circleMap 0 1 θ - q‖ := by
    funext θ; simp [PK]
  rw [e] at h
  field_simp at h
  linarith

/-- Jensen: `∫₀^{2π} log|e^{iθ} − q| = 2π log⁺|q|`. -/
theorem integral_log_circle (q : ℂ) :
    ∫ θ in (0:ℝ)..2 * π, Real.log ‖circleMap 0 1 θ - q‖ = 2 * π * log⁺ ‖q‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := q)
  rw [circleAverage_eq_integral] at h
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at h
  linarith

theorem intervalIntegrable_log_circle (q : ℂ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap 0 1 θ - q‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const (c := 0) (a := q) 1

theorem intervalIntegrable_PK_log_circle {w : ℂ} (hw : ‖w‖ < 1) (q : ℂ) :
    IntervalIntegrable (fun θ => PK w θ * Real.log ‖circleMap 0 1 θ - q‖) volume 0 (2 * π) :=
  (intervalIntegrable_log_circle q).continuousOn_mul (continuous_PK hw).continuousOn

/-- Explicit form of `PK` at `w = ±iβ`. -/
theorem PK_I_mul (β : ℝ) (b : ℝ) (θ : ℝ) (hβ : β ^ 2 < 1) (hb : b = β ∨ b = -β) :
    PK (Complex.I * b) θ = (1 - β^2) / (1 - 2 * b * Real.sin θ + β^2) := by
  have hb2 : b^2 = β^2 := by rcases hb with h | h <;> subst h <;> ring
  simp only [PK, herglotzRieszKernel_def, sub_zero, circleMap_zero, Complex.ofReal_one, one_mul]
  have hz : Complex.exp (↑θ * Complex.I) = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hIb : Complex.I * (b:ℂ) = ⟨0, b⟩ := by apply Complex.ext <;> simp
  have h1 : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) + ⟨0, b⟩ = ⟨Real.cos θ, Real.sin θ + b⟩ := by
    apply Complex.ext <;> simp
  have h2 : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) - ⟨0, b⟩ = ⟨Real.cos θ, Real.sin θ - b⟩ := by
    apply Complex.ext <;> simp
  rw [hz, hIb, h1, h2, Complex.div_re, Complex.normSq_mk]
  simp only
  have hs := Real.sin_sq_add_cos_sq θ
  have hden : Real.cos θ * Real.cos θ + (Real.sin θ - b) * (Real.sin θ - b) =
      1 - 2 * b * Real.sin θ + β^2 := by nlinarith
  rw [hden]
  have hpos : 0 < 1 - 2 * b * Real.sin θ + β^2 := by
    nlinarith [sq_nonneg (Real.sin θ - b), sq_nonneg (Real.cos θ)]
  field_simp
  nlinarith

end
end Zeta32.Analytic.EnergyI

end
