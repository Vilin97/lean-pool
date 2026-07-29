/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Analytic Log On Ball

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace NumberField.Odlyzko

theorem AnalyticOnNhd.exists_analyticLog_on_ball
    {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hgn : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    ∃ L : ℂ → ℂ,
      L c = Complex.log (g c) ∧
      (∀ z ∈ Metric.ball c R,
        HasDerivAt L (logDeriv g z) z) ∧
      ∀ z ∈ Metric.ball c R, Complex.exp (L z) = g z := by
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hlogDiff :
      DifferentiableOn ℂ (logDeriv g) (Metric.ball c R) := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w ↦ deriv g w / g w)
      (Metric.ball c R) z
    exact (hg.deriv z hz).differentiableAt.div
      (hg z hz).differentiableAt (hgn z hz) |>.differentiableWithinAt
  obtain ⟨L, hLc, hL⟩ :=
    hlogDiff.isExactOn_ball.with_val_at c (Complex.log (g c))
  refine ⟨L, hLc, hL, ?_⟩
  let q : ℂ → ℂ := (Complex.exp ∘ L) * g⁻¹
  have hqdiff : DifferentiableOn ℂ q (Metric.ball c R) := by
    intro z hz
    exact ((Complex.hasDerivAt_exp (L z)).comp z (hL z hz)).differentiableAt.mul
      ((hg z hz).differentiableAt.inv (hgn z hz)) |>.differentiableWithinAt
  have hqderiv : Set.EqOn (deriv q) 0 (Metric.ball c R) := by
    intro z hz
    have hgz := (hg z hz).differentiableAt.hasDerivAt
    have hq :
        HasDerivAt q 0 z := by
      have hprod :=
        ((Complex.hasDerivAt_exp (L z)).comp z (hL z hz)).mul
          (hgz.inv (hgn z hz))
      change HasDerivAt (Complex.exp ∘ L * g⁻¹) 0 z
      apply hprod.congr_deriv
      rw [logDeriv_apply]
      simp only [Function.comp_apply, Pi.inv_apply]
      grind
    exact hq.deriv
  have hqconst (z : ℂ) (hz : z ∈ Metric.ball c R) : q z = q c :=
    IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball
      (convex_ball c R).isPreconnected hqdiff hqderiv hz hc
  have hqc : q c = 1 := by
    simp only [q, Pi.mul_apply, Function.comp_apply, Pi.inv_apply]
    rw [hLc, Complex.exp_log (hgn c hc)]
    simp_all
  intro z hz
  have hqz : q z = 1 := (hqconst z hz).trans hqc
  simp only [q, Pi.mul_apply, Function.comp_apply, Pi.inv_apply] at hqz
  grind

end NumberField.Odlyzko
