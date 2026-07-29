/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RectangleSymmetry
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedCompletedZetaZeroPositivity
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles

/-!
# Regularized Poitou Contour

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem regularizedPoitou_mul_completedZetaLogDeriv_one_sub
    (y δ : ℝ) (s : ℂ) :
    poitouTransform (regularizedScaledTartar y δ) (1 - s) *
        logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -(poitouTransform (regularizedScaledTartar y δ) s *
        logDeriv (poleClearedCompletedDedekindZetaContinuation K) s) := by
  apply mul_antiInvariant_of_invariant_of_antiInvariant
  · intro z
    exact poitouTransform_one_sub (regularizedScaledTartar_even y δ) z
  · intro z
    exact
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all K z

theorem regularizedPoitou_centeredRectangle_identity
    {y δ b T : ℝ} (hδ : 0 < δ) (hb : 1 / 2 ≤ b) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
      (z.re = 1 - b ∨ z.re = b ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 - b) b (-T) -
      horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        b (-T) T =
      (2 * Real.pi * I) *
        ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
            K (1 - b) b (-T) T,
          poitouTransform (regularizedScaledTartar y δ) p *
            (completedDedekindZetaZeroDivisor K p : ℂ) := by
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      logDeriv (poleClearedCompletedDedekindZetaContinuation K) s
  change
    horizontalIntegral q (1 - b) b (-T) -
        horizontalIntegral q (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral q b (-T) T = _
  rw [← rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    (f := q)
    (regularizedPoitou_mul_completedZetaLogDeriv_one_sub K y δ) b T]
  have hab : 1 - b ≤ b := by linarith
  have huv : -T ≤ T := by linarith
  have hanalytic :
      ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
        AnalyticAt ℂ
          (poitouTransform (regularizedScaledTartar y δ)) z := by
    intro z _
    exact
      analyticOnNhd_poitouTransform_regularizedScaledTartar hδ z
        (mem_univ z)
  have hrect :=
    rectangleIntegral_mul_logDeriv_poleClearedCompletedDedekindZetaContinuation
      K
      (h := poitouTransform (regularizedScaledTartar y δ))
      (a := 1 - b) (b := b) (u := -T) (v := T)
      hab huv hanalytic hboundary
  simpa only [q, ofReal_neg] using hrect

theorem regularizedPoitou_zeroFreeRectangle_identity
    {y δ ε T : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (-ε) (1 + ε) ×ℂ Icc (-T) T,
      (z.re = -ε ∨ z.re = 1 + ε ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (-ε) (1 + ε) (-T) -
      horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (-ε) (1 + ε) T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 + ε) (-T) T =
      (2 * Real.pi * I) *
        ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
            K (-ε) (1 + ε) (-T) T,
          poitouTransform (regularizedScaledTartar y δ) p *
            (completedDedekindZetaZeroDivisor K p : ℂ) := by
  have hb : 1 / 2 ≤ 1 + ε := by linarith
  have h :=
    regularizedPoitou_centeredRectangle_identity K hδ hb hT
      (y := y) (b := 1 + ε) (by simp_all)
  simp_all

theorem regularizedPoitou_zeroFreeRectangle_im_nonneg
    {y δ ε T : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (hε : 0 < ε) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (-ε) (1 + ε) ×ℂ Icc (-T) T,
      (z.re = -ε ∨ z.re = 1 + ε ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    0 ≤
      (horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (-ε) (1 + ε) (-T) -
        horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (-ε) (1 + ε) T +
        (2 : ℂ) • verticalSegmentIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (1 + ε) (-T) T).im := by
  rw [regularizedPoitou_zeroFreeRectangle_identity K hδ hε hT hboundary]
  let S :=
    ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
        K (-ε) (1 + ε) (-T) T,
      poitouTransform (regularizedScaledTartar y δ) p *
        (completedDedekindZetaZeroDivisor K p : ℂ)
  have hS : 0 ≤ S.re := by
    dsimp [S]
    exact
      re_sum_poitouTransform_regularized_completedZetaZerosInClosedRectangle_nonneg
        K hy hδ (-ε) (1 + ε) (-T) T
  change 0 ≤ ((2 * Real.pi : ℂ) * Complex.I * S).im
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re,
    I_im, mul_zero, mul_one, sub_zero, add_zero]
  norm_num
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hp : 0 ≤ (2 : ℝ) * Real.pi :=
    mul_nonneg htwo Real.pi_pos.le
  exact mul_nonneg hp hS

end NumberField.Odlyzko
