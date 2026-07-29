/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RectangleIntegralLinear
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouPoleContour

/-!
# Regularized Poitou Subtracted Contour

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem regularizedPoitou_subtracted_centeredRectangle_im_lowerBound
    {y δ b T : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (hb : 1 < b) (hT : 0 < T)
    (hboundary : ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
      (z.re = 1 - b ∨ z.re = b ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    -4 * Real.pi *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          (1 - b) b (-T) -
        horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          b (-T) T).im := by
  let Φ : ℂ → ℂ :=
    poitouTransform (regularizedScaledTartar y δ)
  let qFull : ℂ → ℂ := fun s ↦
    Φ s * logDeriv (poleClearedCompletedDedekindZetaContinuation K) s
  let qPole : ℂ → ℂ := fun s ↦
    Φ s * completedZetaPoleLogDeriv s
  let qSub : ℂ → ℂ := fun s ↦
    Φ s * (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
      completedZetaPoleLogDeriv s)
  let z : ℂ := ((1 - b : ℝ) : ℂ) + -(T : ℂ) * I
  let w : ℂ := (b : ℂ) + (T : ℂ) * I
  have hab : 1 - b ≤ b := by linarith
  have huv : -T ≤ T := by linarith
  have hΦanalytic : AnalyticOnNhd ℂ Φ univ :=
    analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
  have hfullInt : RectangleBorderIntegrable qFull z w := by
    simpa only [z, w, ofReal_neg] using
      (rectangleBorderIntegrable_of_continuousAt_boundary
        (f := qFull) hab huv (by
          intro s hs hside
          unfold qFull logDeriv
          exact (hΦanalytic s (mem_univ s)).continuousAt.mul
            ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation
                K s (mem_univ s)).deriv.continuousAt.div
              (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation
                K s (mem_univ s)).continuousAt
              (hboundary s hs hside))))
  have hpoleInt : RectangleBorderIntegrable qPole z w := by
    simpa only [z, w, ofReal_neg] using
      (rectangleBorderIntegrable_of_continuousAt_boundary
        (f := qPole) hab huv (by
          intro s hs hside
          have hs0 : s ≠ 0 := by
            intro heq
            subst s
            simp only [zero_re, zero_im] at hside
            grind
          have hs1 : s ≠ 1 := by
            intro heq
            subst s
            simp only [one_re, one_im] at hside
            grind
          unfold qPole completedZetaPoleLogDeriv
          apply (hΦanalytic s (mem_univ s)).continuousAt.mul
          apply ContinuousAt.add
          · exact continuousAt_const.div continuousAt_id hs0
          · exact continuousAt_const.div
              (continuousAt_id.sub continuousAt_const)
              (sub_ne_zero.mpr hs1)))
  have hsubPointwise :
      qSub = fun s ↦ qFull s - qPole s := by grind
  have hrectSub :
      rectangleIntegral qSub z w =
        rectangleIntegral qFull z w - rectangleIntegral qPole z w := by
    rw [hsubPointwise]
    exact rectangleIntegral_sub hfullInt hpoleInt
  let EFull : ℂ :=
    horizontalIntegral qFull (1 - b) b (-T) -
      horizontalIntegral qFull (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qFull b (-T) T
  let EPole : ℂ :=
    horizontalIntegral qPole (1 - b) b (-T) -
      horizontalIntegral qPole (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qPole b (-T) T
  let ESub : ℂ :=
    horizontalIntegral qSub (1 - b) b (-T) -
      horizontalIntegral qSub (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qSub b (-T) T
  have hfullRect : EFull = rectangleIntegral qFull z w := by
    simpa only [EFull, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qFull)
        (fun s ↦
          regularizedPoitou_mul_completedZetaLogDeriv_one_sub K y δ s)).symm
  have hpoleRect : EPole = rectangleIntegral qPole z w := by
    simpa only [EPole, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qPole)
        (fun s ↦ mul_antiInvariant_of_invariant_of_antiInvariant
          (fun u ↦ poitouTransform_one_sub
            (regularizedScaledTartar_even y δ) u)
          completedZetaPoleLogDeriv_one_sub s)).symm
  have hsubAnti : ∀ s, qSub (1 - s) = -qSub s := by
    intro s
    dsimp only [qSub, Φ]
    rw [poitouTransform_one_sub (regularizedScaledTartar_even y δ),
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all K,
      completedZetaPoleLogDeriv_one_sub]
    ring
  have hsubRect : ESub = rectangleIntegral qSub z w := by
    simpa only [ESub, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qSub) hsubAnti).symm
  have hESub : ESub = EFull - EPole := by simp_all
  have hfullNonneg : 0 ≤ EFull.im := by
    have hε : 0 < b - 1 := by linarith
    have h :=
      regularizedPoitou_zeroFreeRectangle_im_nonneg
        K hy hδ hε hT.le
        (by
          simp_all)
    have hleft : -(b - 1) = 1 - b := by ring
    grind
  have hpole :
      EPole =
        4 * Real.pi * I *
          poitouTransform (regularizedScaledTartar y δ) 1 := by
    simpa only [EPole, qPole, Φ] using
      regularizedPoitou_completedZetaPole_centeredRectangle_identity
        hδ hb hT
  have hpoleIm :
      EPole.im =
        4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re := by
    rw [hpole]
    simp
  change -4 * Real.pi * (Φ 1).re ≤ ESub.im
  rw [hESub, sub_im, hpoleIm]
  nlinarith

end NumberField.Odlyzko
