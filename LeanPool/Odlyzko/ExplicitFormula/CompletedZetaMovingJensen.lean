/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.VerticalGrowth
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaJensenCount

/-!
# Completed Zeta Moving Jensen

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta moving circle bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCircleBound (R t : ℝ) : ℝ :=
  max 1 <|
    poleClearedCompletedDedekindZetaVerticalBound K (2 - |R|) (2 + |R|) *
      (1 + |t| + |R|) ^ 2

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingCircleBound (R t : ℝ) :
    1 ≤ completedZetaMovingCircleBound K R t :=
  le_max_left _ _

theorem norm_poleClearedCompletedZeta_le_movingCircleBound
    (R t : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere (2 + t * I) |R|) :
    ‖poleClearedCompletedDedekindZetaContinuation K z‖ ≤
      completedZetaMovingCircleBound K R t := by
  have hdist : ‖z - (2 + t * I)‖ = |R| := by simp_all
  have hre : |z.re - 2| ≤ |R| := by
    calc
      |z.re - 2| = |(z - (2 + t * I)).re| := by simp
      _ ≤ ‖z - (2 + t * I)‖ := Complex.abs_re_le_norm _
      _ = |R| := hdist
  have him : |z.im - t| ≤ |R| := by
    calc
      |z.im - t| = |(z - (2 + t * I)).im| := by simp
      _ ≤ ‖z - (2 + t * I)‖ := Complex.abs_im_le_norm _
      _ = |R| := hdist
  have hzre : z.re ∈ Icc (2 - |R|) (2 + |R|) := by grind
  have : |z.im| ≤ |t| + |R| := by grind
  have hrepr : (z.re : ℂ) + z.im * I = z := by simp
  rw [← hrepr]
  calc
    ‖poleClearedCompletedDedekindZetaContinuation K
        ((z.re : ℂ) + z.im * I)‖ ≤
        poleClearedCompletedDedekindZetaVerticalBound K
            (2 - |R|) (2 + |R|) * (1 + |z.im|) ^ 2 :=
      norm_poleClearedCompletedDedekindZetaContinuation_vertical_le K hzre
    _ ≤ poleClearedCompletedDedekindZetaVerticalBound K
            (2 - |R|) (2 + |R|) * (1 + |t| + |R|) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_left₀
        · positivity
        · linarith
      · exact poleClearedCompletedDedekindZetaVerticalBound_nonneg K _ _
    _ ≤ completedZetaMovingCircleBound K R t := le_max_right _ _

theorem card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
    {a b u v r R t : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|)
    (hc : poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0)
    (hrect :
      Icc a b ×ℂ Icc u v ⊆ Metric.closedBall (2 + t * I) |r|) :
    ((completedDedekindZetaZerosInClosedRectangle K a b u v).card : ℝ) ≤
      Real.log
          (completedZetaMovingCircleBound K R t /
            ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖) /
        Real.log (R / r) := by
  exact card_completedDedekindZetaZerosInClosedRectangle_le_jensen K
    hr hrR (one_le_completedZetaMovingCircleBound K R t) hc
    (fun z hz ↦ norm_poleClearedCompletedZeta_le_movingCircleBound K R t hz)
    hrect

end NumberField.Odlyzko
