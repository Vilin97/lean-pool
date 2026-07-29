/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaRectangle
public import LeanPool.Odlyzko.ExplicitFormula.JensenZeroCount

/-!
# Completed Zeta Jensen Count

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem mem_divisor_closedBall_of_mem_completedZetaZeroDivisor_support
    {c z : ℂ} {r : ℝ} (hzball : z ∈ Metric.closedBall c |r|)
    (hz : z ∈ (completedDedekindZetaZeroDivisor K).support) :
    z ∈ Function.support
      (MeromorphicOn.divisor
        (poleClearedCompletedDedekindZetaContinuation K)
        (Metric.closedBall c |r|)) := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hΞ :
      MeromorphicOn Ξ (Metric.closedBall c |r|) :=
    fun z _ ↦
      (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K)
        z (mem_univ z) |>.meromorphicAt
  have hglobal :
      MeromorphicOn Ξ Set.univ :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
  intro hzero
  apply Function.mem_support.mp hz
  rw [completedDedekindZetaZeroDivisor,
    MeromorphicOn.divisor_apply hglobal (mem_univ z)]
  have hsmall :
      (MeromorphicOn.divisor Ξ (Metric.closedBall c |r|)) z =
        (meromorphicOrderAt Ξ z).untop₀ :=
    MeromorphicOn.divisor_apply hΞ hzball
  grind

open Classical in
theorem card_completedDedekindZetaZerosInClosedRectangle_le_jensen
    {a b u v : ℝ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc :
      poleClearedCompletedDedekindZetaContinuation K c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|,
      ‖poleClearedCompletedDedekindZetaContinuation K z‖ ≤ M)
    (hrect : Icc a b ×ℂ Icc u v ⊆ Metric.closedBall c |r|) :
    ((completedDedekindZetaZerosInClosedRectangle K a b u v).card : ℝ) ≤
      Real.log
          (M / ‖poleClearedCompletedDedekindZetaContinuation K c‖) /
        Real.log (R / r) := by
  apply AnalyticOnNhd.card_zeros_le hr hrR hM
    ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).mono
      (subset_univ _))
    hc f_bound
  intro z hz
  have hz' :=
    (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hz
  exact mem_divisor_closedBall_of_mem_completedZetaZeroDivisor_support K
    (hrect hz'.1) hz'.2

end NumberField.Odlyzko
