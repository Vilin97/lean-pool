/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaCenterLogBound
public import LeanPool.Odlyzko.ExplicitFormula.QuantitativeZeroFreeHeights

/-!
# Selected Height Log Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta selected height ordinates used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightOrdinates (A : ℝ) : Finset ℝ :=
  completedDedekindZetaZeroAbsoluteOrdinatesInBands K (-3) 7 (A - 5) (A + 6)

open Classical in
/-- A completed zeta selected height separation used in the Odlyzko-bound argument. -/
noncomputable def completedZetaSelectedHeightSeparation (A : ℝ) : ℝ :=
  finiteSetAvoidanceRadiusOnLength 1
    (completedZetaSelectedHeightOrdinates K A)

omit [IsTotallyComplex K] in
open Classical in
theorem completedZetaSelectedHeightSeparation_pos (A : ℝ) :
    0 < completedZetaSelectedHeightSeparation K A :=
  finiteSetAvoidanceRadiusOnLength_pos one_pos _

omit [IsTotallyComplex K] in
open Classical in
private theorem horizontal_segment_separated_from_local_zeros
    {A t δ : ℝ} (hAt : A < |t|) (htA : |t| < A + 1)
    (hzeroSep : ∀ p : ℂ,
      p.re ∈ Icc (-3 : ℝ) 7 →
      |p.im| ∈ Icc (A - 5) (A + 6) →
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ |t - p.im|)
    {x : ℝ} (_hx : x ∈ Icc (-1 : ℝ) 5) :
    ∀ p ∈ ball (2 + t * I) 5,
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ ‖(x + t * I) - p‖ := by
  intro p hp hpzero
  have hdist : ‖p - (2 + t * I)‖ < 5 := by
    simpa [mem_ball, dist_eq, norm_sub_rev] using hp
  have hreDist : |p.re - 2| < 5 := by
    simpa using
      (Complex.abs_re_le_norm (p - (2 + t * I))).trans_lt hdist
  have himDist : |p.im - t| < 5 := by
    simpa using
      (Complex.abs_im_le_norm (p - (2 + t * I))).trans_lt hdist
  have hpRe : p.re ∈ Icc (-3 : ℝ) 7 := by
    grind
  have habsLower : A - 5 ≤ |p.im| := by
    grind
  have habsUpper : |p.im| ≤ A + 6 := by grind
  have hvertical : δ ≤ |t - p.im| :=
    hzeroSep p hpRe ⟨habsLower, habsUpper⟩ hpzero
  exact hvertical.trans (by
    have himNorm := Complex.abs_im_le_norm ((x + t * I : ℂ) - p)
    simpa using himNorm)

open Classical in
theorem exists_height_norm_logDeriv_poleClearedCompletedZeta_le
    {A : ℝ} (hA : 6 ≤ A) :
    ∃ T : ℝ, A < T ∧ T < A + 1 ∧
      ∀ x ∈ Icc (-1 : ℝ) 5,
        (poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x + T * I)‖ ≤
          (completedZetaCenterLogLinearBound K T *
                completedZetaCanonicalJensenCoefficient /
              completedZetaSelectedHeightSeparation K A +
            completedZetaCenterLogLinearBound K T *
              completedZetaCanonicalJensenCoefficient) +
            32 * completedZetaCenterLogLinearBound K T) ∧
        (poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 ∧
        ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K)
            (x - T * I)‖ ≤
          (completedZetaCenterLogLinearBound K (-T) *
                completedZetaCanonicalJensenCoefficient /
              completedZetaSelectedHeightSeparation K A +
            completedZetaCenterLogLinearBound K (-T) *
              completedZetaCanonicalJensenCoefficient) +
            32 * completedZetaCenterLogLinearBound K (-T)) := by
  let δ := completedZetaSelectedHeightSeparation K A
  obtain ⟨T, hAT, hTA, hsep⟩ :=
    exists_completedZeta_height_separated_from_zeros_in_bands
      K (-3) 7 (A - 5) (A := A) (L := 1) (V := A + 6)
      (by linarith) one_pos
  have hδ : 0 < δ := completedZetaSelectedHeightSeparation_pos K A
  have hsepPlus :
      ∀ p : ℂ, p.re ∈ Icc (-3 : ℝ) 7 →
        |p.im| ∈ Icc (A - 5) (A + 6) →
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ |T - p.im| := by
    intro p hpRe hpIm hpzero
    exact (hsep p hpRe hpIm hpzero).1
  have hsepMinus :
      ∀ p : ℂ, p.re ∈ Icc (-3 : ℝ) 7 →
        |p.im| ∈ Icc (A - 5) (A + 6) →
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ |-T - p.im| := by
    intro p hpRe hpIm hpzero
    exact (hsep p hpRe hpIm hpzero).2
  refine ⟨T, hAT, hTA, ?_⟩
  intro x hx
  have hxabs : |x - 2| ≤ 3 := by grind
  have hnormPlus :
      ‖(x + T * I : ℂ) - (2 + T * I)‖ ≤ 3 := by
    rw [show (x + T * I : ℂ) - (2 + T * I) = ((x - 2 : ℝ) : ℂ) by
      simp, Complex.norm_real]
    exact hxabs
  have hnormMinus :
      ‖(x - T * I : ℂ) - (2 + ((-T : ℝ) : ℂ) * I)‖ ≤ 3 := by
    rw [show (x - T * I : ℂ) - (2 + ((-T : ℝ) : ℂ) * I) =
        ((x - 2 : ℝ) : ℂ) by
      push_cast
      ring, Complex.norm_real]
    exact hxabs
  have hzPlus : x + T * I ∈ closedBall (2 + T * I) 3 := by
    rw [mem_closedBall, dist_eq]
    simp_all
  have hzMinus :
      x - T * I ∈ closedBall (2 + ((-T : ℝ) : ℂ) * I) 3 := by simp_all
  have hlocalPlus :=
    horizontal_segment_separated_from_local_zeros K
      (A := A) (t := T) (δ := δ)
      (by grind) (by grind)
      hsepPlus hx
  have hlocalMinus :=
    horizontal_segment_separated_from_local_zeros K
      (A := A) (t := -T) (δ := δ)
      (by grind)
      (by grind)
      hsepMinus hx
  have hlocalMinus' :
      ∀ p ∈ ball (2 + ((-T : ℝ) : ℂ) * I) 5,
        poleClearedCompletedDedekindZetaContinuation K p = 0 →
        δ ≤ ‖(x - T * I) - p‖ := by
    intro p hp hpzero
    (convert hlocalMinus p hp hpzero using 1; push_cast; ring_nf)
  have hfPlus :
      poleClearedCompletedDedekindZetaContinuation K (x + T * I) ≠ 0 := by
    intro hzero
    have := hlocalPlus (x + T * I)
      (by
        rw [mem_ball, dist_eq]
        linarith)
      hzero
    rw [sub_self, norm_zero] at this
    grind
  have hfMinus :
      poleClearedCompletedDedekindZetaContinuation K (x - T * I) ≠ 0 := by
    intro hzero
    have := hlocalMinus' (x - T * I)
      (by
        rw [mem_ball, dist_eq]
        linarith)
      hzero
    rw [sub_self, norm_zero] at this
    grind
  refine ⟨⟨hfPlus, ?_⟩, ⟨hfMinus, ?_⟩⟩
  · exact norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation K
      hδ (lt_of_lt_of_le zero_lt_one
        (one_le_completedZetaCenterLogLinearBound K T))
      (completedZeta_center_log_gap_le K (by
        grind))
      hzPlus hfPlus hlocalPlus
  · have hbound :=
      norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation K
        hδ (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaCenterLogLinearBound K (-T)))
        (completedZeta_center_log_gap_le K (by
          grind))
        hzMinus hfMinus hlocalMinus'
    grind

end NumberField.Odlyzko
