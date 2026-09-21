/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.SplitCageEvenSignBase
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EvenSignBaseStableComplement
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicComplementFrontier

/-!
# Split-cage nonparabolic complement frontier

The split-cage base supplies the only geometric input needed for the
even-sign factor four: every signed image of the base point returns to its
Gamma component. This module discharges both sign-invariance hypotheses of
the nonparabolic complement frontier automatically.
-/

namespace BGS.Markoff

open BGS.NumberTheory

/-- A split-cage base above the half-order threshold has a component
complement whose cardinality is divisible by four. -/
theorem four_dvd_puncturedComponentComplementFinset_card_of_splitCageBase
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p
      (normalizedSurfaceOfPunctured
        (puncturedNormalizationEquiv (ZMod p) c)))
    (hhalfThreshold :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    4 ∣ (puncturedComponentComplementFinset p c).card := by
  apply
    four_dvd_puncturedComponentComplementFinset_card_of_base_sign_stable
      p (by omega) c
  exact samePuncturedComponent_evenSign_smul_of_splitCageBase
    p hpSeven c hbase hhalfThreshold hlarge

/-- Nonparabolic paired-maximal-divisor frontier with the even-sign
invariance and factor-four hypotheses discharged by a split-cage base. -/
theorem
    puncturedMarkoffTransitiveAt_of_splitCage_nonparabolicComplement_pairedMaximalDivisor_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p
      (normalizedSurfaceOfPunctured
        (puncturedNormalizationEquiv (ZMod p) c)))
    (hhalfThreshold :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ))
    (hcube : ∀ d : ℕ, 0 < d →
      8 * p ≤
        (d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      (6 * maximalDivisorCountSum p (d + 1)) ^ 3 < d)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 * maximalDivisorCountSum p (d + 1) * d < p)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  have hbaseSign :
      ∀ s : EvenSign, SamePuncturedComponent c (s • c) :=
    samePuncturedComponent_evenSign_smul_of_splitCageBase
      p hpSeven c hbase hhalfThreshold hlarge
  have hsign :
      ∀ (s : EvenSign) (x : PuncturedMarkoffSurface (ZMod p)),
        s • x ∈ puncturedComponentComplementFinset p c ↔
          x ∈ puncturedComponentComplementFinset p c :=
    fun s x =>
      puncturedComponentComplementFinset_evenSign_mem_iff_of_base_stable
        p c x hbaseSign s
  have hfour :
      4 ∣ (puncturedComponentComplementFinset p c).card :=
    four_dvd_puncturedComponentComplementFinset_card_of_base_sign_stable
      p (by omega) c hbaseSign
  exact
    puncturedMarkoffTransitiveAt_of_nonparabolicComplement_pairedMaximalDivisor_frontier
      p (by omega) c hcube hlinear hlarge hsign hfour

end BGS.Markoff
