/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.SplitCageNonparabolicComplementFrontier
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenNonparabolicComplementFrontier

/-!
# Split-cage Euler-seven nonparabolic complement frontier

The split-cage base discharges the even-sign inputs, while the middle game
uses the exact paired coefficient `189`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

/-- Exact Euler-seven nonparabolic complement frontier with the even-sign
invariance and factor-four hypotheses discharged by a split-cage base. -/
theorem
    puncturedMarkoffTransitiveAt_of_splitCage_nonparabolicComplement_eulerSevenPairedMaximalDivisor_frontier
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
      189 * maximalDivisorCountSum p (d + 1) ^ 3 < d)
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
    puncturedMarkoffTransitiveAt_of_nonparabolicComplement_eulerSevenPairedMaximalDivisor_frontier
      p (by omega) c hcube hlinear hlarge hsign hfour

end BGS.Markoff
