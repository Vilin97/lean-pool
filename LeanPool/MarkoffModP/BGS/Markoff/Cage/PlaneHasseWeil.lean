/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Cage.PlaneModels
import LeanPool.MarkoffModP.BGS.Markoff.Cage.HasseWeilAssumption

/-!
# Hasse--Weil estimates for the direct cage plane models

This file applies the single allowed general affine Hasse--Weil theorem to
the two explicit cage models.  It also proves that the divisor exponents
used by the cage are prime to the characteristic; that condition is not
left as a specialized assumption.
-/

namespace BGS.Markoff

noncomputable section

/-- A uniform point estimate for both direct cage plane models. -/
def CagePlanePointEstimate (coefficient : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p →
    ∀ (xi eta : ZMod p),
      IsSplitMaximalTrace p xi → IsSplitMaximalTrace p eta →
      ∀ d : ℕ, d ∣ p - 1 → 0 < d →
        |((BGS.External.affinePlaneCurveZeros (ZMod p)
              (cageDiagonalPlanePolynomial xi d)).card : ℝ) - p| ≤
            (coefficient : ℝ) * Real.sqrt p * d ∧
          (xi ^ 2 ≠ eta ^ 2 →
            |((BGS.External.affinePlaneCurveZeros (ZMod p)
                (cageOffDiagonalPlanePolynomial xi eta d)).card : ℝ) - p| ≤
              (coefficient : ℝ) * Real.sqrt p * d)

/-- A positive divisor of `p-1` is strictly smaller than `p`. -/
lemma divisor_pred_lt_prime {p d : ℕ} (hpTwo : 2 ≤ p)
    (hd : d ∣ p - 1) :
    d < p := by
  have hdLe : d ≤ p - 1 := Nat.le_of_dvd (by omega) hd
  omega

/-- The pulled-cover exponent `2d` is nonzero in `ZMod p` for every positive
divisor `d` of `p-1` and every prime `p ≥ 7`. -/
lemma two_mul_divisor_pred_ne_zero_zmod
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    {d : ℕ} (hd : d ∣ p - 1) (hdPositive : 0 < d) :
    (((2 * d : ℕ) : ZMod p)) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 * d := (ZMod.natCast_eq_zero_iff (2 * d) p).mp hzero
  rcases (Fact.out : p.Prime).dvd_mul.mp hpDvd with hpTwo | hpD
  · have hpLeTwo := Nat.le_of_dvd (by norm_num) hpTwo
    omega
  · have hdLt := divisor_pred_lt_prime (by omega) hd
    exact (Nat.not_dvd_of_pos_of_lt hdPositive hdLt) hpD

/-- A fixed-coefficient affine Hasse--Weil bound gives fixed uniform estimates
for both cage plane models. -/
theorem cagePlanePointEstimate_of_bivariateAffineHasseWeilBound
    (generalCoefficient : ℕ)
    (hgeneral : BGS.External.BivariateAffineHasseWeilBound generalCoefficient) :
    CagePlanePointEstimate (32 * generalCoefficient) := by
  let coefficient := 32 * generalCoefficient
  change CagePlanePointEstimate coefficient
  intro p _ hpSeven xi eta hxi heta d hd hdPositive
  have h2 : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (n := 2) (p := p) (by norm_num) (by omega)
  have hdegree : (((2 * d : ℕ) : ZMod p)) ≠ 0 :=
    two_mul_divisor_pred_ne_zero_zmod p hpSeven hd hdPositive
  have hxiNonzero := splitMaximalTrace_ne_zero p hpSeven xi hxi
  have hetaNonzero := splitMaximalTrace_ne_zero p hpSeven eta heta
  have hXi := sub_ne_zero.mpr (splitMaximalTrace_sq_ne_four p hpSeven xi hxi)
  have hEta := sub_ne_zero.mpr (splitMaximalTrace_sq_ne_four p hpSeven eta heta)
  have hDiagonal := hgeneral (ZMod p)
    (cageDiagonalPlanePolynomial xi d) 2 (4 * d)
    (by norm_num) (by omega)
    (cageDiagonalPlanePolynomial_hasBidegreeAtMost xi d)
    (cageDiagonalPlanePolynomial_absolutelyIrreducible
      hxiNonzero hXi hdPositive h2 hdegree)
  constructor
  · have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hcard] at hDiagonal
    dsimp [coefficient]
    calc
      |((BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageDiagonalPlanePolynomial xi d)).card : ℝ) - p| ≤
          (generalCoefficient : ℝ) * Real.sqrt p *
            ((2 : ℕ) : ℝ) * (((4 * d : ℕ) : ℝ)) := hDiagonal
      _ = (8 * generalCoefficient : ℝ) * Real.sqrt p * d := by
        push_cast
        ring
      _ ≤ (((32 * generalCoefficient : ℕ) : ℝ)) * Real.sqrt p * d := by
        push_cast
        have hnonnegative :
            0 ≤ (generalCoefficient : ℝ) * Real.sqrt p * (d : ℝ) := by
          positivity
        nlinarith
  · intro hoffDiagonal
    have hOffDiagonal := hgeneral (ZMod p)
      (cageOffDiagonalPlanePolynomial xi eta d) 4 (8 * d)
      (by norm_num) (by omega)
      (cageOffDiagonalPlanePolynomial_hasBidegreeAtMost xi eta d)
      (cageOffDiagonalPlanePolynomial_absolutelyIrreducible
        hxiNonzero hetaNonzero hXi hEta hoffDiagonal hdPositive h2 hdegree)
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hcard] at hOffDiagonal
    dsimp [coefficient]
    calc
      |((BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageOffDiagonalPlanePolynomial xi eta d)).card : ℝ) - p| ≤
          (generalCoefficient : ℝ) * Real.sqrt p *
            ((4 : ℕ) : ℝ) * (((8 * d : ℕ) : ℝ)) := hOffDiagonal
      _ = (((32 * generalCoefficient : ℕ) : ℝ)) * Real.sqrt p * d := by
        push_cast
        ring

/-- The allowed general Hasse--Weil theorem gives uniform estimates for both
the diagonal and off-diagonal cage plane models. -/
theorem exists_cagePlanePointEstimate_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ, 0 < coefficient ∧ CagePlanePointEstimate coefficient := by
  obtain ⟨generalCoefficient, hgeneralCoefficient, hgeneral⟩ := hHasse
  exact ⟨32 * generalCoefficient, by omega,
    cagePlanePointEstimate_of_bivariateAffineHasseWeilBound
      generalCoefficient hgeneral⟩

/-- Divide an exact `d`-fold cover estimate by its fiber multiplicity.  This
is the numerical step used after the geometric count comparison. -/
lemma range_count_error_of_exact_cover
    {coverCard rangeCard p d multiplicity : ℕ} {error : ℝ}
    (hd : 0 < d) (hcover : coverCard = d * rangeCard)
    (herror :
      |(coverCard : ℝ) - (multiplicity : ℝ) * p| ≤
        error * d) :
    |(rangeCard : ℝ) - (multiplicity : ℝ) * p / d| ≤ error := by
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdNonnegative : (0 : ℝ) ≤ d := by positivity
  have hidentity :
      |(rangeCard : ℝ) - (multiplicity : ℝ) * p / d| =
        |(coverCard : ℝ) - (multiplicity : ℝ) * p| / d := by
    rw [hcover]
    push_cast
    calc
      |(rangeCard : ℝ) - (multiplicity : ℝ) * p / d| =
          |((d : ℝ) * rangeCard - (multiplicity : ℝ) * p) / d| := by
        congr 1
        field_simp [hdReal]
      _ = |(d : ℝ) * rangeCard - (multiplicity : ℝ) * p| / |(d : ℝ)| :=
        abs_div _ _
      _ = |(d : ℝ) * rangeCard - (multiplicity : ℝ) * p| / d := by
        rw [abs_of_nonneg hdNonnegative]
  rw [hidentity]
  calc
    |(coverCard : ℝ) - (multiplicity : ℝ) * p| / d ≤
        (error * d) / d := div_le_div_of_nonneg_right herror hdNonnegative
    _ = error := by field_simp [hdReal]

end

end BGS.Markoff
