/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.PlaneCountComparison
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.AxisEquivalence
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.SmallPrime

/-!
# Transferring plane estimates to the cage witness count

This file combines the geometric Hasse--Weil estimates, the explicit plane
comparison, the exact `d`-fold power-cover multiplicity, and the all-axis
equivalence.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The pulled cage radicand depends on a trace only through its square. -/
lemma cagePulledRadicand_eq_of_sq_eq
    {K : Type*} [Field K] {xi eta : K} (d : ℕ)
    (h : xi ^ 2 = eta ^ 2) :
    cagePulledRadicand xi d = cagePulledRadicand eta d := by
  simp only [cagePulledRadicand, h]

/-- Replacing either cage trace by another trace with the same square does
not change the pulled root-pair cover. -/
def cagePulledRootPairEquivOfSqEq
    (p : ℕ) [Fact p.Prime] (xi eta eta' : ZMod p) (d : ℕ)
    (h : eta ^ 2 = eta' ^ 2) :
    CagePulledRootPair p xi eta d ≃ CagePulledRootPair p xi eta' d where
  toFun z :=
    { parameter := z.parameter
      firstRoot := z.firstRoot
      secondRoot := z.secondRoot
      firstEquation := z.firstEquation
      secondEquation := by
        rw [← cagePulledRadicand_eq_of_sq_eq d h]
        exact z.secondEquation }
  invFun z :=
    { parameter := z.parameter
      firstRoot := z.firstRoot
      secondRoot := z.secondRoot
      firstEquation := z.firstEquation
      secondEquation := by
        rw [cagePulledRadicand_eq_of_sq_eq d h]
        exact z.secondEquation }
  left_inv z := by
    apply CagePulledRootPair.ext <;> rfl
  right_inv z := by
    apply CagePulledRootPair.ext <;> rfl

lemma natCard_cagePulledRootPair_eq_of_sq_eq
    (p : ℕ) [Fact p.Prime] (xi eta eta' : ZMod p) (d : ℕ)
    (h : eta ^ 2 = eta' ^ 2) :
    Nat.card (CagePulledRootPair p xi eta d) =
      Nat.card (CagePulledRootPair p xi eta' d) := by
  exact Nat.card_congr (cagePulledRootPairEquivOfSqEq p xi eta eta' d h)

/-- The diagonal plane estimate gives the canonical cage range estimate with
the correct geometric multiplicity two. -/
lemma canonicalDiagonalCageRangeEstimate
    (planeCoefficient : ℕ) (hPlane : CagePlanePointEstimate planeCoefficient)
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    (xi : ZMod p) (hxi : IsSplitMaximalTrace p xi)
    (d : ℕ) (hd : d ∣ Nat.card (ZMod p)ˣ) (hdPositive : 0 < d) :
    |(Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi xi d) : ℝ) -
        (2 : ℝ) * p / d| ≤
      ((2 * planeCoefficient + 8 : ℕ) : ℝ) * Real.sqrt p := by
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hdPred : d ∣ p - 1 := by
    rw [← hcard]
    exact hd
  have hpTwo : p ≠ 2 := by omega
  have hXi := sub_ne_zero.mpr (splitMaximalTrace_sq_ne_four p hpSeven xi hxi)
  have hcomparisonInt := cagePulledRootPair_diagonal_card_comparison
    p hpTwo xi hdPositive hXi
  have hcomparison :
      |(Nat.card (CagePulledRootPair p xi xi d) : ℝ) -
          2 * (BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageDiagonalPlanePolynomial xi d)).card| ≤
        (4 * d + 4 : ℕ) := by
    exact_mod_cast hcomparisonInt
  have hHasse := (hPlane p hpSeven xi xi hxi hxi d hdPred hdPositive).1
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    have hpNonnegative : (0 : ℝ) ≤ p := by positivity
    have hsquare := Real.sq_sqrt hpNonnegative
    have hsqrtNonnegative := Real.sqrt_nonneg (p : ℝ)
    have hpSevenReal : (7 : ℝ) ≤ p := by exact_mod_cast hpSeven
    nlinarith
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPositive
  have hexception : ((4 * d + 4 : ℕ) : ℝ) ≤
      8 * Real.sqrt p * d := by
    push_cast
    nlinarith
  have hcoverError :
      |(Nat.card (CagePulledRootPair p xi xi d) : ℝ) - (2 : ℝ) * p| ≤
        (((2 * planeCoefficient + 8 : ℕ) : ℝ) * Real.sqrt p) * d := by
    let planeCard := (BGS.External.affinePlaneCurveZeros (ZMod p)
      (cageDiagonalPlanePolynomial xi d)).card
    calc
      |(Nat.card (CagePulledRootPair p xi xi d) : ℝ) - (2 : ℝ) * p| =
          |((Nat.card (CagePulledRootPair p xi xi d) : ℝ) -
              2 * planeCard) + 2 * ((planeCard : ℝ) - p)| := by
        congr 1
        ring
      _ ≤ |(Nat.card (CagePulledRootPair p xi xi d) : ℝ) -
              2 * planeCard| + |2 * ((planeCard : ℝ) - p)| := abs_add_le _ _
      _ = |(Nat.card (CagePulledRootPair p xi xi d) : ℝ) -
              2 * planeCard| + 2 * |(planeCard : ℝ) - p| := by
        rw [abs_mul]
        norm_num
      _ ≤ ((4 * d + 4 : ℕ) : ℝ) +
            2 * ((planeCoefficient : ℝ) * Real.sqrt p * d) := by
        gcongr
      _ ≤ 8 * Real.sqrt p * d +
            2 * ((planeCoefficient : ℝ) * Real.sqrt p * d) := by
        gcongr
      _ = (((2 * planeCoefficient + 8 : ℕ) : ℝ) * Real.sqrt p) * d := by
        push_cast
        ring
  apply range_count_error_of_exact_cover hdPositive
    (natCard_cagePulledRootPair_eq_mul_canonicalPowerRange
      p hpTwo xi xi d hdPred)
  simpa only [Nat.cast_ofNat] using hcoverError

/-- When the two cage traces have the same square, their pulled radicands
coincide and the diagonal multiplicity-two estimate applies unchanged. -/
lemma canonicalEqualSquareCageRangeEstimate
    (planeCoefficient : ℕ) (hPlane : CagePlanePointEstimate planeCoefficient)
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    (xi eta : ZMod p)
    (hxi : IsSplitMaximalTrace p xi)
    (hsquare : xi ^ 2 = eta ^ 2)
    (d : ℕ) (hd : d ∣ Nat.card (ZMod p)ˣ) (hdPositive : 0 < d) :
    |(Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi eta d) : ℝ) -
        (2 : ℝ) * p / d| ≤
      ((2 * planeCoefficient + 8 : ℕ) : ℝ) * Real.sqrt p := by
  have hpTwo : p ≠ 2 := by omega
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hdPred : d ∣ p - 1 := by
    rw [← hcard]
    exact hd
  have hpulled :
      Nat.card (CagePulledRootPair p xi eta d) =
        Nat.card (CagePulledRootPair p xi xi d) :=
    natCard_cagePulledRootPair_eq_of_sq_eq p xi eta xi d hsquare.symm
  have hcoverEta := natCard_cagePulledRootPair_eq_mul_canonicalPowerRange
    p hpTwo xi eta d hdPred
  have hcoverXi := natCard_cagePulledRootPair_eq_mul_canonicalPowerRange
    p hpTwo xi xi d hdPred
  have hrange :
      Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi eta d) =
        Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi xi d) := by
    rw [hpulled] at hcoverEta
    rw [hcoverXi] at hcoverEta
    exact Nat.eq_of_mul_eq_mul_left hdPositive hcoverEta.symm
  rw [hrange]
  exact canonicalDiagonalCageRangeEstimate planeCoefficient hPlane p hpSeven
    xi hxi d hd hdPositive

/-- Away from the equal-square diagonal, the primitive quartic plane model
has the same main term as the pulled root-pair cover, up to its explicitly
bounded exceptional fibers. -/
lemma canonicalOffDiagonalCageRangeEstimate
    (planeCoefficient : ℕ) (hPlane : CagePlanePointEstimate planeCoefficient)
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    (xi eta : ZMod p)
    (hxi : IsSplitMaximalTrace p xi)
    (heta : IsSplitMaximalTrace p eta)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2)
    (d : ℕ) (hd : d ∣ Nat.card (ZMod p)ˣ) (hdPositive : 0 < d) :
    |(Nat.card (cageMiddleWitnessPowerRangeSolutions
          p .first .second xi eta d) : ℝ) -
        (p : ℝ) / d| ≤
      ((planeCoefficient + 10 : ℕ) : ℝ) * Real.sqrt p := by
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hdPred : d ∣ p - 1 := by
    rw [← hcard]
    exact hd
  have hpTwo : p ≠ 2 := by omega
  have hcomparisonInt := cagePulledRootPair_offDiagonal_card_comparison
    p hpTwo xi eta hdPositive hoffDiagonal
  have hcomparison :
      |(Nat.card (CagePulledRootPair p xi eta d) : ℝ) -
          (BGS.External.affinePlaneCurveZeros (ZMod p)
            (cageOffDiagonalPlanePolynomial xi eta d)).card| ≤
        (6 * d + 4 : ℕ) := by
    exact_mod_cast hcomparisonInt
  have hHasse :=
    (hPlane p hpSeven xi eta hxi heta d hdPred hdPositive).2 hoffDiagonal
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    have hpNonnegative : (0 : ℝ) ≤ p := by positivity
    have hsquare := Real.sq_sqrt hpNonnegative
    have hsqrtNonnegative := Real.sqrt_nonneg (p : ℝ)
    have hpSevenReal : (7 : ℝ) ≤ p := by exact_mod_cast hpSeven
    nlinarith
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPositive
  have hexception : ((6 * d + 4 : ℕ) : ℝ) ≤
      10 * Real.sqrt p * d := by
    push_cast
    nlinarith
  have hcoverError :
      |(Nat.card (CagePulledRootPair p xi eta d) : ℝ) - (p : ℝ)| ≤
        (((planeCoefficient + 10 : ℕ) : ℝ) * Real.sqrt p) * d := by
    let planeCard := (BGS.External.affinePlaneCurveZeros (ZMod p)
      (cageOffDiagonalPlanePolynomial xi eta d)).card
    calc
      |(Nat.card (CagePulledRootPair p xi eta d) : ℝ) - (p : ℝ)| =
          |((Nat.card (CagePulledRootPair p xi eta d) : ℝ) - planeCard) +
            ((planeCard : ℝ) - p)| := by
        congr 1
        ring
      _ ≤ |(Nat.card (CagePulledRootPair p xi eta d) : ℝ) - planeCard| +
            |((planeCard : ℝ) - p)| := abs_add_le _ _
      _ ≤ ((6 * d + 4 : ℕ) : ℝ) +
            ((planeCoefficient : ℝ) * Real.sqrt p * d) := by
        gcongr
      _ ≤ 10 * Real.sqrt p * d +
            ((planeCoefficient : ℝ) * Real.sqrt p * d) := by
        gcongr
      _ = (((planeCoefficient + 10 : ℕ) : ℝ) * Real.sqrt p) * d := by
        push_cast
        ring
  have hrange := range_count_error_of_exact_cover
    (coverCard := Nat.card (CagePulledRootPair p xi eta d))
    (rangeCard := Nat.card (cageMiddleWitnessPowerRangeSolutions
      p .first .second xi eta d))
    (p := p) (d := d) (multiplicity := 1)
    (error := ((planeCoefficient + 10 : ℕ) : ℝ) * Real.sqrt p)
    hdPositive
    (natCard_cagePulledRootPair_eq_mul_canonicalPowerRange
      p hpTwo xi eta d hdPred)
    (by simpa only [Nat.cast_one, one_mul] using hcoverError)
  simpa only [Nat.cast_one, one_mul] using hrange

/-- A fixed cage-plane estimate supplies the corresponding fixed witness
estimate.  The proof chooses the geometric multiplicity only after splitting
the genuine equal-square and off-diagonal cases. -/
theorem cageWitnessPointEstimate_of_cagePlanePointEstimate
    (planeCoefficient : ℕ) (hPlane : CagePlanePointEstimate planeCoefficient) :
    CageWitnessPointEstimate (100000 + 2 * planeCoefficient + 10) := by
  let coefficient := 100000 + 2 * planeCoefficient + 10
  change CageWitnessPointEstimate coefficient
  intro p _ hpFive axis other xi eta hxi heta
  by_cases hpIsFive : p = 5
  · subst p
    obtain ⟨multiplicity, hmultiplicity, hestimate⟩ :=
      cageWitnessPointEstimate_five axis other xi eta hxi heta
    refine ⟨multiplicity, hmultiplicity, ?_⟩
    intro d hd hdPositive
    calc
      |(Nat.card (cageMiddleWitnessPowerRangeSolutions
            5 axis other xi eta d) : ℝ) -
          (multiplicity : ℝ) * (5 : ℝ) / d| ≤
          (100000 : ℝ) * Real.sqrt 5 := hestimate d hd hdPositive
      _ ≤ (coefficient : ℝ) * Real.sqrt 5 := by
        have hsqrtNonnegative : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
        dsimp [coefficient]
        push_cast
        nlinarith
  · have hpNotSix : p ≠ 6 := by
      intro hpSix
      subst p
      have hprime : Nat.Prime 6 := Fact.out
      norm_num at hprime
    have hpSeven : 7 ≤ p := by omega
    by_cases hsquare : xi ^ 2 = eta ^ 2
    · refine ⟨2, by norm_num, ?_⟩
      intro d hd hdPositive
      rw [natCard_cageMiddleWitnessPowerRangeSolutions_eq_canonical
        p axis other xi eta d]
      calc
        |(Nat.card (cageMiddleWitnessPowerRangeSolutions
              p .first .second xi eta d) : ℝ) -
            (2 : ℝ) * p / d| ≤
            ((2 * planeCoefficient + 8 : ℕ) : ℝ) * Real.sqrt p :=
          canonicalEqualSquareCageRangeEstimate planeCoefficient hPlane
            p hpSeven xi eta hxi hsquare d hd hdPositive
        _ ≤ (coefficient : ℝ) * Real.sqrt p := by
          have hsqrtNonnegative : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg p
          dsimp [coefficient]
          push_cast
          nlinarith

    · refine ⟨1, by norm_num, ?_⟩
      intro d hd hdPositive
      rw [natCard_cageMiddleWitnessPowerRangeSolutions_eq_canonical
        p axis other xi eta d]
      norm_num only [Nat.cast_one, one_mul]
      calc
        |(Nat.card (cageMiddleWitnessPowerRangeSolutions
              p .first .second xi eta d) : ℝ) -
            (p : ℝ) / d| ≤
            ((planeCoefficient + 10 : ℕ) : ℝ) * Real.sqrt p :=
          canonicalOffDiagonalCageRangeEstimate planeCoefficient hPlane
            p hpSeven xi eta hxi heta hsquare d hd hdPositive
        _ ≤ (coefficient : ℝ) * Real.sqrt p := by
          have hsqrtNonnegative : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg p
          have hplaneNonnegative : (0 : ℝ) ≤ planeCoefficient := by positivity
          dsimp [coefficient]
          push_cast
          nlinarith

/-- The single allowed general affine Hasse--Weil theorem supplies the full
cage witness estimate. -/
theorem exists_cageWitnessPointEstimate_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ, 0 < coefficient ∧ CageWitnessPointEstimate coefficient := by
  obtain ⟨planeCoefficient, _hplanePositive, hPlane⟩ :=
    exists_cagePlanePointEstimate_of_generalHasseWeil hHasse
  exact ⟨100000 + 2 * planeCoefficient + 10, by omega,
    cageWitnessPointEstimate_of_cagePlanePointEstimate planeCoefficient hPlane⟩

end

end BGS.Markoff
