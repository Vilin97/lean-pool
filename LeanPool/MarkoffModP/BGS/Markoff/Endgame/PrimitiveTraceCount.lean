/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilBoundAssumption
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PowerCoverCounting

/-!
# Endgame point estimates after quotienting by the power maps

The Weil interfaces count points on the power-cover curves.  The paper's inclusion--exclusion
argument instead counts solutions on the two power-map images.  This file connects those two
levels exactly.  It proves the source's division by `d * e`, then divides the point-count error by
the same positive factor to obtain the uniform `O(sqrt q)` error used in equations (34)--(36).

Both split and corrected seeded nonsplit branches are covered.  The nonsplit equivalence uses the
actual base-field solution finset on the norm-one torus; it never replaces that finset by all
quadratic-field points.
-/

namespace BGS.Markoff

noncomputable section

/-- Dividing an exact `d * e`-sheeted cover count divides its Weil error by the same factor. -/
theorem rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (coverCount rangeCount fieldCard coefficient d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hcover : coverCount = d * e * rangeCount)
    (herror :
      |(coverCount : ℝ) - (fieldCard : ℝ)| ≤
        (coefficient : ℝ) * Real.sqrt (fieldCard : ℝ) * (d : ℝ) * (e : ℝ)) :
    |(rangeCount : ℝ) -
        (fieldCard : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (fieldCard : ℝ) := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have heReal : (0 : ℝ) < e := by exact_mod_cast he
  have hdeReal : (0 : ℝ) < (d : ℝ) * (e : ℝ) := mul_pos hdReal heReal
  have hcoverReal :
      (coverCount : ℝ) = (d : ℝ) * (e : ℝ) * (rangeCount : ℝ) := by
    exact_mod_cast hcover
  rw [hcoverReal] at herror
  have hidentity :
      (rangeCount : ℝ) - (fieldCard : ℝ) / ((d : ℝ) * (e : ℝ)) =
        (((d : ℝ) * (e : ℝ) * (rangeCount : ℝ) - (fieldCard : ℝ)) /
          ((d : ℝ) * (e : ℝ))) := by
    field_simp
  rw [hidentity, abs_div, abs_of_pos hdeReal]
  apply (div_le_iff₀ hdeReal).2
  simpa [mul_assoc] using herror

section Split

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- Solutions on the two power-map images for the weighted split trace equation. -/
abbrev splitTracePowerRangeSolutions
    (alpha beta : K) (d e : ℕ) :=
  powerTraceRangeSolutions
    (splitTorusTrace : Kˣ → K) (weightedSplitTorusTrace alpha beta) d e

/-- The finite-set model of the split trace cover is definitionally the same equation as the
generic two-power cover, up to reversing the displayed equality. -/
def splitTraceCurveSolutionsEquivPowerTraceCoverSolutions
    (alpha beta : K) (d e : ℕ) :
    ↥(splitTraceCurveSolutions K alpha beta d e) ≃
      powerTraceCoverSolutions
        (splitTorusTrace : Kˣ → K) (weightedSplitTorusTrace alpha beta) d e where
  toFun z := ⟨z.1, (mem_splitTraceCurveSolutions_iff K alpha beta d e z.1).mp z.2 |>.symm⟩
  invFun z := ⟨z.1,
    (mem_splitTraceCurveSolutions_iff K alpha beta d e z.1).mpr z.2.symm⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact source equation (32) for the split trace cover. -/
theorem splitTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
    (alpha beta : K) (d e : ℕ)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    (splitTraceCurveSolutions K alpha beta d e).card =
      d * e * Nat.card (splitTracePowerRangeSolutions K alpha beta d e) := by
  calc
    (splitTraceCurveSolutions K alpha beta d e).card =
        Nat.card ↥(splitTraceCurveSolutions K alpha beta d e) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe _).symm
    _ = Nat.card
        (powerTraceCoverSolutions
          (splitTorusTrace : Kˣ → K) (weightedSplitTorusTrace alpha beta) d e) :=
      Nat.card_congr
        (splitTraceCurveSolutionsEquivPowerTraceCoverSolutions K alpha beta d e)
    _ = d * e * Nat.card (splitTracePowerRangeSolutions K alpha beta d e) :=
      natCard_powerTraceCoverSolutions_of_dvd
        (splitTorusTrace : Kˣ → K) (weightedSplitTorusTrace alpha beta) d e hdvd hedvd

/-- Equation (34) for a concrete weighted split trace cover, derived from the explicit Weil
assumption only after Lean proves the cover's absolute irreducibility. -/
theorem splitTracePowerRangeSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ) (hWeil : WeightedSplitTraceWeilBoundAssumption coefficient)
    (alpha beta : K) (d e : ℕ)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hnondegenerate : alpha * beta ≠ 1)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0)
    (hdvd : d ∣ Nat.card Kˣ) (hedvd : e ∣ Nat.card Kˣ) :
    |(Nat.card (splitTracePowerRangeSolutions K alpha beta d e) : ℝ) -
        (Fintype.card K : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
  apply rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (splitTraceCurveSolutions K alpha beta d e).card
    (Nat.card (splitTracePowerRangeSolutions K alpha beta d e))
    (Fintype.card K) coefficient d e hd he
    (splitTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
      K alpha beta d e hdvd hedvd)
  exact splitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    K coefficient hWeil alpha beta d e halpha hbeta hnondegenerate hd he heChar

end Split

section Nonsplit

variable (p : ℕ) [Fact p.Prime]

/-- The unpowered left trace in the corrected seeded nonsplit equation. -/
def existingConicSeedNonsplitTorusTrace
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (w : quadraticNormOneTorus p) : ZMod p :=
  Algebra.trace (ZMod p) (quadraticFiniteField p)
    ((s.1 : quadraticFiniteField p) *
      ((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p))

/-- Solutions on the two power-map images for the corrected seeded nonsplit equation. -/
abbrev existingConicSeedNonsplitPowerRangeSolutions
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0)) (d e : ℕ) :=
  powerTraceRangeSolutions
    (existingConicSeedNonsplitTorusTrace p t ht ht0 s)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e

/-- The corrected nonsplit solution finset is exactly the corresponding generic two-power
cover over the norm-one torus and the base-field unit group. -/
def existingConicSeedNonsplitTraceCurveSolutionsEquivPowerTraceCoverSolutions
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0)) (d e : ℕ) :
    ↥(existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e) ≃
      powerTraceCoverSolutions
        (existingConicSeedNonsplitTorusTrace p t ht ht0 s)
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e where
  toFun z := ⟨z.1, by
    have hz :=
      (mem_existingConicSeedNonsplitTraceCurveSolutions_iff
        p t ht ht0 s d e z.1).mp z.2
    exact hz⟩
  invFun z := ⟨z.1,
    (mem_existingConicSeedNonsplitTraceCurveSolutions_iff
      p t ht ht0 s d e z.1).mpr z.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Exact source equation (32) for the corrected seeded nonsplit trace cover. -/
theorem existingConicSeedNonsplitTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0)) (d e : ℕ)
    (hdvd : d ∣ Nat.card (quadraticNormOneTorus p))
    (hedvd : e ∣ Nat.card (ZMod p)ˣ) :
    (existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e).card =
      d * e * Nat.card
        (existingConicSeedNonsplitPowerRangeSolutions p t ht ht0 s d e) := by
  calc
    (existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e).card =
        Nat.card ↥(existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe _).symm
    _ = Nat.card
        (powerTraceCoverSolutions
          (existingConicSeedNonsplitTorusTrace p t ht ht0 s)
          (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e) :=
      Nat.card_congr
        (existingConicSeedNonsplitTraceCurveSolutionsEquivPowerTraceCoverSolutions
          p t ht ht0 s d e)
    _ = d * e * Nat.card
        (existingConicSeedNonsplitPowerRangeSolutions p t ht ht0 s d e) :=
      natCard_powerTraceCoverSolutions_of_dvd
        (existingConicSeedNonsplitTorusTrace p t ht ht0 s)
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) d e hdvd hedvd

/-- Equation (34) for the corrected seeded nonsplit cover.  Its main term is `p / (d * e)`
because the counted solution set is over the base field. -/
theorem existingConicSeedNonsplitPowerRangeSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ) (hWeil : SeededNonsplitTraceWeilBoundAssumption coefficient)
    (hpTwo : p ≠ 2)
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0)) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hdChar : (d : quadraticFiniteField p) ≠ 0)
    (hdvd : d ∣ Nat.card (quadraticNormOneTorus p))
    (hedvd : e ∣ Nat.card (ZMod p)ˣ) :
    |(Nat.card
        (existingConicSeedNonsplitPowerRangeSolutions p t ht ht0 s d e) : ℝ) -
        (p : ℝ) / ((d : ℝ) * (e : ℝ))| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
  apply rangeCount_error_le_of_coverCount_error_and_exactMultiplicity
    (existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e).card
    (Nat.card (existingConicSeedNonsplitPowerRangeSolutions p t ht ht0 s d e))
    p coefficient d e hd he
    (existingConicSeedNonsplitTraceCurveSolutions_card_eq_mul_natCard_powerTraceRangeSolutions
      p t ht ht0 s d e hdvd hedvd)
  exact
    existingConicSeedNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
      coefficient hWeil p hpTwo t ht ht0 s d e hd he hdChar

end Nonsplit

end

end BGS.Markoff
