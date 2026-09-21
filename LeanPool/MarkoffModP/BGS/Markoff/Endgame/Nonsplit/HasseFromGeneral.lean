/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.DescendedIrreducibility
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilBoundAssumption

/-!
# The nonsplit endgame estimate from the general affine Hasse--Weil theorem

This file applies the single permitted general Hasse--Weil input to the explicit descended
plane curve.  The identity point omitted by the Cayley chart is kept visible and bounded
separately; it is not folded into a specialized estimate assumption.
-/

namespace BGS.Markoff

noncomputable section

/-- A fixed-coefficient affine Hasse--Weil bound supplies the correspondingly
fixed seeded nonsplit estimate.  The coefficient `4*C + 2` records the
`(2d,2e)` bidegree and the at-most `2e` Cayley-chart boundary. -/
theorem seededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
    (generalCoefficient : ℕ)
    (hgeneral : BGS.External.BivariateAffineHasseWeilBound generalCoefficient) :
    SeededNonsplitTraceWeilBoundAssumption (4 * generalCoefficient + 2) := by
  let coefficient := 4 * generalCoefficient + 2
  change SeededNonsplitTraceWeilBoundAssumption coefficient
  refine ⟨by dsimp [coefficient]; omega, ?_⟩
  intro p _ hpTwo t ht ht0 s d e hd he hirreducible
  have hDescendedIrreducible :=
    seededNonsplitDescendedPolynomial_absolutelyIrreducible_of_splitCover
      p s.1 d e hd he hirreducible
  have hAffine := hgeneral (ZMod p)
    (seededNonsplitDescendedPolynomial p s.1 d e)
    (2 * d) (2 * e) (by omega) (by omega)
    (seededNonsplitDescendedPolynomial_hasBidegreeAtMost p s.1 d e)
    hDescendedIrreducible
  have hCardNat :=
    existingConicSeedNonsplitTraceCurveSolutions_card_eq_affine_add_identityBoundary
      p t ht ht0 s d e hd he
  have hBoundaryNat := seededNonsplitIdentityBoundarySolutions_card_le p
    (quadraticFiberProductUnit p t ht ht0) s d e he
  let affineCard :=
    (BGS.External.affinePlaneCurveZeros (ZMod p)
      (seededNonsplitDescendedPolynomial p s.1 d e)).card
  let boundaryCard :=
    (seededNonsplitIdentityBoundarySolutions p
      (quadraticFiberProductUnit p t ht ht0) s d e).card
  let x : ℝ := Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ)
  have hCardReal :
      ((existingConicSeedNonsplitTraceCurveSolutions
          p t ht ht0 s d e).card : ℝ) = affineCard + boundaryCard := by
    dsimp only [affineCard, boundaryCard]
    exact_mod_cast hCardNat
  have hBoundaryReal : (boundaryCard : ℝ) ≤ 2 * (e : ℝ) := by
    exact_mod_cast hBoundaryNat
  have hpOneNat : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hpOneNat)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heNonnegative : (0 : ℝ) ≤ e := by positivity
  have hBoundaryAbsorb : (boundaryCard : ℝ) ≤ 2 * x := by
    have hscaleOne : (1 : ℝ) ≤ Real.sqrt (p : ℝ) * (d : ℝ) := by
      nlinarith
    have heScale : (e : ℝ) ≤
        (Real.sqrt (p : ℝ) * (d : ℝ)) * (e : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscaleOne heNonnegative
    calc
      (boundaryCard : ℝ) ≤ 2 * (e : ℝ) := hBoundaryReal
      _ ≤ 2 * (Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ)) := by gcongr
      _ = 2 * x := by rfl
  have hAffine' :
      |(affineCard : ℝ) - (p : ℝ)| ≤
        4 * (generalCoefficient : ℝ) * x := by
    dsimp only [affineCard]
    rw [ZMod.card] at hAffine
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hAffine
    convert hAffine using 1 <;> dsimp [x] <;> ring
  rw [hCardReal]
  calc
    |((affineCard : ℝ) + boundaryCard) - (p : ℝ)| =
        |((affineCard : ℝ) - (p : ℝ)) + boundaryCard| := by ring_nf
    _ ≤ |(affineCard : ℝ) - (p : ℝ)| + |(boundaryCard : ℝ)| := abs_add_le _ _
    _ = |(affineCard : ℝ) - (p : ℝ)| + boundaryCard := by
      have hbabs : |(boundaryCard : ℝ)| = boundaryCard :=
        abs_of_nonneg (Nat.cast_nonneg boundaryCard)
      rw [hbabs]
    _ ≤ 4 * (generalCoefficient : ℝ) * x + 2 * x := by gcongr
    _ = (coefficient : ℝ) * Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ) := by
      dsimp [coefficient, x]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- The general affine Hasse--Weil theorem supplies the seeded nonsplit estimate. -/
theorem exists_seededNonsplitTraceWeilBoundAssumption_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ, SeededNonsplitTraceWeilBoundAssumption coefficient := by
  obtain ⟨generalCoefficient, _hgeneralCoefficient, hgeneral⟩ := hHasse
  exact ⟨4 * generalCoefficient + 2,
    seededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
      generalCoefficient hgeneral⟩

end

end BGS.Markoff
