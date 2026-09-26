/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilBoundAssumption
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Boundary

/-!
# Applying the general affine Hasse--Weil theorem to split trace covers
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

private theorem degreeOf_first_monomial_le
    (c : K) (a b : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C c * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) ≤ a := by
  calc
    _ ≤ MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C c * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C c) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ a := by
      have ha : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ a := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = a := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

private theorem degreeOf_second_monomial_le
    (c : K) (a b : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C c * MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) ≤ b := by
  calc
    _ ≤ MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C c * MvPolynomial.X 0 ^ a) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ (MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C c) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0 ^ a)) +
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1 ^ b) := by
      gcongr
      exact MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ b := by
      have ha : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ a * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      have hb : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K) ≤ b := by
        calc
          _ ≤ b * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = b := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      omega

theorem splitTraceCoverPolynomial_degreeOf_first_le
    (alpha beta : K) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (splitTraceCoverPolynomial alpha beta d e) ≤ 2 * d := by
  unfold splitTraceCoverPolynomial
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · exact (degreeOf_first_monomial_le alpha d (2 * e)).trans
          (show d ≤ 2 * d by omega)
      · simpa using
          (degreeOf_first_monomial_le beta d 0).trans
            (show d ≤ 2 * d by omega)
    · simpa using
        (degreeOf_first_monomial_le (1 : K) (2 * d) e)
  · simpa using
      (degreeOf_first_monomial_le (1 : K) 0 e).trans
        (show 0 ≤ 2 * d by omega)

theorem splitTraceCoverPolynomial_degreeOf_second_le
    (alpha beta : K) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (splitTraceCoverPolynomial alpha beta d e) ≤ 2 * e := by
  unfold splitTraceCoverPolynomial
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · exact degreeOf_second_monomial_le alpha d (2 * e)
      · simpa using
          (degreeOf_second_monomial_le beta d 0).trans
            (show 0 ≤ 2 * e by omega)
    · simpa using
        (degreeOf_second_monomial_le (1 : K) (2 * d) e).trans
          (show e ≤ 2 * e by omega)
  · simpa using
      (degreeOf_second_monomial_le (1 : K) 0 e).trans
        (show e ≤ 2 * e by omega)

theorem splitTraceCoverPolynomial_hasBidegreeAtMost
    (alpha beta : K) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (splitTraceCoverPolynomial alpha beta d e) (2 * d) (2 * e) := by
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp
      (splitTraceCoverPolynomial_degreeOf_first_le alpha beta d e))
        monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp
      (splitTraceCoverPolynomial_degreeOf_second_le alpha beta d e))
        monomial hmonomial⟩

/-- A fixed-coefficient affine Hasse--Weil bound supplies the correspondingly
fixed split trace estimate. -/
theorem weightedSplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
    (generalCoefficient : ℕ)
    (hgeneral : BGS.External.BivariateAffineHasseWeilBound generalCoefficient) :
    WeightedSplitTraceWeilBoundAssumption (4 * generalCoefficient + 1) := by
  let coefficient := 4 * generalCoefficient + 1
  change WeightedSplitTraceWeilBoundAssumption coefficient
  refine ⟨by dsimp [coefficient]; omega, ?_⟩
  intro K _ _ _ alpha beta d e halpha hbeta hnondegenerate hd he hirreducible
  have hAffine := hgeneral K (splitTraceCoverPolynomial alpha beta d e)
    (2 * d) (2 * e) (by omega) (by omega)
    (splitTraceCoverPolynomial_hasBidegreeAtMost alpha beta d e) hirreducible
  have hcardNat :
      (BGS.External.affinePlaneCurveZeros K
        (splitTraceCoverPolynomial alpha beta d e)).card =
        (splitTraceCurveSolutions K alpha beta d e).card + 1 := by
    calc
      (BGS.External.affinePlaneCurveZeros K
          (splitTraceCoverPolynomial alpha beta d e)).card =
          (affineSplitTraceCoverZeros K alpha beta d e).card := by rfl
      _ = (torusSplitTraceCoverZeros K alpha beta d e).card + 1 :=
        affineSplitTraceCoverZeros_card_eq_torus_card_add_one
          K alpha beta d e hd he hbeta
      _ = (splitTraceCurveSolutions K alpha beta d e).card + 1 := by
        rw [torusSplitTraceCoverZeros_card_eq_splitTraceCurveSolutions_card]
  have hcardReal :
      ((BGS.External.affinePlaneCurveZeros K
        (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) =
        (splitTraceCurveSolutions K alpha beta d e).card + 1 := by
    exact_mod_cast hcardNat
  let x : ℝ := Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ)
  have hcardOne : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by
    have hcardPositive : 0 < Fintype.card K :=
      Fintype.card_pos_iff.mpr ⟨(0 : K)⟩
    exact_mod_cast hcardPositive
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Fintype.card K : ℝ) :=
    Real.one_le_sqrt.mpr hcardOne
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heOne : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hxOne : (1 : ℝ) ≤ x := by
    dsimp [x]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ Real.sqrt (Fintype.card K : ℝ) * d * e := by gcongr
  have hAffine' :
      |((BGS.External.affinePlaneCurveZeros K
          (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) -
          (Fintype.card K : ℝ)| ≤
        4 * (generalCoefficient : ℝ) * x := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hAffine
    convert hAffine using 1 <;> dsimp [x] <;> ring
  have herrorIdentity :
      ((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
          (Fintype.card K : ℝ) =
        (((BGS.External.affinePlaneCurveZeros K
          (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) -
            (Fintype.card K : ℝ)) - 1 := by
    rw [hcardReal]
    ring
  rw [herrorIdentity]
  calc
    |(((BGS.External.affinePlaneCurveZeros K
        (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) -
          (Fintype.card K : ℝ)) - 1| ≤
        |((BGS.External.affinePlaneCurveZeros K
          (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) -
            (Fintype.card K : ℝ)| + 1 := by
      simpa using abs_sub
        (((BGS.External.affinePlaneCurveZeros K
          (splitTraceCoverPolynomial alpha beta d e)).card : ℝ) -
            (Fintype.card K : ℝ)) (1 : ℝ)
    _ ≤ 4 * (generalCoefficient : ℝ) * x + 1 := by gcongr
    _ ≤ (4 * (generalCoefficient : ℝ) + 1) * x := by
      nlinarith [hxOne]
    _ = (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
          (d : ℝ) * (e : ℝ) := by
      dsimp [coefficient, x]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      ring

/-- The general affine Hasse--Weil theorem supplies the uniform split trace
estimate.  Absolute irreducibility remains an explicit premise of the target
interface and the unique affine boundary point is absorbed into the uniform
coefficient. -/
theorem exists_weightedSplitTraceWeilBoundAssumption_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ coefficient : ℕ, WeightedSplitTraceWeilBoundAssumption coefficient := by
  obtain ⟨generalCoefficient, _hgeneralCoefficient, hgeneral⟩ := hHasse
  exact ⟨4 * generalCoefficient + 1,
    weightedSplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound
      generalCoefficient hgeneral⟩

end

end BGS.Markoff
