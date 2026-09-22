/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePoweredImageDegreeBudget
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePoweredHeightBounds
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PropositionTwoDegreeMonotonicity
import Mathlib.Tactic

/-!
# Numerical assembly of plane-curve Proposition 2

This module isolates the final numerical use of the powered-image relation.
The geometric Wronskian estimate is supplied pointwise; the remaining degree,
index, and trivial-gcd bookkeeping is discharged here in both coordinate
orientations.
-/

namespace BGS.CorvajaZannier

noncomputable section


variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

private theorem propositionTwoAuxiliaryBound_of_zero_parameter
    (A B Chi h k : ℕ) (G : ℝ) (hG : G ≤ (A : ℝ))
    (hn : 0 < h * k + h + k) (hzero : h = 0 ∨ k = 0) :
    G ≤
      (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (A : ℝ) +
        ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (B : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (Chi : ℝ) := by
  rcases hzero with rfl | rfl
  · have hk : 0 < k := by simpa using hn
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have heuler : 0 ≤ (((k : ℝ) - 1) / 2) * (Chi : ℝ) := by
      have hkOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      positivity
    norm_num [hk0]
    have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
    have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
    linarith
  · have hh : 0 < h := by simpa using hn
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have heuler : 0 ≤ (((h : ℝ) - 1) / 2) * (Chi : ℝ) := by
      have hhOne : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      positivity
    norm_num [hh0]
    linarith

/-- Proposition 2 in the orientation `(u,v)=(x^m,y^n)`. -/
theorem planeCurvePropositionTwo_natural_of_auxiliaryBounds
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n p Chi : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hindex :
      letI := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ Chi)
    (hauxiliary : ∀ h k : ℕ, 0 < h → 0 < k →
      PropositionTwoParametersAreAdmissible
          (n * MvPolynomial.degreeOf 0 f)
          (m * MvPolynomial.degreeOf 1 f) p h k →
      ¬ ((transposeBivariate
            (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree ≤ k ∧
          (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree ≤ h) →
      letI := planeCurveCoordinateRing_isDomain hf
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      let hx := firstCoordinate_transcendental hf
        (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
      letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
      letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
        hf hpartialSecond
      letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
      (finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
          (1 - (planeCurveFunction f 0) ^ m)
          (1 - (planeCurveFunction f 1) ^ n) : ℝ) ≤
        (((h + 2 * k : ℕ) : ℝ) /
            ((h * k + h + k : ℕ) : ℝ)) *
              (n * MvPolynomial.degreeOf 0 f : ℕ) +
          ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) *
              (m * MvPolynomial.degreeOf 1 f : ℕ) +
            ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (Chi : ℝ)) :
    PropositionTwoNumericalAlternatives
      (n * MvPolynomial.degreeOf 0 f)
      (m * MvPolynomial.degreeOf 1 f) p Chi
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let a := (transposeBivariate
    (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree
  let b := (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree
  let d := Module.finrank (PoweredImageOverFirst f m n)
    (PlaneCurveFunctionField f)
  let A := n * MvPolynomial.degreeOf 0 f
  let B := m * MvPolynomial.degreeOf 1 f
  have ha : 0 < a := by
    dsimp only [a]
    exact poweredCoordinateImageRelation_transpose_natDegree_pos
      hf hpartialFirst hpartialSecond m hm n hn
  have hb : 0 < b := by
    dsimp only [b]
    exact poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n
  have hfactor : a * d = A := by
    simpa only [a, d, A] using
      poweredCoordinateImageRelation_transpose_natDegree_mul_commonIndex
        hf hpartialFirst hpartialSecond m n hm hn
  have hA : A ≤ d * a := by
    rw [Nat.mul_comm, hfactor]
  have hdChi : d ≤ Chi := by
    simpa only [d] using hindex
  have hGnat : planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n ≤ A := by
    rw [planeCurveExhaustiveTorsionGcdWeightedDegree_eq_one_sub
      hf hpartialFirst hpartialSecond m n hm hn]
    exact finiteExtensionGcdWeightedDegree_one_sub_planeCurvePowers_le
      hf hpartialFirst hpartialSecond m n hm hn
  have hG : (planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hGnat
  apply propositionTwoNumericalAlternatives_of_scaledAuxiliaryDegreeAlternative
    a b d A B p Chi
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ)
      ha hb hA hdChi hG
  intro h k hadmissible
  by_cases hdegree : a ≤ k ∧ b ≤ h
  · exact Or.inl hdegree
  · right
    by_cases hh : h = 0
    · exact propositionTwoAuxiliaryBound_of_zero_parameter
        A B Chi h k
        (planeCurveExhaustiveTorsionGcdWeightedDegree
          hf hpartialSecond m n : ℝ) hG hadmissible.1 (Or.inl hh)
    by_cases hk : k = 0
    · exact propositionTwoAuxiliaryBound_of_zero_parameter
        A B Chi h k
        (planeCurveExhaustiveTorsionGcdWeightedDegree
          hf hpartialSecond m n : ℝ) hG hadmissible.1 (Or.inr hk)
    simpa only [a, b, A, B,
      planeCurveExhaustiveTorsionGcdWeightedDegree_eq_one_sub
        hf hpartialFirst hpartialSecond m n hm hn] using
      hauxiliary h k (Nat.pos_of_ne_zero hh) (Nat.pos_of_ne_zero hk)
        (by simpa only [A, B] using hadmissible)
        (by simpa only [a, b] using hdegree)

/-- Proposition 2 in the swapped orientation `(u,v)=(y^n,x^m)`. -/
theorem planeCurvePropositionTwo_swapped_of_auxiliaryBounds
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n p Chi : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hindex :
      letI := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ Chi)
    (hauxiliary : ∀ h k : ℕ, 0 < h → 0 < k →
      PropositionTwoParametersAreAdmissible
          (m * MvPolynomial.degreeOf 1 f)
          (n * MvPolynomial.degreeOf 0 f) p h k →
      ¬ ((poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree ≤ k ∧
          (transposeBivariate
            (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree ≤ h) →
      letI := planeCurveCoordinateRing_isDomain hf
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      let hx := firstCoordinate_transcendental hf
        (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
      letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
      letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
        hf hpartialSecond
      letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
      (finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
          (1 - (planeCurveFunction f 1) ^ n)
          (1 - (planeCurveFunction f 0) ^ m) : ℝ) ≤
        (((h + 2 * k : ℕ) : ℝ) /
            ((h * k + h + k : ℕ) : ℝ)) *
              (m * MvPolynomial.degreeOf 1 f : ℕ) +
          ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) *
              (n * MvPolynomial.degreeOf 0 f : ℕ) +
            ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (Chi : ℝ)) :
    PropositionTwoNumericalAlternatives
      (m * MvPolynomial.degreeOf 1 f)
      (n * MvPolynomial.degreeOf 0 f) p Chi
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let a := (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree
  let b := (transposeBivariate
    (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree
  let d := Module.finrank (PoweredImageOverFirst f m n)
    (PlaneCurveFunctionField f)
  let A := m * MvPolynomial.degreeOf 1 f
  let B := n * MvPolynomial.degreeOf 0 f
  have ha : 0 < a := by
    dsimp only [a]
    exact poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n
  have hb : 0 < b := by
    dsimp only [b]
    exact poweredCoordinateImageRelation_transpose_natDegree_pos
      hf hpartialFirst hpartialSecond m hm n hn
  have hfactor : a * d = A := by
    simpa only [a, d, A] using
      poweredCoordinateImageRelation_natDegree_mul_commonIndex
        hf hpartialSecond m n hm
  have hA : A ≤ d * a := by
    rw [Nat.mul_comm, hfactor]
  have hdChi : d ≤ Chi := by
    simpa only [d] using hindex
  have hGnat : planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n ≤ A := by
    rw [planeCurveExhaustiveTorsionGcdWeightedDegree_eq_one_sub
      hf hpartialFirst hpartialSecond m n hm hn]
    rw [finiteExtensionGcdWeightedDegree_comm]
    exact finiteExtensionGcdWeightedDegree_one_sub_planeCurvePowers_swapped_le
      hf hpartialFirst hpartialSecond m n hm hn
  have hG : (planeCurveExhaustiveTorsionGcdWeightedDegree
      hf hpartialSecond m n : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hGnat
  apply propositionTwoNumericalAlternatives_of_scaledAuxiliaryDegreeAlternative
    a b d A B p Chi
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ)
      ha hb hA hdChi hG
  intro h k hadmissible
  by_cases hdegree : a ≤ k ∧ b ≤ h
  · exact Or.inl hdegree
  · right
    by_cases hh : h = 0
    · exact propositionTwoAuxiliaryBound_of_zero_parameter
        A B Chi h k
        (planeCurveExhaustiveTorsionGcdWeightedDegree
          hf hpartialSecond m n : ℝ) hG hadmissible.1 (Or.inl hh)
    by_cases hk : k = 0
    · exact propositionTwoAuxiliaryBound_of_zero_parameter
        A B Chi h k
        (planeCurveExhaustiveTorsionGcdWeightedDegree
          hf hpartialSecond m n : ℝ) hG hadmissible.1 (Or.inr hk)
    have hbound := hauxiliary h k (Nat.pos_of_ne_zero hh) (Nat.pos_of_ne_zero hk)
      (by simpa only [A, B] using hadmissible)
      (by simpa only [a, b] using hdegree)
    rw [planeCurveExhaustiveTorsionGcdWeightedDegree_eq_one_sub
      hf hpartialFirst hpartialSecond m n hm hn]
    rw [finiteExtensionGcdWeightedDegree_comm]
    simpa only [A, B] using hbound

end

end BGS.CorvajaZannier
