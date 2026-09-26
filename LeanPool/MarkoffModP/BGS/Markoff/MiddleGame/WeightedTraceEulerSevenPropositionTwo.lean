/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEulerSeven
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTracePoweredImageIndexTwo
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePropositionTwoGeometric
public import Mathlib.Tactic

/-!
# Proposition Two with Euler budget seven for the weighted trace curve

The general bidegree endpoint uses the ambient budget `8`. For the weighted
trace curve, the common affine origin saves one boundary degree, while the
sparse support determinant bounds the powered-image index by `2`. This module
feeds both exact inputs into the natural and swapped Proposition Two proofs.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.CorvajaZannier

noncomputable section


theorem weightedTracePropositionTwo_natural_eulerSeven
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n)
    (hcardK : 2 < Fintype.card K) :
    let f := weightedTraceTorusClosurePolynomial alpha beta
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure
        hadmissible.2.2.2.1
    PropositionTwoNumericalAlternatives
      (n * MvPolynomial.degreeOf 0 f)
      (m * MvPolynomial.degreeOf 1 f) p 7
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf
        (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
          alpha beta hadmissible.2.1)
        m n : ℝ) := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure
      hadmissible.2.2.2.1
  let hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta hadmissible.2.1
  let hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta hadmissible.2.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  have hindexTwo :
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ 2 := by
    simpa only [f, hf] using
      weightedTraceTorusClosure_poweredImageIndex_le_two
        (p := p) alpha beta hadmissible m n hm hn hmPrime hnPrime
  have hindexSeven :
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ 7 :=
    hindexTwo.trans (by omega)
  apply planeCurvePropositionTwo_natural_of_auxiliaryBounds
    hf hpartialFirst hpartialSecond m n p 7 hm hn hindexSeven
  intro h k hh hk hparameters hexcluded
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let gK := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let g := poweredCoordinateFrobeniusImageRelation
    (p := p) hf hpartialSecond m hm n
  have hbidegree := poweredCoordinateImageRelation_bidegree_le
    hf hpartialFirst hpartialSecond m hm n hn
  have hdegreeG : g.natDegree ≤ n * MvPolynomial.degreeOf 0 f := by
    dsimp only [g]
    rw [poweredCoordinateFrobeniusImageRelation_natDegree]
    exact hbidegree.2
  have hdegreeTranspose : (transposeBivariate g).natDegree ≤
      m * MvPolynomial.degreeOf 1 f := by
    dsimp only [g]
    rw [transposeBivariate_poweredCoordinateFrobeniusImageRelation_natDegree]
    exact hbidegree.1
  have hsize : g.natDegree * h +
      (transposeBivariate g).natDegree * k < p := by
    apply lt_of_le_of_lt _ hparameters.2
    exact Nat.add_le_add
      (Nat.mul_le_mul_right h hdegreeG)
      (Nat.mul_le_mul_right k hdegreeTranspose)
  have hexcludedG : ¬ (g.natDegree ≤ k ∧
      (transposeBivariate g).natDegree ≤ h) := by
    dsimp only [g, gK] at hexcluded ⊢
    rw [poweredCoordinateFrobeniusImageRelation_natDegree,
      transposeBivariate_poweredCoordinateFrobeniusImageRelation_natDegree]
    exact hexcluded
  have hLI :=
    poweredCoordinateFrobeniusImage_auxiliaryFamily_linearIndependent
      (p := p) hadmissible.2.2.2.1 hf hpartialFirst hpartialSecond
        m n hm hnPrime h k hh hk hsize hexcludedG
  have hEuler :=
    weightedTraceTorusClosure_canonicalExceptionalDegree_le_seven
      alpha beta hadmissible.1 hadmissible.2.1 hadmissible.2.2.1
      hcardK m n hm hn
  exact finiteExtensionGcdBound_planeCurvePowers_of_auxiliaryFamily_linearIndependent
    (p := p) hf hpartialFirst hpartialSecond m n hm hn
      h k hparameters.1 7 hLI (by
        simpa only [f, hf, Nat.cast_ofNat] using hEuler)

private theorem exceptionalPlaces_comm
    (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
    (L : Type*) [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (u v : L) : propositionTwoExceptionalPlaces K L u v =
      propositionTwoExceptionalPlaces K L v u := by
  classical
  exact Finset.union_comm _ _

theorem weightedTracePropositionTwo_swapped_eulerSeven
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n)
    (hcardK : 2 < Fintype.card K) :
    let f := weightedTraceTorusClosurePolynomial alpha beta
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure
        hadmissible.2.2.2.1
    PropositionTwoNumericalAlternatives
      (m * MvPolynomial.degreeOf 1 f)
      (n * MvPolynomial.degreeOf 0 f) p 7
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf
        (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
          alpha beta hadmissible.2.1)
        m n : ℝ) := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure
      hadmissible.2.2.2.1
  let hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
      alpha beta hadmissible.2.1
  let hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0 :=
    weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
      alpha beta hadmissible.2.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  have hindexTwo :
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ 2 := by
    simpa only [f, hf] using
      weightedTraceTorusClosure_poweredImageIndex_le_two
        (p := p) alpha beta hadmissible m n hm hn hmPrime hnPrime
  have hindexSeven :
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤ 7 :=
    hindexTwo.trans (by omega)
  apply planeCurvePropositionTwo_swapped_of_auxiliaryBounds
    hf hpartialFirst hpartialSecond m n p 7 hm hn hindexSeven
  intro h k hh hk hparameters hexcluded
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  let gK := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let g : Polynomial (Polynomial F) := gK.map (Polynomial.mapRingHom ι)
  have hι : Function.Injective ι :=
    perfectConstantsToFrobeniusSubfield_injective
      (K := K) (L := L) (p := p)
  have hmap : Function.Injective (Polynomial.mapRingHom ι) :=
    Polynomial.map_injective ι hι
  have hdegreeG : g.natDegree = gK.natDegree := by
    dsimp only [g]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have hdegreeTranspose : (transposeBivariate g).natDegree =
      (transposeBivariate gK).natDegree := by
    dsimp only [g]
    rw [transposeBivariate_map]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have hbidegree := poweredCoordinateImageRelation_bidegree_le
    hf hpartialFirst hpartialSecond m hm n hn
  have hsize : g.natDegree * h +
      (transposeBivariate g).natDegree * k < p := by
    apply lt_of_le_of_lt _ hparameters.2
    rw [hdegreeG, hdegreeTranspose]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right h hbidegree.1)
      (Nat.mul_le_mul_right k hbidegree.2)
  have hexcludedG : ¬ (g.natDegree ≤ k ∧
      (transposeBivariate g).natDegree ≤ h) := by
    rw [hdegreeG, hdegreeTranspose]
    exact hexcluded
  have hLI :=
    poweredCoordinateFrobeniusImage_auxiliaryFamily_linearIndependent_swapped
      (p := p) hadmissible.2.2.2.1 hf hpartialFirst hpartialSecond
        m n hm hn hmPrime h k hh hk hsize hexcludedG
  have hEuler :=
    weightedTraceTorusClosure_canonicalExceptionalDegree_le_seven
      alpha beta hadmissible.1 hadmissible.2.1 hadmissible.2.2.1
      hcardK m n hm hn
  exact
    finiteExtensionGcdBound_planeCurvePowers_swapped_of_auxiliaryFamily_linearIndependent
      (p := p) hf hpartialFirst hpartialSecond m n hm hn
        h k hparameters.1 7 hLI (by
          erw [exceptionalPlaces_comm]
          exact hEuler)

/-- The natural and swapped orientations give the minimum/maximum form with
Euler budget exactly seven. -/
theorem weightedTracePropositionTwo_eulerSeven
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n)
    (hcardK : 2 < Fintype.card K) :
    let f := weightedTraceTorusClosurePolynomial alpha beta
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure
        hadmissible.2.2.2.1
    PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) m n)
      (planeCurveTorsionUpperDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) m n)
      p 7
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf
        (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
          alpha beta hadmissible.2.1)
        m n : ℝ) := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure
      hadmissible.2.2.2.1
  by_cases horient : n * MvPolynomial.degreeOf 0 f ≤
      m * MvPolynomial.degreeOf 1 f
  · have hnatural :=
      weightedTracePropositionTwo_natural_eulerSeven
        (p := p) alpha beta hadmissible m n hm hn
          hmPrime hnPrime hcardK
    simpa only [f, hf, planeCurveTorsionLowerDegree,
      planeCurveTorsionUpperDegree, min_eq_left horient,
      max_eq_right horient] using hnatural
  · have horient' : m * MvPolynomial.degreeOf 1 f ≤
        n * MvPolynomial.degreeOf 0 f :=
      Nat.le_of_lt (lt_of_not_ge horient)
    have hswapped :=
      weightedTracePropositionTwo_swapped_eulerSeven
        (p := p) alpha beta hadmissible m n hm hn
          hmPrime hnPrime hcardK
    simpa only [f, hf, planeCurveTorsionLowerDegree,
      planeCurveTorsionUpperDegree, min_eq_right horient',
      max_eq_left horient'] using hswapped

end

end BGS.Markoff
