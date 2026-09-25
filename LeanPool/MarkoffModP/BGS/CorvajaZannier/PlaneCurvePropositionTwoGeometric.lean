/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePropositionTwoAssembly
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalGcdBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalEulerBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCharacteristicCardinality
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.EndpointComposition
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageFrobeniusRelation
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageFrobeniusRelationSwapped

/-!
# Geometric Proposition 2 for a plane curve

The powered-image linear-independence theorem and the canonical global
Wronskian estimate are assembled here.  The source-to-image index remains an
explicit premise of the two orientation lemmas; the following endpoint module
discharges it from the non-subtorus hypothesis.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section


private theorem exceptionalPlaces_comm
    (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
    (L : Type*) [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (u v : L) : propositionTwoExceptionalPlaces K L u v =
      propositionTwoExceptionalPlaces K L v u := by
  classical
  exact Finset.union_comm _ _

/-- The natural orientation `(u,v)=(x^m,y^n)` of the geometric Proposition 2
argument. -/
theorem planeCurvePropositionTwo_natural_of_poweredImageIndexBound
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hnPrime : ¬ p ∣ n)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (hindex :
      let := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f) :
    PropositionTwoNumericalAlternatives
      (n * MvPolynomial.degreeOf 0 f)
      (m * MvPolynomial.degreeOf 1 f) p
      (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f)
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let Chi := 2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f
  apply planeCurvePropositionTwo_natural_of_auxiliaryBounds
    hf hpartialFirst hpartialSecond m n p Chi hm hn hindex
  intro h k hh hk hadmissible hexcluded
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
  have hsize : g.natDegree * h + (transposeBivariate g).natDegree * k < p := by
    apply lt_of_le_of_lt _ hadmissible.2
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
      (p := p) habsolute hf hpartialFirst hpartialSecond
        m n hm hnPrime h k hh hk hsize hexcludedG
  have hEuler :=
    planeCurve_canonicalDifferent_add_propositionTwoExceptional_weightedDegree_le
      hf hpartialFirst hpartialSecond hcardK m n hm hn
  exact finiteExtensionGcdBound_planeCurvePowers_of_auxiliaryFamily_linearIndependent
    (p := p) hf hpartialFirst hpartialSecond m n hm hn
      h k hadmissible.1 Chi hLI hEuler

/-- The swapped orientation `(u,v)=(y^n,x^m)` of the geometric Proposition 2
argument. -/
theorem planeCurvePropositionTwo_swapped_of_poweredImageIndexBound
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (hindex :
      let := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f) :
    PropositionTwoNumericalAlternatives
      (m * MvPolynomial.degreeOf 1 f)
      (n * MvPolynomial.degreeOf 0 f) p
      (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f)
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let Chi := 2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f
  apply planeCurvePropositionTwo_swapped_of_auxiliaryBounds
    hf hpartialFirst hpartialSecond m n p Chi hm hn hindex
  intro h k hh hk hadmissible hexcluded
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
  have hsize : g.natDegree * h + (transposeBivariate g).natDegree * k < p := by
    apply lt_of_le_of_lt _ hadmissible.2
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
      (p := p) habsolute hf hpartialFirst hpartialSecond
        m n hm hn hmPrime h k hh hk hsize hexcludedG
  have hEulerNatural :=
    planeCurve_canonicalDifferent_add_propositionTwoExceptional_weightedDegree_le
      hf hpartialFirst hpartialSecond hcardK m n hm hn
  exact finiteExtensionGcdBound_planeCurvePowers_swapped_of_auxiliaryFamily_linearIndependent
    (p := p) hf hpartialFirst hpartialSecond m n hm hn
      h k hadmissible.1 Chi hLI (by
        erw [exceptionalPlaces_comm]
        exact hEulerNatural)

/-- The two orientations combine to the actual minimum/maximum degree form
needed by the plane-curve endpoint. -/
theorem planeCurvePropositionTwo_of_poweredImageIndexBound
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n)
    (hlarge : 12 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p)
    (hindex :
      let := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f) :
    PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) m n)
      (planeCurveTorsionUpperDegree
        (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) m n)
      p (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f)
      (planeCurveExhaustiveTorsionGcdWeightedDegree
        hf hpartialSecond m n : ℝ) := by
  have hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K :=
    planeCurve_degreeOf_second_lt_card_of_twelve_mul_degrees_lt_char
      hpartialFirst hpartialSecond hlarge
  by_cases horient : n * MvPolynomial.degreeOf 0 f ≤
      m * MvPolynomial.degreeOf 1 f
  · have hnatural := planeCurvePropositionTwo_natural_of_poweredImageIndexBound
      (p := p) hf habsolute hpartialFirst hpartialSecond
        m n hm hn hnPrime hcardK hindex
    simpa only [planeCurveTorsionLowerDegree, planeCurveTorsionUpperDegree,
      min_eq_left horient, max_eq_right horient] using hnatural
  · have horient' : m * MvPolynomial.degreeOf 1 f ≤
        n * MvPolynomial.degreeOf 0 f := Nat.le_of_lt (lt_of_not_ge horient)
    have hswapped := planeCurvePropositionTwo_swapped_of_poweredImageIndexBound
      (p := p) hf habsolute hpartialFirst hpartialSecond
        m n hm hn hmPrime hcardK hindex
    simpa only [planeCurveTorsionLowerDegree, planeCurveTorsionUpperDegree,
      min_eq_right horient', max_eq_left horient'] using hswapped

end

end BGS.CorvajaZannier
