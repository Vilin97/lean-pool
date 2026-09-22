/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageCurve
import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionGcdDivisorBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionBidegreeCount
import LeanPool.MarkoffModP.BGS.CorvajaZannier.NumericalCorollary
import LeanPool.MarkoffModP.BGS.CorvajaZannier.ElementaryFiniteFieldBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBidegreeBridge

/-!
# Composition of the Corvaja--Zannier plane-curve endpoint

This module discharges the algebraic and numerical bookkeeping between the
public plane-curve interface and the remaining global geometric estimate.  It
constructs the powered-image relation from `IsCorvajaZannierPlaneCurve`, proves
that the two powered torsion functions are nonzero, identifies the finite-set
cardinality with the torsion-point subtype cardinality, and composes the
Dedekind gcd divisor estimate with the proved numerical optimization.

The only remaining input is exposed as the ordinary proposition
`GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange`.  Its
certificate is precisely a gcd-divisor number which bounds the rational
torsion points, satisfies the trivial degree bound, and satisfies the
Corvaja--Zannier Proposition 2 alternatives.  No axiom or typeclass hides this
geometric obligation.
-/

namespace BGS.CorvajaZannier

noncomputable section

open Polynomial

theorem pow_sub_one_ne_zero_of_transcendental
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {z : L} (hz : Transcendental K z) (n : ℕ) (hn : 0 < n) :
    z ^ n - 1 ≠ 0 := by
  intro hzero
  have hroot : Polynomial.aeval z (Polynomial.X ^ n - 1 : Polynomial K) = 0 := by
    simpa using hzero
  have hpolyZero := (transcendental_iff.mp hz)
    (Polynomial.X ^ n - 1 : Polynomial K) hroot
  have hmonic : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub_C 1 hn.ne'
  exact hmonic.ne_zero (by simpa using hpolyZero)

theorem torusCurveTorsionIntersection_card_eq_torsionPoint_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    (BGS.External.torusCurveTorsionIntersection
        K f firstOrder secondOrder).card =
      Fintype.card (TorusCurveTorsionPoint f firstOrder secondOrder) := by
  exact (Fintype.card_coe
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder)).symm

theorem poweredTorsionFunctions_ne_zero_of_isCorvajaZannierPlaneCurve
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (firstOrder secondOrder : ℕ)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure hcurve.1
    letI := planeCurveCoordinateRing_isDomain hf
    planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0 ∧
      planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0 := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure hcurve.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have hxTrans : Transcendental K (planeCurveFunction f 0) :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hcurve.2.2.2)
  have hyTrans : Transcendental K (planeCurveFunction f 1) :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hcurve.2.2.1)
  exact ⟨pow_sub_one_ne_zero_of_transcendental
      hxTrans firstOrder hfirstOrder,
    pow_sub_one_ne_zero_of_transcendental
      hyTrans secondOrder hsecondOrder⟩

/-- The public curve hypotheses instantiate the canonical powered-image
relation, including the advertised source bidegree bounds. -/
theorem poweredCoordinateImageRelation_spec_of_isCorvajaZannierPlaneCurve
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure hcurve.1
    letI := planeCurveCoordinateRing_isDomain hf
    let g := poweredCoordinateImageRelation hf hcurve.2.2.2
      firstOrder hfirstOrder secondOrder
    Irreducible g ∧
      evalBivariate (planeCurveFunction f 0 ^ firstOrder)
        (planeCurveFunction f 1 ^ secondOrder) g = 0 ∧
      0 < g.natDegree ∧
      0 < (transposeBivariate g).natDegree ∧
      g.natDegree ≤ firstOrder * secondDegree ∧
      (transposeBivariate g).natDegree ≤ secondOrder * firstDegree ∧
      ∀ i, (g.coeff i).natDegree ≤ secondOrder * firstDegree := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure hcurve.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let g := poweredCoordinateImageRelation hf hcurve.2.2.2
    firstOrder hfirstOrder secondOrder
  have hspec := poweredCoordinateImageRelation_spec
    hf hcurve.2.2.1 hcurve.2.2.2
      firstOrder hfirstOrder secondOrder hsecondOrder
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
    hspec.2.2.2.2.1.trans ?_, hspec.2.2.2.2.2.1.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_left firstOrder
      (degreeOf_second_le_of_hasBidegreeAtMost hbidegree)
  · exact Nat.mul_le_mul_left secondOrder
      (degreeOf_first_le_of_hasBidegreeAtMost hbidegree)
  · intro i
    exact (hspec.2.2.2.2.2.2 i).trans
      (Nat.mul_le_mul_left secondOrder
        (degreeOf_first_le_of_hasBidegreeAtMost hbidegree))

/-- The smaller of the degrees of `x ^ firstOrder` and `y ^ secondOrder`,
using only the public bidegree bounds. -/
def planeCurveTorsionLowerDegree
    (firstDegree secondDegree firstOrder secondOrder : ℕ) : ℕ :=
  min (secondOrder * firstDegree) (firstOrder * secondDegree)

/-- The larger of the degrees of `x ^ firstOrder` and `y ^ secondOrder`,
using only the public bidegree bounds. -/
def planeCurveTorsionUpperDegree
    (firstDegree secondDegree firstOrder secondOrder : ℕ) : ℕ :=
  max (secondOrder * firstDegree) (firstOrder * secondDegree)

theorem planeCurveTorsionLowerDegree_mul_upperDegree
    (firstDegree secondDegree firstOrder secondOrder : ℕ) :
    planeCurveTorsionLowerDegree firstDegree secondDegree firstOrder secondOrder *
        planeCurveTorsionUpperDegree firstDegree secondDegree firstOrder secondOrder =
      firstOrder * secondOrder * firstDegree * secondDegree := by
  rw [planeCurveTorsionLowerDegree, planeCurveTorsionUpperDegree, min_mul_max]
  ac_rfl

/-- Proposition 2 plus the trivial gcd bound gives exactly the numerical
right-hand side of the public plane-curve theorem, independently of which
powered coordinate has the smaller degree. -/
theorem planeCurveCorvajaZannierNumericalBound_of_propositionTwo
    (p firstDegree secondDegree firstOrder secondOrder : ℕ) (G : ℝ)
    (hfirstDegree : 0 < firstDegree)
    (hsecondDegree : 0 < secondDegree)
    (hfirstOrder : 0 < firstOrder)
    (hsecondOrder : 0 < secondOrder)
    (hp : 0 < p)
    (hGNonneg : 0 ≤ G)
    (hGTrivial : G ≤ planeCurveTorsionLowerDegree
      firstDegree secondDegree firstOrder secondOrder)
    (hPropositionTwo : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree) G) :
    G ≤ BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
      p firstOrder secondOrder firstDegree secondDegree
        (BGS.External.planeTorusEulerCharacteristicBound
          firstDegree secondDegree) := by
  let a := planeCurveTorsionLowerDegree
    firstDegree secondDegree firstOrder secondOrder
  let b := planeCurveTorsionUpperDegree
    firstDegree secondDegree firstOrder secondOrder
  let chi : ℕ := 2 * firstDegree * secondDegree
  have ha : 0 < a := by
    simp only [a, planeCurveTorsionLowerDegree]
    exact lt_min (Nat.mul_pos hsecondOrder hfirstDegree)
      (Nat.mul_pos hfirstOrder hsecondDegree)
  have hab : a ≤ b := by
    simp only [a, b, planeCurveTorsionLowerDegree,
      planeCurveTorsionUpperDegree]
    exact min_le_max
  have hchi : 0 < chi := by
    simp only [chi]
    positivity
  have hbound := theoremTwo_maxBound_of_propositionTwo
    a b chi p G ha hab hchi hp hGNonneg hGTrivial hPropositionTwo
  have habProductNat :
      a * b = firstOrder * secondOrder * firstDegree * secondDegree := by
    exact planeCurveTorsionLowerDegree_mul_upperDegree
      firstDegree secondDegree firstOrder secondOrder
  have habProductReal :
      (a : ℝ) * (b : ℝ) =
        ((firstOrder * secondOrder * firstDegree * secondDegree : ℕ) : ℝ) := by
    exact_mod_cast habProductNat
  rw [habProductReal] at hbound
  unfold BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
  simp only [chi, Nat.cast_mul] at hbound
  simpa only [BGS.External.planeTorusEulerCharacteristicBound,
    Nat.cast_ofNat, Nat.cast_mul, mul_assoc] using hbound

/-- A certificate for the only remaining geometric input at the endpoint.
The real number `G` is intended to be the degree of the gcd divisor of the
two powered torsion functions.  Its fields state, respectively, that every
rational torsion point contributes to it, that the elementary divisor bound
holds, and that the Corvaja--Zannier Proposition 2 alternatives hold. -/
def PlaneCurvePropositionTwoCertificate
    (p : ℕ) (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ) : Prop :=
  ∃ G : ℝ,
    ((BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card : ℝ) ≤ G ∧
    G ≤ planeCurveTorsionLowerDegree
      firstDegree secondDegree firstOrder secondOrder ∧
    PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree) G

/-- Proposition 2's alternatives are downward closed in the gcd quantity. -/
theorem propositionTwoNumericalAlternatives_mono
    {a b p chi : ℕ} {G H : ℝ} (hGH : G ≤ H)
    (hH : PropositionTwoNumericalAlternatives a b p chi H) :
    PropositionTwoNumericalAlternatives a b p chi G := by
  intro h k hadmissible
  rcases hH h k hadmissible with hdegree | hbound
  · exact Or.inl hdegree
  · exact Or.inr (hGH.trans hbound)

theorem torusCurveTorsionIntersection_le_corvajaZannierBound_of_certificate
    (p : ℕ) (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hfirstDegree : 0 < firstDegree)
    (hsecondDegree : 0 < secondDegree)
    (hfirstOrder : 0 < firstOrder)
    (hsecondOrder : 0 < secondOrder)
    (hp : 0 < p)
    (hcertificate : PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder) :
    ((BGS.External.torusCurveTorsionIntersection
        K f firstOrder secondOrder).card : ℝ) ≤
      BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
        p firstOrder secondOrder firstDegree secondDegree
          (BGS.External.planeTorusEulerCharacteristicBound
            firstDegree secondDegree) := by
  obtain ⟨G, hcard, htrivial, hpropositionTwo⟩ := hcertificate
  have hGNonneg : 0 ≤ G :=
    (Nat.cast_nonneg
      (BGS.External.torusCurveTorsionIntersection
        K f firstOrder secondOrder).card).trans hcard
  exact hcard.trans
    (planeCurveCorvajaZannierNumericalBound_of_propositionTwo
      p firstDegree secondDegree firstOrder secondOrder G
      hfirstDegree hsecondDegree hfirstOrder hsecondOrder hp
      hGNonneg htrivial hpropositionTwo)

/-- The explicit Dedekind gcd sum supplies a Proposition 2 certificate once
the two still-geometric inequalities for that sum have been proved. -/
theorem planeCurvePropositionTwoCertificate_of_dedekindGcdSum
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (p firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (htrivial :
      ((∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
          firstOrder secondOrder,
          torsionGcdMultiplicity (f := f) (B := B)
            firstOrder secondOrder v : ℕ) : ℝ) ≤
        planeCurveTorsionLowerDegree
          firstDegree secondDegree firstOrder secondOrder)
    (hpropositionTwo : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree)
      ((∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
          firstOrder secondOrder,
          torsionGcdMultiplicity (f := f) (B := B)
            firstOrder secondOrder v : ℕ) : ℝ)) :
    PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder := by
  let GNat : ℕ :=
    ∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
      firstOrder secondOrder,
      torsionGcdMultiplicity (f := f) (B := B)
        firstOrder secondOrder v
  refine ⟨(GNat : ℝ), ?_, htrivial, hpropositionTwo⟩
  have hcardNat := torsionPoint_card_le_torsionGcdMultiplicity_sum
    (f := f) (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero
  have hfinsetNat :
      (BGS.External.torusCurveTorsionIntersection
        K f firstOrder secondOrder).card ≤ GNat := by
    rw [torusCurveTorsionIntersection_card_eq_torsionPoint_card]
    exact hcardNat
  exact_mod_cast hfinsetNat

/-- The sharp fiber-counting bound supplies the trivial certificate bound
directly.  Consequently an upper gcd divisor only has to satisfy Proposition
2; it need not separately be proved below the smaller coordinate height. -/
theorem planeCurvePropositionTwoCertificate_of_dedekindGcdSum_and_bidegree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (p firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hbidegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hfirstOrder : 0 < firstOrder) (hsecondOrder : 0 < secondOrder)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (hpropositionTwo : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree)
      ((∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
          firstOrder secondOrder,
          torsionGcdMultiplicity (f := f) (B := B)
            firstOrder secondOrder v : ℕ) : ℝ)) :
    PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder := by
  let card : ℕ :=
    (BGS.External.torusCurveTorsionIntersection
      K f firstOrder secondOrder).card
  let gcdDegree : ℕ :=
    ∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
      firstOrder secondOrder,
      torsionGcdMultiplicity (f := f) (B := B)
        firstOrder secondOrder v
  have hcardTrivial : card ≤ planeCurveTorsionLowerDegree
      firstDegree secondDegree firstOrder secondOrder := by
    dsimp only [card, planeCurveTorsionLowerDegree]
    simpa only [min_comm] using
      torusCurveTorsionIntersection_card_le_min_bidegree_order
        f firstDegree secondDegree firstOrder secondOrder
        hbidegree hcurve hfirstOrder hsecondOrder
  have hcardGcd : card ≤ gcdDegree := by
    dsimp only [card, gcdDegree]
    rw [torusCurveTorsionIntersection_card_eq_torsionPoint_card]
    exact torsionPoint_card_le_torsionGcdMultiplicity_sum
      (f := f) (B := B) firstOrder secondOrder
        hfirstNonzero hsecondNonzero
  refine ⟨(card : ℝ), le_rfl, ?_, ?_⟩
  · exact_mod_cast hcardTrivial
  · apply propositionTwoNumericalAlternatives_mono
      (G := (card : ℝ)) (H := (gcdDegree : ℝ))
    · exact_mod_cast hcardGcd
    · simpa only [gcdDegree] using hpropositionTwo

/-- A concrete Dedekind gcd sum satisfying the divisor and Proposition 2
inequalities gives the public numerical endpoint directly. -/
theorem torusCurveTorsionIntersection_le_corvajaZannierBound_of_dedekindGcdSum
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)]
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (p firstDegree secondDegree firstOrder secondOrder : ℕ)
    (hfirstDegree : 0 < firstDegree)
    (hsecondDegree : 0 < secondDegree)
    (hfirstOrder : 0 < firstOrder)
    (hsecondOrder : 0 < secondOrder)
    (hp : 0 < p)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (htrivial :
      ((∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
          firstOrder secondOrder,
          torsionGcdMultiplicity (f := f) (B := B)
            firstOrder secondOrder v : ℕ) : ℝ) ≤
        planeCurveTorsionLowerDegree
          firstDegree secondDegree firstOrder secondOrder)
    (hpropositionTwo : PropositionTwoNumericalAlternatives
      (planeCurveTorsionLowerDegree
        firstDegree secondDegree firstOrder secondOrder)
      (planeCurveTorsionUpperDegree
        firstDegree secondDegree firstOrder secondOrder)
      p (2 * firstDegree * secondDegree)
      ((∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
          firstOrder secondOrder,
          torsionGcdMultiplicity (f := f) (B := B)
            firstOrder secondOrder v : ℕ) : ℝ)) :
    ((BGS.External.torusCurveTorsionIntersection
        K f firstOrder secondOrder).card : ℝ) ≤
      BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
        p firstOrder secondOrder firstDegree secondDegree
          (BGS.External.planeTorusEulerCharacteristicBound
            firstDegree secondDegree) := by
  apply torusCurveTorsionIntersection_le_corvajaZannierBound_of_certificate
    p K f firstDegree secondDegree firstOrder secondOrder
    hfirstDegree hsecondDegree hfirstOrder hsecondOrder hp
  exact planeCurvePropositionTwoCertificate_of_dedekindGcdSum
    p firstDegree secondDegree firstOrder secondOrder
    hfirstNonzero hsecondNonzero htrivial hpropositionTwo

/-- The remaining above-elementary-range assertion, now reduced to explicit
Proposition 2 certificates.  It contains no axiom or typeclass assumption. -/
def GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ),
    0 < firstDegree →
    0 < secondDegree →
    BGS.External.HasBidegreeAtMost f firstDegree secondDegree →
    BGS.External.IsCorvajaZannierPlaneCurve f →
    0 < firstOrder →
    0 < secondOrder →
    ¬ p ∣ firstOrder →
    ¬ p ∣ secondOrder →
    12 * firstDegree * secondDegree < p →
    PlaneCurvePropositionTwoCertificate
      p K f firstDegree secondDegree firstOrder secondOrder

theorem generalCorvajaZannierPlaneCurveTheoremAboveElementaryRange_of_certificates
    (hcertificates :
      GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange) :
    BGS.External.GeneralCorvajaZannierPlaneCurveTheoremAboveElementaryRange := by
  unfold GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange at hcertificates
  unfold BGS.External.GeneralCorvajaZannierPlaneCurveTheoremAboveElementaryRange
  intro p _ K _ _ _ _ f firstDegree secondDegree firstOrder secondOrder
    hfirstDegree hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
    hfirstPrimeToChar hsecondPrimeToChar hlarge
  exact torusCurveTorsionIntersection_le_corvajaZannierBound_of_certificate
    p K f firstDegree secondDegree firstOrder secondOrder
    hfirstDegree hsecondDegree hfirstOrder hsecondOrder
    (Fact.out : p.Prime).pos
    (hcertificates p (K := K) f
      firstDegree secondDegree firstOrder secondOrder
      hfirstDegree hsecondDegree hbidegree hcurve
      hfirstOrder hsecondOrder hfirstPrimeToChar hsecondPrimeToChar hlarge)

/-- The exact endpoint follows from the remaining certificate proposition;
the complementary characteristic range is the proved elementary theorem. -/
theorem generalCorvajaZannierPlaneCurveTheorem_of_certificates
    (hcertificates :
      GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange) :
    BGS.External.GeneralCorvajaZannierPlaneCurveTheorem := by
  rw [BGS.External.generalCorvajaZannierPlaneCurveTheorem_iff_aboveElementaryRange]
  exact generalCorvajaZannierPlaneCurveTheoremAboveElementaryRange_of_certificates
    hcertificates

end

end BGS.CorvajaZannier
