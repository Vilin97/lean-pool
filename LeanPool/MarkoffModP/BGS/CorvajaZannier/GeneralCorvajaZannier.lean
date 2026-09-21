/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePropositionTwoGeometric
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePropositionTwoDegreeBridge
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageIndexBound

/-!
# The general Corvaja--Zannier plane-curve theorem

This file is the final public assembly.  Its first theorem isolates the sole
powered-image index input, so that the geometric index theorem can be audited
independently; the unconditional endpoint below instantiates that input.
-/

namespace BGS.CorvajaZannier

noncomputable section


/-- A uniform source-to-powered-image index bound supplies all Proposition 2
certificates above the elementary range. -/
theorem generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange_of_poweredImageIndexBound
    (hindex : ∀ (p : ℕ) [Fact p.Prime]
      (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
      (f : MvPolynomial (Fin 2) K) (m n : ℕ)
      (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
      (_hm : 0 < m) (_hn : 0 < n) (_hmPrime : ¬ p ∣ m) (_hnPrime : ¬ p ∣ n),
      let hf : Irreducible f :=
        irreducible_of_irreducible_map_algebraicClosure
          hcurve.1
      letI := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f) :
    GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange := by
  apply generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange_of_actualDegree
  intro p _ K _ _ _ _ f firstDegree secondDegree firstOrder secondOrder
    _hfirstDegree _hsecondDegree hbidegree hcurve hfirstOrder hsecondOrder
    hfirstPrimeToChar hsecondPrimeToChar hlarge
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure hcurve.1
  have hfirstActual : MvPolynomial.degreeOf 0 f ≤ firstDegree :=
    degreeOf_first_le_of_hasBidegreeAtMost hbidegree
  have hsecondActual : MvPolynomial.degreeOf 1 f ≤ secondDegree :=
    degreeOf_second_le_of_hasBidegreeAtMost hbidegree
  have hactualDegreeProduct :
      12 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f ≤
        12 * firstDegree * secondDegree :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 12 hfirstActual) hsecondActual
  have hlargeActual :
      12 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f < p :=
    hactualDegreeProduct.trans_lt hlarge
  have hpoweredIndex :
      letI := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f firstOrder secondOrder)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
    simpa only [hf] using hindex p K f firstOrder secondOrder
      hcurve hfirstOrder hsecondOrder hfirstPrimeToChar hsecondPrimeToChar
  simpa only [hf] using
    planeCurvePropositionTwo_of_poweredImageIndexBound
      (p := p) hf hcurve.1 hcurve.2.2.1 hcurve.2.2.2
        firstOrder secondOrder hfirstOrder hsecondOrder
        hfirstPrimeToChar hsecondPrimeToChar hlargeActual hpoweredIndex

/-- The public finite-field Corvaja--Zannier theorem follows from the exact
powered-image index statement. -/
theorem generalCorvajaZannierPlaneCurveTheorem_of_poweredImageIndexBound
    (hindex : ∀ (p : ℕ) [Fact p.Prime]
      (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
      (f : MvPolynomial (Fin 2) K) (m n : ℕ)
      (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
      (_hm : 0 < m) (_hn : 0 < n) (_hmPrime : ¬ p ∣ m) (_hnPrime : ¬ p ∣ n),
      let hf : Irreducible f :=
        irreducible_of_irreducible_map_algebraicClosure
          hcurve.1
      letI := planeCurveCoordinateRing_isDomain hf
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
        2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f) :
    BGS.External.GeneralCorvajaZannierPlaneCurveTheorem :=
  generalCorvajaZannierPlaneCurveTheorem_of_certificates
    (generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange_of_poweredImageIndexBound
      hindex)

/-- The geometric powered-image index input required by the final assembly is
provided by the exact Galois stabilizer count. -/
theorem poweredImageIndexBound_of_isCorvajaZannierPlaneCurve
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (m n : ℕ)
    (hcurve : BGS.External.IsCorvajaZannierPlaneCurve f)
    (hm : 0 < m) (hn : 0 < n) (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure hcurve.1
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  exact finrank_poweredImageOverFirst_le_twice_bidegree
    hcurve.1 hcurve.2.1 hcurve.2.2.1 hcurve.2.2.2
      m n hm hn hmPrime hnPrime

/-- The unconditional certificates for the high-characteristic range. -/
theorem generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange :
    GeneralPlaneCurvePropositionTwoCertificatesAboveElementaryRange :=
  generalPlaneCurvePropositionTwoCertificatesAboveElementaryRange_of_poweredImageIndexBound
    poweredImageIndexBound_of_isCorvajaZannierPlaneCurve

/-- **The general Corvaja--Zannier finite-field plane-curve theorem.** -/
theorem generalCorvajaZannierPlaneCurveTheorem :
    BGS.External.GeneralCorvajaZannierPlaneCurveTheorem :=
  generalCorvajaZannierPlaneCurveTheorem_of_poweredImageIndexBound
    poweredImageIndexBound_of_isCorvajaZannierPlaneCurve

end

end BGS.CorvajaZannier
