/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.AbsoluteIrreducibilityBaseChange
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSeparability
import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems

/-!
# From the public bidegree interface to function-field degrees

The finite-field Corvaja--Zannier endpoint states its degree hypothesis
support-wise, through `BGS.External.HasBidegreeAtMost`.  The function-field
development uses `MvPolynomial.degreeOf` and the degrees of the two coordinate
projections.  This file records the exact, assumption-free bridge between
those two presentations.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The first coordinate degree is bounded by the first component of a
support-wise bidegree bound. -/
theorem degreeOf_first_le_of_hasBidegreeAtMost
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    MvPolynomial.degreeOf 0 f ≤ firstDegree := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro monomial hmonomial
  exact (hdegree monomial hmonomial).1

/-- The second coordinate degree is bounded by the second component of a
support-wise bidegree bound. -/
theorem degreeOf_second_le_of_hasBidegreeAtMost
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    MvPolynomial.degreeOf 1 f ≤ secondDegree := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro monomial hmonomial
  exact (hdegree monomial hmonomial).2

/-- Absolute irreducibility in the public plane-curve interface implies
irreducibility over the original constant field. -/
theorem irreducible_of_irreducible_map_algebraicClosure
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible f := by
  have h := irreducible_map_of_irreducible_map_algebraicClosure
    (RingHom.id K) f habsolute
  rw [MvPolynomial.map_id] at h
  exact h

/-- The degree of the first-coordinate projection of the plane-curve
function field is bounded by the supplied second bidegree. -/
theorem finrank_over_firstCoordinate_le_of_hasBidegreeAtMost
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    letI := planeCurveCoordinateRing_isDomain
      (irreducible_of_irreducible_map_algebraicClosure habsolute)
    Module.finrank (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) ≤
      secondDegree := by
  let hf := irreducible_of_irreducible_map_algebraicClosure habsolute
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (finrank_over_firstCoordinate_eq_degreeOf_second_of_irreducible
    hf hpartialSecond).le.trans
      (degreeOf_second_le_of_hasBidegreeAtMost hdegree)

/-- The degree of the second-coordinate projection of the plane-curve
function field is bounded by the supplied first bidegree. -/
theorem finrank_over_secondCoordinate_le_of_hasBidegreeAtMost
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    letI := planeCurveCoordinateRing_isDomain
      (irreducible_of_irreducible_map_algebraicClosure habsolute)
    Module.finrank (SecondCoordinateSubfield f) (PlaneCurveFunctionField f) ≤
      firstDegree := by
  let hf := irreducible_of_irreducible_map_algebraicClosure habsolute
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  exact (finrank_over_secondCoordinate_eq_degreeOf_first_of_irreducible
    hf hpartialFirst).le.trans
      (degreeOf_first_le_of_hasBidegreeAtMost hdegree)

end

end BGS.CorvajaZannier
