/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageCurve

/-!
# The source-to-powered-image degree factor

The bidegrees of `poweredCoordinateImageRelation` are degrees on the powered
image curve, whereas the divisor argument computes coordinate heights on the
source curve.  The discrepancy is exactly the degree of the finite map from
the source curve to its powered image.  These tower identities expose that
factor explicitly.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The source degree over the powered first coordinate is the powered-image
relation's degree in the second coordinate times the source-to-image degree. -/
theorem poweredCoordinateImageRelation_natDegree_mul_imageIndex
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree *
        Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) =
      Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PlaneCurveFunctionField f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  rw [poweredCoordinateImageRelation_natDegree_eq_finrank
    hf hpartialSecond m hm n]
  exact Module.finrank_mul_finrank
    (FirstPoweredCoordinateSubfield f m)
    (PoweredImageOverFirst f m n)
    (PlaneCurveFunctionField f)

/-- The source degree over the powered second coordinate is the powered-image
relation's degree in the first coordinate times the same geometric
source-to-image degree, written in the second-coordinate presentation. -/
theorem poweredCoordinateImageRelation_transpose_natDegree_mul_imageIndex
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    (transposeBivariate
        (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree *
        Module.finrank (PoweredImageOverSecond f m n)
          (PlaneCurveFunctionField f) =
      Module.finrank (SecondPoweredCoordinateSubfield f n)
        (PlaneCurveFunctionField f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : FiniteDimensional (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_secondPoweredCoordinate hf hpartialFirst n hn
  rw [poweredCoordinateImageRelation_transpose_natDegree_eq_finrank
    hf hpartialFirst hpartialSecond m hm n hn]
  exact Module.finrank_mul_finrank
    (SecondPoweredCoordinateSubfield f n)
    (PoweredImageOverSecond f m n)
    (PlaneCurveFunctionField f)

end

end BGS.CorvajaZannier
