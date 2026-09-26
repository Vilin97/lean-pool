/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageHeightFactor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageIndex
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TranscendentalPowerDegree

/-!
# Exact source-height factorization through the powered image

These identities are the degree bookkeeping used in the two orientations of
Corvaja--Zannier Proposition 2.  The first factor is the relevant degree of
the powered-image relation and the second is the common source-to-image
index.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section


/-- In the orientation `(u,v)=(x^m,y^n)`, the degree of the image relation in
`u` times the common source-to-image index is the source height `n d₀`. -/
theorem poweredCoordinateImageRelation_transpose_natDegree_mul_commonIndex
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    (transposeBivariate
        (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree *
        Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) =
      n * MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let a := (transposeBivariate
    (poweredCoordinateImageRelation hf hpartialSecond m hm n)).natDegree
  calc
    a * Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) =
        a * Module.finrank (PoweredImageOverSecond f m n)
          (PlaneCurveFunctionField f) := by
      rw [finrank_poweredImageOverFirst_eq_poweredImageOverSecond]
    _ = Module.finrank (SecondPoweredCoordinateSubfield f n)
          (PlaneCurveFunctionField f) := by
      exact poweredCoordinateImageRelation_transpose_natDegree_mul_imageIndex
        hf hpartialFirst hpartialSecond m hm n hn
    _ = n * MvPolynomial.degreeOf 0 f :=
      finrank_over_secondPoweredCoordinate_eq hf hpartialFirst n hn

/-- In the swapped orientation `(u,v)=(y^n,x^m)`, the degree of the image
relation in `y^n` times the same index is the source height `m d₁`. -/
theorem poweredCoordinateImageRelation_natDegree_mul_commonIndex
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) :
    letI := planeCurveCoordinateRing_isDomain hf
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree *
        Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) =
      m * MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  calc
    (poweredCoordinateImageRelation hf hpartialSecond m hm n).natDegree *
        Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) =
      Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PlaneCurveFunctionField f) :=
      poweredCoordinateImageRelation_natDegree_mul_imageIndex
        hf hpartialSecond m hm n
    _ = m * MvPolynomial.degreeOf 1 f :=
      finrank_over_firstPoweredCoordinate_eq hf hpartialSecond m hm

end

end BGS.CorvajaZannier
