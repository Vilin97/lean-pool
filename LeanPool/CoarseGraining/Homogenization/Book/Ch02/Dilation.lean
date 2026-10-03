/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Dilation.Basic

/-! # Dilation -/

@[expose] public section

open scoped Pointwise

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Public dilation package after the Chapter 2.5 definitions

This file freezes the note-facing dilation vocabulary used by later Chapter 3
arguments.  The statements are deliberately phrased with the public `CoeffOn`
and `TriadicCoeffFamily` interfaces: coefficient representatives are compared
only almost everywhere on the dilated cube.

The geometric convention is that dilation by `3^k` sends a triadic cube
`Q = 3^m (z + [-1/2,1/2]^d)` to the cube with the same integer index and scale
`m + k`.
-/

noncomputable section

/-- One-cube public dilation statements.  These are the Chapter 3-facing facts:
solutions dilate to solutions, scalar and doubled response values are
unchanged, and all canonical one-cube coarse matrices are unchanged. -/
structure CubeDilationTheory (d : ℕ) : Prop where
  solution_dilation_exists :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      ∀ hCoeff : CoeffOn.IsCubeDilation k a b,
        ∀ u : Solution (cubeDomain Q) a,
          Nonempty (Solution.CubeDilation hCoeff u)
  responseValue_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        ∀ p q : Vec d,
          responseValue (cubeDomain (dilateCube k Q)) b p q v =
            responseValue (cubeDomain Q) a p q u
  variationEnergyValue_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        variationEnergyValue (cubeDomain (dilateCube k Q)) b v =
          variationEnergyValue (cubeDomain Q) a u
  averageGradient_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        averageGradient (cubeDomain (dilateCube k Q)) b v =
          averageGradient (cubeDomain Q) a u
  averageFlux_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))}
      (hCoeff : CoeffOn.IsCubeDilation k a b)
      {u : Solution (cubeDomain Q) a}
      {v : Solution (cubeDomain (dilateCube k Q)) b},
      Solution.IsCubeDilation hCoeff u v →
        averageFlux (cubeDomain (dilateCube k Q)) b v =
          averageFlux (cubeDomain Q) a u
  responseJ_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ p q : Vec d,
          responseJ (cubeDomain (dilateCube k Q)) b p q =
            responseJ (cubeDomain Q) a p q
  doubledMu_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ P : BlockVec d,
          doubledMu (cubeDomain (dilateCube k Q)) b P =
            doubledMu (cubeDomain Q) a P
  doubledResponseJ_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        ∀ P R : BlockVec d,
          doubledResponseJ (cubeDomain (dilateCube k Q)) b P R =
            doubledResponseJ (cubeDomain Q) a P R
  sigmaCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaCoarse (cubeDomain Q) a
  sigmaStarInvCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaStarInvCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaStarInvCoarse (cubeDomain Q) a
  sigmaStarCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        sigmaStarCoarse (cubeDomain (dilateCube k Q)) b =
          sigmaStarCoarse (cubeDomain Q) a
  kappaCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        kappaCoarse (cubeDomain (dilateCube k Q)) b =
          kappaCoarse (cubeDomain Q) a
  coarseMatrices_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        coarseMatrices (cubeDomain (dilateCube k Q)) b =
          coarseMatrices (cubeDomain Q) a
  bCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        bCoarse (cubeDomain (dilateCube k Q)) b =
          bCoarse (cubeDomain Q) a
  aCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        aCoarse (cubeDomain (dilateCube k Q)) b =
          aCoarse (cubeDomain Q) a
  aStarCoarse_dilate :
    ∀ {k : ℤ} {Q : TriadicCube d}
      {a : CoeffOn (cubeDomain Q)}
      {b : CoeffOn (cubeDomain (dilateCube k Q))},
      CoeffOn.IsCubeDilation k a b →
        aStarCoarse (cubeDomain (dilateCube k Q)) b =
          aStarCoarse (cubeDomain Q) a

/-- Chapter 2.5 multiscale dilation statements.  A dilation shifts every scale
index by `k`; the normalized multiscale quantities themselves do not change. -/
structure MultiscaleDilationTheory (d : ℕ) [NeZero d] : Prop where
  coarseBMatrixNorm_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ Q : TriadicCube d,
          coarseBMatrixNorm (dilateCube k Q) b =
            coarseBMatrixNorm Q a
  coarseSigmaStarInvMatrixNorm_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ Q : TriadicCube d,
          coarseSigmaStarInvMatrixNorm (dilateCube k Q) b =
            coarseSigmaStarInvMatrixNorm Q a
  maxDescendantBMatrixNormAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ),
          maxDescendantBMatrixNormAtScale (dilateCube k Q) (n + k) b =
            maxDescendantBMatrixNormAtScale Q n a
  maxDescendantSigmaStarInvMatrixNormAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ),
          maxDescendantSigmaStarInvMatrixNormAtScale (dilateCube k Q) (n + k) b =
            maxDescendantSigmaStarInvMatrixNormAtScale Q n a
  LambdaSq_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
          LambdaSq (dilateCube k Q) s q b =
            LambdaSq Q s q a
  lambdaSq_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
          lambdaSq (dilateCube k Q) s q b =
            lambdaSq Q s q a
  LambdaS_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ),
          LambdaS (dilateCube k Q) s b = LambdaS Q s a
  lambdaS_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ),
          lambdaS (dilateCube k Q) s b = lambdaS Q s a
  ThetaRatio_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s t : ℝ),
          ThetaRatio (dilateCube k Q) s t b = ThetaRatio Q s t a
  maxDescendantUpperEllipticityAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ) (q : MultiscaleExponent),
          maxDescendantUpperEllipticityAtScale (dilateCube k Q) (n + k) s q b =
            maxDescendantUpperEllipticityAtScale Q n s q a
  maxDescendantLowerEllipticityInvAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ) (q : MultiscaleExponent),
          maxDescendantLowerEllipticityInvAtScale (dilateCube k Q) (n + k) s q b =
            maxDescendantLowerEllipticityInvAtScale Q n s q a
  normalizedBlockResponseMax_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (a0 : Mat d),
          normalizedBlockResponseMax (dilateCube k Q) b a0 =
            normalizedBlockResponseMax Q a a0
  maxDescendantNormalizedBlockResponseAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (a0 : Mat d),
          maxDescendantNormalizedBlockResponseAtScale (dilateCube k Q) (n + k) b a0 =
            maxDescendantNormalizedBlockResponseAtScale Q n a a0
  scaleResponseAtScale_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (p : MultiscaleExponent) (a0 : Mat d),
          scaleResponseAtScale (dilateCube k Q) (n + k) p b a0 =
            scaleResponseAtScale Q n p a a0
  HomogenizationError_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (n : ℤ) (s : ℝ)
          (p q : MultiscaleExponent) (a0 : Mat d),
          HomogenizationError (dilateCube k Q) (n + k) s p q b a0 =
            HomogenizationError Q n s p q a a0
  HomogenizationErrorOnCube_dilate :
    ∀ {k : ℤ} {a b : TriadicCoeffFamily d},
      TriadicCoeffFamily.IsDilation k a b →
        ∀ (Q : TriadicCube d) (s : ℝ)
          (p q : MultiscaleExponent) (a0 : Mat d),
          HomogenizationErrorOnCube (dilateCube k Q) s p q b a0 =
            HomogenizationErrorOnCube Q s p q a a0

/-- Aggregate public dilation theorem package for Chapter 2 / 2.5, intended to
be imported by Chapter 3 scale-normalization arguments. -/
structure DilationTheory (d : ℕ) [NeZero d] : Prop where
  cube : CubeDilationTheory d
  multiscale : MultiscaleDilationTheory d

end

end Ch02
end Book
end Homogenization
