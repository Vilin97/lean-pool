/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.DoubledResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.MultiscaleEllipticity
import Mathlib.Analysis.Matrix.Order

/-! # Homogenization Error -/

open scoped BigOperators MatrixOrder

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Public multiscale homogenization error

This file records the Chapter 2 note-facing quantity
`\mathcal E_{s,p,q}` using the public `TriadicCoeffFamily` interface.  In
particular the heterogeneous coefficient is a.e.-elliptic on every open cube,
not pointwise elliptic.
-/

noncomputable section

/-- Euclidean squared norm on doubled vectors in the full `2d` indexing. -/
def fullBlockVecNormSq {d : ℕ} (x : FullBlockVec d) : ℝ :=
  ∑ i, x i ^ 2

/-- Average of a real-valued function over a finite set. -/
noncomputable def finsetAverageReal {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ((s.card : ℝ)⁻¹) * s.sum f

/-- Constant block matrix associated with a constant coefficient matrix `a0`. -/
noncomputable def constantBlockMatrix {d : ℕ} (a0 : Mat d) : BlockMat d :=
  let sigma0 := symmPart a0
  let kappa0 := skewPart a0
  let sigma0Inv := sigma0⁻¹
  { upperLeft := sigma0 + matTranspose kappa0 * sigma0Inv * kappa0
    upperRight := -(matTranspose kappa0 * sigma0Inv)
    lowerLeft := -(sigma0Inv * kappa0)
    lowerRight := sigma0Inv }

/-- Constant block matrix in full `2d × 2d` matrix coordinates. -/
noncomputable def constantFullBlockMatrix {d : ℕ} [NeZero d] (a0 : Mat d) :
    FullBlockMat d :=
  toFullBlockMat (constantBlockMatrix a0)

/-- Positive square root used in the normalization of `\mathcal E`. -/
noncomputable def constantFullBlockMatrixSqrt {d : ℕ} [NeZero d] (a0 : Mat d) :
    FullBlockMat d :=
  CFC.sqrt (constantFullBlockMatrix a0)

/-- Inverse positive square root used in the normalization of `\mathcal E`. -/
noncomputable def constantFullBlockMatrixInvSqrt {d : ℕ} [NeZero d] (a0 : Mat d) :
    FullBlockMat d :=
  (constantFullBlockMatrixSqrt a0)⁻¹

/-- The normalized block-response value set
`max_{|e|=1} J(Q, A0^{-1/2} e, A0^{1/2} e; a)`. -/
noncomputable def normalizedBlockResponseValueSet {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) : Set ℝ :=
  { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
      m =
        doubledResponseJ (cubeDomain Q) (a.coeffOn Q)
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)) }

/-- The one-cube normalized block-response maximum. -/
noncomputable def normalizedBlockResponseMax {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  sSup (normalizedBlockResponseValueSet Q a a0)

/-- Maximum normalized block response over descendants of `Q` at scale `k`. -/
noncomputable def maxDescendantNormalizedBlockResponseAtScale {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℤ) (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  finsetSupReal (descendantsAtScale Q k) fun R => normalizedBlockResponseMax R a a0

/-- The `p`-aggregation over descendants at one scale in the definition of
`\mathcal E_{s,p,q}`. -/
noncomputable def scaleResponseAtScale {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℤ) (p : MultiscaleExponent)
    (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  match p with
  | .finite p =>
      Real.rpow
        (finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (normalizedBlockResponseMax R a a0) (p / 2)))
        (1 / p)
  | .infinity =>
      Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k a a0) (1 / 2)

/-- Finite-`q` multiscale homogenization error. -/
noncomputable def HomogenizationErrorFinite {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent) (q : ℝ)
    (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  Real.rpow
    (∑' l : ℕ,
      geometricWeight s q l *
        Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p a a0) q)
    (1 / q)

/-- Endpoint-`q` multiscale homogenization error. -/
noncomputable def HomogenizationErrorInfinity {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent)
    (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  sSup
    { m | ∃ l : ℕ,
        m =
          Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p a a0 }

/-- Multiscale homogenization error for finite `q` and `q = infinity`. -/
noncomputable def HomogenizationError {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p q : MultiscaleExponent)
    (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  match q with
  | .finite q => HomogenizationErrorFinite Q n s p q a a0
  | .infinity => HomogenizationErrorInfinity Q n s p a a0

/-- The untruncated cube quantity `\mathcal E_{s,p,q}(Q; a, a0)`, where the
truncation scale is the scale of `Q`. -/
noncomputable def HomogenizationErrorOnCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s : ℝ) (p q : MultiscaleExponent)
    (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  HomogenizationError Q Q.scale s p q a a0

end

end Ch02
end Book
end Homogenization
