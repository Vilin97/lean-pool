/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge

/-!
# Deterministic identities for Chapter 2 observables

This file is the public Chapter 2 owner for deterministic identities among the
scalar response, doubled `mu`, and block response observables.  Chapter 4 may
turn these identities into law-relative measurability statements; it should not
reprove the deterministic algebra.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- The public doubled-`mu` infimum agrees with the deterministic block `Mu`
on the same Chapter 2 domain.  This bridge belongs with the deterministic
old-engine identities rather than the clean doubled-`Mu` theorem surface. -/
theorem doubledMu_eq_Mu {d : ℕ} (U : Domain d) (a : CoeffOn U) (P : BlockVec d) :
    doubledMu U a P = Mu (U : Set (Vec d)) P a.toCoeffField :=
  Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U a P

/-- The scalar response is the doubled `mu` value at `(-p, q)`, up to the
deterministic pairing term. -/
theorem responseJ_eq_doubledMu_neg_left_sub_vecDot {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    responseJ U a p q = doubledMu U a (-p, q) - vecDot p q := by
  calc
    responseJ U a p q =
        (1 / 2 : ℝ) *
            blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) -
          vecDot p q :=
      Homogenization.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic U a p q
    _ = doubledMu U a (-p, q) - vecDot p q := by
      rw [← (doubledMuTheory U a).doubledMu_eq_coarseBlockMatrix (-p, q)]

/-- Old-engine scalar response equals old-engine `Mu` at `(-p, q)`, up to the
deterministic pairing term. -/
theorem ResponseJ_eq_Mu_neg_left_sub_vecDot {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) :
    ResponseJ (U : Set (Vec d)) p q a.toCoeffField =
      Mu (U : Set (Vec d)) (-p, q) a.toCoeffField - vecDot p q := by
  calc
    ResponseJ (U : Set (Vec d)) p q a.toCoeffField = responseJ U a p q :=
      (Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U a p q).symm
    _ = doubledMu U a (-p, q) - vecDot p q :=
      responseJ_eq_doubledMu_neg_left_sub_vecDot U a p q
    _ = Mu (U : Set (Vec d)) (-p, q) a.toCoeffField - vecDot p q := by
      rw [Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U a (-p, q)]

/-- Cube-set form of `ResponseJ_eq_Mu_neg_left_sub_vecDot`. -/
theorem ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q)) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a.toCoeffField =
      Mu (cubeSet Q) (-p, q) a.toCoeffField - vecDot p q := by
  calc
    ResponseJ (cubeSet Q) p q a.toCoeffField =
        ResponseJ (openCubeSet Q) p q a.toCoeffField :=
      responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a.toCoeffField
    _ = Mu (openCubeSet Q) (-p, q) a.toCoeffField - vecDot p q := by
      simpa [cubeDomain_coe] using ResponseJ_eq_Mu_neg_left_sub_vecDot
        (cubeDomain Q) a p q
    _ = Mu (cubeSet Q) (-p, q) a.toCoeffField - vecDot p q := by
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube
        (Q := Q) (P := (-p, q)) (a := a.toCoeffField)]

/-- Public scalar splitting for doubled response. -/
theorem doubledResponseJ_eq_half_responseJ_adjoint_sum {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p pStar q qStar : Vec d) :
    doubledResponseJ U a (p, q) (qStar, pStar) =
      (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
  (doubledResponseTheory U a).doubledResponseJ_eq_scalar p pStar q qStar

/-- Public bridge from doubled response to the old-engine `BlockJ`, under the
pointwise ellipticity hypothesis required by the old block response space. -/
theorem doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (P Q : BlockVec d) :
    doubledResponseJ U a P Q =
      BlockJ (U : Set (Vec d)) P Q a.toCoeffField :=
  Homogenization.Internal.Ch02.BookCh02.book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
    U a hEll P Q

/-- Old-engine `BlockJ` is the half-sum of the scalar responses for `a` and its
adjoint. -/
theorem BlockJ_eq_half_ResponseJ_adjoint_sum_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p pStar q qStar : Vec d) :
    BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField =
      (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d))
        (p - pStar) (qStar - q) a.toCoeffField +
      (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d))
        (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField) := by
  calc
    BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField =
        doubledResponseJ U a (p, q) (qStar, pStar) := by
      exact (doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
        U a hEll (p, q) (qStar, pStar)).symm
    _ =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
      doubledResponseJ_eq_half_responseJ_adjoint_sum U a p pStar q qStar
    _ =
        (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d))
            (p - pStar) (qStar - q) a.toCoeffField +
          (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d))
            (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField) := by
      rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U a,
        Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U a.transpose]
      have hAdj : a.transpose.toCoeffField = adjointCoeffField a.toCoeffField := by
        funext x
        rfl
      rw [hAdj]

/-- Cube-set form of the deterministic `BlockJ` half-sum identity. -/
theorem BlockJ_cubeSet_eq_half_ResponseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (hEll : IsEllipticFieldOn a.lam a.Lam (openCubeSet Q) a.toCoeffField)
    (p pStar q qStar : Vec d) :
    BlockJ (cubeSet Q) (p, q) (qStar, pStar) a.toCoeffField =
      (1 / 2 : ℝ) * ResponseJ (cubeSet Q)
        (p - pStar) (qStar - q) a.toCoeffField +
      (1 / 2 : ℝ) * ResponseJ (cubeSet Q)
        (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField) := by
  calc
    BlockJ (cubeSet Q) (p, q) (qStar, pStar) a.toCoeffField =
        BlockJ (openCubeSet Q) (p, q) (qStar, pStar) a.toCoeffField :=
      BlockJ_cubeSet_eq_openCubeSet_of_triadicCube Q (p, q) (qStar, pStar)
        a.toCoeffField
    _ =
        (1 / 2 : ℝ) * ResponseJ (openCubeSet Q)
            (p - pStar) (qStar - q) a.toCoeffField +
          (1 / 2 : ℝ) * ResponseJ (openCubeSet Q)
            (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField) := by
      simpa [cubeDomain_coe] using
        BlockJ_eq_half_ResponseJ_adjoint_sum_of_isEllipticFieldOn
          (cubeDomain Q) a (by simpa [cubeDomain_coe] using hEll) p pStar q qStar
    _ =
        (1 / 2 : ℝ) * ResponseJ (cubeSet Q)
            (p - pStar) (qStar - q) a.toCoeffField +
          (1 / 2 : ℝ) * ResponseJ (cubeSet Q)
            (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField) := by
      rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube
          Q (p - pStar) (qStar - q) a.toCoeffField,
        ← responseJ_cubeSet_eq_openCubeSet_of_triadicCube
          Q (pStar + p) (qStar + q) (adjointCoeffField a.toCoeffField)]

end

end Ch02
end Book
end Homogenization
