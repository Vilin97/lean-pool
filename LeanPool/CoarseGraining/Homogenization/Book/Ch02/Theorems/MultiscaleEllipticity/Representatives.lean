/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-! # Representatives -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Representative Bridges for Chapter 2.5 Multiscale Ellipticity

This file bridges public a.e. coefficient families to pointwise representatives
used by the deterministic multiscale ellipticity estimates.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius


/-- Restrict the pointwise-good representative of a root-cube coefficient
object to a smaller triadic cube.  This is an internal bridge object: public
coefficient fields remain a.e. objects, while old deterministic lemmas consume
pointwise elliptic representatives. -/
noncomputable def pointwiseCoeffOnRestrict {d : ℕ} {Q R : TriadicCube d}
    (aQ : CoeffOn (cubeDomain Q))
    (hsub : openCubeSet R ⊆ openCubeSet Q) :
    CoeffOn (cubeDomain R) where
  toCoeffField := Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ
  lam := aQ.lam
  Lam := aQ.Lam
  lam_pos := aQ.lam_pos
  lam_le_Lam := aQ.lam_le_Lam
  aeStronglyMeasurable := by
    classical
    intro i j
    have hcoeff :
        Measurable fun x : Vec d =>
          Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ x i j := by
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (Internal.Ch02.BookCh02.pointwiseCoeffField_measurable (cubeDomain Q) aQ) i) j)
    have hentry :
        Measurable fun x : Vec d =>
          restrictCoeffField (openCubeSet R)
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ) x i j := by
      have hite :
          Measurable fun x : Vec d =>
            if x ∈ openCubeSet R then
              Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ x i j
            else 0 :=
        Measurable.ite (measurableSet_openCubeSet R) hcoeff measurable_const
      convert hite using 1
      funext x
      by_cases hx : x ∈ openCubeSet R <;> simp [restrictCoeffField, hx]
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)]
      with x hxR
    exact (Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
      (cubeDomain Q) aQ).2 x (hsub hxR)

theorem coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict {d : ℕ}
    (a : TriadicCoeffFamily d) {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    CoeffOn.AEEq (a.coeffOn R)
      (pointwiseCoeffOnRestrict (a.coeffOn Q)
        (openCubeSet_subset_of_mem_descendantsAtScale hk hR)) := by
  have hrestrict : CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn R) :=
    a.restrictsTo_descendant hk hR
  have hpointQ :
      Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          (a.coeffOn Q).toCoeffField := by
    simpa using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (cubeDomain Q) (a.coeffOn Q)
  have hpointR' :
      Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
        =ᵐ[volumeMeasureOn (openCubeSet R)]
          (a.coeffOn Q).toCoeffField :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR) hpointQ
  exact hrestrict.trans (Filter.EventuallyEq.symm hpointR')

theorem pointwiseCoeffField_openCube_descendant_data {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (aQ : CoeffOn (cubeDomain Q)) :
    OpenCubeDescendantDeterministicCoarseData Q
      (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ) := by
  have hEll :
      IsEllipticFieldOn aQ.lam aQ.Lam (openCubeSet Q)
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ) := by
    simpa using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) aQ
  have hOrigin : OpenCubeOriginEllipticRecoveryExistence aQ.lam aQ.Lam :=
    openCubeOriginEllipticRecoveryExistence
      (d := d) (lam := aQ.lam) (Lam := aQ.Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      Q (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) aQ)
      hEll hOrigin
  exact openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec

theorem coarseBMatrixNorm_le_coarseBBlockNorm_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    coarseBMatrixNorm R a ≤
      Homogenization.coarseBBlockNorm R
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict
      (a := a) hk hR
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hSCanon :
      IsSigmaStarCoarse (openCubeSet R) A
        (Homogenization.sigmaStarCoarse (openCubeSet R) A) := by
    simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet] using hS
  have hUpperCanon :
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet R) A)
          (Homogenization.sigmaStarCoarse (openCubeSet R) A)
          (Homogenization.kappaCoarse (openCubeSet R) A) := by
    calc
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft =
          Homogenization.bCoarse sigma sigmaStar kappa := by
            exact coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix
              hA hS hK hSigma hdet
      _ =
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A) := by
              rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
                eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
                eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  calc
    coarseBMatrixNorm R a =
        matrixNorm (bCoarse (cubeDomain R) (a.coeffOn R)) := by
          rfl
    _ = matrixNorm (bCoarse (cubeDomain R) aRpw) := by
          rw [bCoarse_eq_ofAEEq haeeq]
    _ =
        matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A)) := by
          simpa [bCoarse, aRpw, A] using!
            congrArg matrixNorm
              (Internal.Ch02.book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse
                (cubeDomain R) aRpw hSCanon)
    _ ≤
        Homogenization.matNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A)) := by
          exact matrixNorm_le_matNorm _
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft := by
          rw [hUpperCanon]
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (cubeSet R) A).upperLeft := by
          rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R A]
    _ = Homogenization.coarseBBlockNorm R A := by
          rfl

theorem coarseSigmaStarInvMatrixNorm_le_coarseSigmaStarInvBlockNorm_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    coarseSigmaStarInvMatrixNorm R a ≤
      Homogenization.coarseSigmaStarInvBlockNorm R
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict
      (a := a) hk hR
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hLower :
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).lowerRight =
        Homogenization.sigmaStarInvCoarse (openCubeSet R) A :=
    coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA
  calc
    coarseSigmaStarInvMatrixNorm R a =
        matrixNorm (sigmaStarInvCoarse (cubeDomain R) (a.coeffOn R)) := by
          rfl
    _ = matrixNorm (sigmaStarInvCoarse (cubeDomain R) aRpw) := by
          rw [sigmaStarInvCoarse_eq_ofAEEq haeeq]
    _ = matrixNorm (Homogenization.sigmaStarInvCoarse (openCubeSet R) A) := by
          simpa [aRpw, A] using!
            congrArg matrixNorm
              (Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse
                (cubeDomain R) aRpw)
    _ ≤ Homogenization.matNorm (Homogenization.sigmaStarInvCoarse (openCubeSet R) A) := by
          exact matrixNorm_le_matNorm _
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (openCubeSet R) A).lowerRight := by
          rw [hLower]
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (cubeSet R) A).lowerRight := by
          rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R A]
    _ = Homogenization.coarseSigmaStarInvBlockNorm R A := by
          rfl

theorem coarseBMatrixNorm_eq_matrixNorm_bCoarse_pointwiseCoeffField_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    coarseBMatrixNorm R a =
      matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (cubeSet R)
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
          (Homogenization.sigmaStarCoarse (cubeSet R)
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
          (Homogenization.kappaCoarse (cubeSet R)
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict
      (a := a) hk hR
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hSCanon :
      IsSigmaStarCoarse (openCubeSet R) A
        (Homogenization.sigmaStarCoarse (openCubeSet R) A) := by
    simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet] using hS
  have hOpenCube :
      Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet R) A)
          (Homogenization.sigmaStarCoarse (openCubeSet R) A)
          (Homogenization.kappaCoarse (openCubeSet R) A) =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (cubeSet R) A)
          (Homogenization.sigmaStarCoarse (cubeSet R) A)
          (Homogenization.kappaCoarse (cubeSet R) A) := by
    symm
    rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
      (Q := R) (a := A) hS hK hSigma hdet]
  calc
    coarseBMatrixNorm R a =
        matrixNorm (bCoarse (cubeDomain R) (a.coeffOn R)) := by
          rfl
    _ = matrixNorm (bCoarse (cubeDomain R) aRpw) := by
          rw [bCoarse_eq_ofAEEq haeeq]
    _ =
        matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A)) := by
          simpa [bCoarse, aRpw, A] using!
            congrArg matrixNorm
              (Internal.Ch02.book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse
                (cubeDomain R) aRpw hSCanon)
    _ =
        matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet R) A)
            (Homogenization.sigmaStarCoarse (cubeSet R) A)
            (Homogenization.kappaCoarse (cubeSet R) A)) := by
          rw [hOpenCube]

theorem coarseSigmaStarInvMatrixNorm_eq_matrixNorm_sigmaStarInv_pointwiseCoeffField_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    coarseSigmaStarInvMatrixNorm R a =
      matrixNorm
        (Homogenization.sigmaStarInvCoarse (cubeSet R)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q))) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict
      (a := a) hk hR
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hOpenCube :
      Homogenization.sigmaStarInvCoarse (openCubeSet R) A =
        Homogenization.sigmaStarInvCoarse (cubeSet R) A := by
    symm
    rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := R) (a := A) hS]
  calc
    coarseSigmaStarInvMatrixNorm R a =
        matrixNorm (sigmaStarInvCoarse (cubeDomain R) (a.coeffOn R)) := by
          rfl
    _ = matrixNorm (sigmaStarInvCoarse (cubeDomain R) aRpw) := by
          rw [sigmaStarInvCoarse_eq_ofAEEq haeeq]
    _ = matrixNorm (Homogenization.sigmaStarInvCoarse (openCubeSet R) A) := by
          simpa [aRpw, A] using!
            congrArg matrixNorm
              (Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse
                (cubeDomain R) aRpw)
    _ = matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet R) A) := by
          rw [hOpenCube]

theorem coarseBBlockNorm_le_dim_mul_coarseBMatrixNorm_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    Homogenization.coarseBBlockNorm R
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * coarseBMatrixNorm R a := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hUpperCanon :
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet R) A)
          (Homogenization.sigmaStarCoarse (openCubeSet R) A)
          (Homogenization.kappaCoarse (openCubeSet R) A) := by
    calc
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft =
          Homogenization.bCoarse sigma sigmaStar kappa := by
            exact coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix
              hA hS hK hSigma hdet
      _ =
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A) := by
              rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
                eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
                eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  have hOpenCube :
      Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet R) A)
          (Homogenization.sigmaStarCoarse (openCubeSet R) A)
          (Homogenization.kappaCoarse (openCubeSet R) A) =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (cubeSet R) A)
          (Homogenization.sigmaStarCoarse (cubeSet R) A)
          (Homogenization.kappaCoarse (cubeSet R) A) := by
    symm
    rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
      (Q := R) (a := A) hS hK hSigma hdet]
  calc
    Homogenization.coarseBBlockNorm R A =
        Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (cubeSet R) A).upperLeft := by
          rfl
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (openCubeSet R) A).upperLeft := by
          rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R A]
    _ =
        Homogenization.matNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A)) := by
          rw [hUpperCanon]
    _ =
        Homogenization.matNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet R) A)
            (Homogenization.sigmaStarCoarse (cubeSet R) A)
            (Homogenization.kappaCoarse (cubeSet R) A)) := by
          rw [hOpenCube]
    _ ≤
        (d : ℝ) *
          matrixNorm
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A)) :=
          matNorm_le_dim_mul_matrixNorm _
    _ = (d : ℝ) * coarseBMatrixNorm R a := by
          rw [coarseBMatrixNorm_eq_matrixNorm_bCoarse_pointwiseCoeffField_of_mem_descendantsAtScale
            (a := a) hk hR]

theorem coarseSigmaStarInvBlockNorm_le_dim_mul_coarseSigmaStarInvMatrixNorm_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    Homogenization.coarseSigmaStarInvBlockNorm R
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * coarseSigmaStarInvMatrixNorm R a := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hDataR : OpenCubeDeterministicCoarseData R A :=
    hData k hk R hR
  rcases hDataR with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hLower :
      (Homogenization.coarseBlockMatrix (openCubeSet R) A).lowerRight =
        Homogenization.sigmaStarInvCoarse (openCubeSet R) A :=
    coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA
  have hOpenCube :
      Homogenization.sigmaStarInvCoarse (openCubeSet R) A =
        Homogenization.sigmaStarInvCoarse (cubeSet R) A := by
    symm
    rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := R) (a := A) hS]
  calc
    Homogenization.coarseSigmaStarInvBlockNorm R A =
        Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (cubeSet R) A).lowerRight := by
          rfl
    _ = Homogenization.matNorm
          (Homogenization.coarseBlockMatrix (openCubeSet R) A).lowerRight := by
          rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R A]
    _ = Homogenization.matNorm
          (Homogenization.sigmaStarInvCoarse (openCubeSet R) A) := by
          rw [hLower]
    _ = Homogenization.matNorm
          (Homogenization.sigmaStarInvCoarse (cubeSet R) A) := by
          rw [hOpenCube]
    _ ≤
        (d : ℝ) *
          matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet R) A) :=
          matNorm_le_dim_mul_matrixNorm _
    _ = (d : ℝ) * coarseSigmaStarInvMatrixNorm R a := by
          rw [coarseSigmaStarInvMatrixNorm_eq_matrixNorm_sigmaStarInv_pointwiseCoeffField_of_mem_descendantsAtScale
            (a := a) hk hR]

theorem coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) :
    coarseBMatrixNorm Q a ≤ maxDescendantBMatrixNormAtScale Q k a := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let j : ℕ := Int.toNat (Q.scale - k)
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hQQ : Q ∈ descendantsAtScale Q Q.scale := by
    simp [descendantsAtScale_self]
  rcases hData Q.scale le_rfl Q hQQ with
    ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  have hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) A
            (deterministicCoarseBlockMatrix (openCubeSet R) A) ∧
          IsSigmaStarCoarse (openCubeSet R) A sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) A sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) A sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    exact hData k hk R hRk
  have hAvgEq :
      descendantsAverageMat Q j
        (fun R =>
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A)) =
        descendantsAverageMat Q j
          (fun R =>
            Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A)) := by
    ext i l
    unfold descendantsAverageMat descendantsAverage
    refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet R) A)
            (Homogenization.sigmaStarCoarse (openCubeSet R) A)
            (Homogenization.kappaCoarse (openCubeSet R) A) =
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet R) A)
            (Homogenization.sigmaStarCoarse (cubeSet R) A)
            (Homogenization.kappaCoarse (cubeSet R) A) := by
      symm
      rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
        (Q := R) (a := A) hSR hKR hSigmaR hdetR]
    simpa using congrArg (fun M : Mat d => M i l) hcanonR
  have hLoewner :
      MatLoewnerLE
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (cubeSet Q) A)
          (Homogenization.sigmaStarCoarse (cubeSet Q) A)
          (Homogenization.kappaCoarse (cubeSet Q) A))
        (descendantsAverageMat Q j
          (fun R =>
            Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A))) := by
    intro p
    calc
      (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet Q) A)
              (Homogenization.sigmaStarCoarse (cubeSet Q) A)
              (Homogenization.kappaCoarse (cubeSet Q) A)) p) =
        (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (openCubeSet Q) A)
              (Homogenization.sigmaStarCoarse (openCubeSet Q) A)
              (Homogenization.kappaCoarse (openCubeSet Q) A)) p) := by
            rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
              (Q := Q) (a := A) hSQ hKQ hSigmaQ hdetQ]
      _ ≤ (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (descendantsAverageMat Q j
                (fun R =>
                  Homogenization.bCoarse
                    (Homogenization.sigmaCoarse (openCubeSet R) A)
                    (Homogenization.sigmaStarCoarse (openCubeSet R) A)
                    (Homogenization.kappaCoarse (openCubeSet R) A))) p) := by
              exact
                Homogenization.bCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
                  j Q A hEll hSQ hKQ hSigmaQ hdetQ hDesc p
      _ = (1 / 2 : ℝ) * vecDot p
            (matVecMul
              (descendantsAverageMat Q j
                (fun R =>
                  Homogenization.bCoarse
                    (Homogenization.sigmaCoarse (cubeSet R) A)
                    (Homogenization.sigmaStarCoarse (cubeSet R) A)
                    (Homogenization.kappaCoarse (cubeSet R) A))) p) := by
              rw [hAvgEq]
  have hParentPSD :
      (Homogenization.bCoarse
        (Homogenization.sigmaCoarse (cubeSet Q) A)
        (Homogenization.sigmaStarCoarse (cubeSet Q) A)
        (Homogenization.kappaCoarse (cubeSet Q) A)).PosSemidef := by
    rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
      (Q := Q) (a := A) hSQ hKQ hSigmaQ hdetQ]
    exact Homogenization.bCoarse_canonical_posSemidef_of_isSigmaCoarse
      hSQ hKQ hSigmaQ hdetQ
  have hAvgPSD :
      (descendantsAverageMat Q j
        (fun R =>
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet R) A)
            (Homogenization.sigmaStarCoarse (cubeSet R) A)
            (Homogenization.kappaCoarse (cubeSet R) A))).PosSemidef := by
    refine Homogenization.descendantsAverageMat_posSemidef ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        Homogenization.bCoarse sigmaR sigmaStarR kappaR =
          Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet R) A)
            (Homogenization.sigmaStarCoarse (cubeSet R) A)
            (Homogenization.kappaCoarse (cubeSet R) A) := by
      calc
        Homogenization.bCoarse sigmaR sigmaStarR kappaR =
            Homogenization.bCoarse
              (Homogenization.sigmaCoarse (openCubeSet R) A)
              (Homogenization.sigmaStarCoarse (openCubeSet R) A)
              (Homogenization.kappaCoarse (openCubeSet R) A) := by
                rw [Homogenization.sigmaCoarse_eq_of_isSigmaCoarse hSR hKR hSigmaR hdetR,
                  Homogenization.eq_sigmaStarCoarse_of_isSigmaStarCoarse hSR hdetR,
                  Homogenization.eq_kappaCoarse_of_isKappaCoarse hSR hKR hdetR]
        _ =
            Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A) := by
                symm
                rw [Homogenization.bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
                  (Q := R) (a := A) hSR hKR hSigmaR hdetR]
    rw [← hcanonR]
    exact Homogenization.bCoarse_posSemidef_of_isSigmaCoarse hSR hSigmaR
  have hParentEq :
      coarseBMatrixNorm Q a =
        matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet Q) A)
            (Homogenization.sigmaStarCoarse (cubeSet Q) A)
            (Homogenization.kappaCoarse (cubeSet Q) A)) := by
    simpa [A] using
      coarseBMatrixNorm_eq_matrixNorm_bCoarse_pointwiseCoeffField_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := Q) (k := Q.scale) le_rfl hQQ
  have hterm_eq :
      ∀ R ∈ descendantsAtDepth Q j,
        matrixNorm
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A)) =
          coarseBMatrixNorm R a := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    simpa [A] using
      (coarseBMatrixNorm_eq_matrixNorm_bCoarse_pointwiseCoeffField_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := R) (k := k) hk hRk).symm
  calc
    coarseBMatrixNorm Q a =
        matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (cubeSet Q) A)
            (Homogenization.sigmaStarCoarse (cubeSet Q) A)
            (Homogenization.kappaCoarse (cubeSet Q) A)) := hParentEq
    _ ≤
        matrixNorm
          (descendantsAverageMat Q j
            (fun R =>
              Homogenization.bCoarse
                (Homogenization.sigmaCoarse (cubeSet R) A)
                (Homogenization.sigmaStarCoarse (cubeSet R) A)
                (Homogenization.kappaCoarse (cubeSet R) A))) := by
          exact matrixNorm_le_of_matLoewnerLE_of_posSemidef
            hParentPSD hAvgPSD hLoewner
    _ ≤ finsetSupReal (descendantsAtDepth Q j)
          (fun R =>
            matrixNorm
              (Homogenization.bCoarse
                (Homogenization.sigmaCoarse (cubeSet R) A)
                (Homogenization.sigmaStarCoarse (cubeSet R) A)
                (Homogenization.kappaCoarse (cubeSet R) A))) := by
          exact matrixNorm_descendantsAverageMat_le_finsetSupReal_matrixNorm Q j
            (fun R =>
              Homogenization.bCoarse
                (Homogenization.sigmaCoarse (cubeSet R) A)
                (Homogenization.sigmaStarCoarse (cubeSet R) A)
                (Homogenization.kappaCoarse (cubeSet R) A))
    _ = finsetSupReal (descendantsAtDepth Q j)
          (fun R => coarseBMatrixNorm R a) := by
          exact finsetSupReal_congr (descendantsAtDepth Q j) hterm_eq
    _ = maxDescendantBMatrixNormAtScale Q k a := by
          unfold maxDescendantBMatrixNormAtScale
          rw [descendantsAtScale_eq_descendantsAtDepth Q hk]

theorem coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) :
    coarseSigmaStarInvMatrixNorm Q a ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let j : ℕ := Int.toNat (Q.scale - k)
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData :
      OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hQQ : Q ∈ descendantsAtScale Q Q.scale := by
    simp [descendantsAtScale_self]
  rcases hData Q.scale le_rfl Q hQQ with
    ⟨sigmaQ, sigmaStarQ, kappaQ, hAQ, hSQ, hKQ, hSigmaQ, hdetQ⟩
  have hDesc :
      ∀ R ∈ descendantsAtDepth Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) A
            (deterministicCoarseBlockMatrix (openCubeSet R) A) ∧
          IsSigmaStarCoarse (openCubeSet R) A sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) A sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) A sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    exact hData k hk R hRk
  have hAvgEq :
      descendantsAverageMat Q j
          (fun R => Homogenization.sigmaStarInvCoarse (openCubeSet R) A) =
        descendantsAverageMat Q j
          (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A) := by
    ext i l
    unfold descendantsAverageMat descendantsAverage
    refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    have hcanonR :
        Homogenization.sigmaStarInvCoarse (openCubeSet R) A =
          Homogenization.sigmaStarInvCoarse (cubeSet R) A := by
      symm
      rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
        (Q := R) (a := A) hSR]
    simpa using congrArg (fun M : Mat d => M i l) hcanonR
  have hLoewner :
      MatLoewnerLE (Homogenization.sigmaStarInvCoarse (cubeSet Q) A)
        (descendantsAverageMat Q j
          (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A)) := by
    intro q
    calc
      (1 / 2 : ℝ) * vecDot q
          (matVecMul (Homogenization.sigmaStarInvCoarse (cubeSet Q) A) q) =
        (1 / 2 : ℝ) * vecDot q
          (matVecMul (Homogenization.sigmaStarInvCoarse (openCubeSet Q) A) q) := by
            rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
              (Q := Q) (a := A) hSQ]
      _ ≤ (1 / 2 : ℝ) * vecDot q
            (matVecMul
              (descendantsAverageMat Q j
                (fun R => Homogenization.sigmaStarInvCoarse (openCubeSet R) A)) q) := by
              exact
                Homogenization.sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
                  j Q A hEll hSQ hKQ hSigmaQ hdetQ hDesc q
      _ = (1 / 2 : ℝ) * vecDot q
            (matVecMul
              (descendantsAverageMat Q j
                (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A)) q) := by
              rw [hAvgEq]
  have hParentPSD :
      (Homogenization.sigmaStarInvCoarse (cubeSet Q) A).PosSemidef := by
    rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := Q) (a := A) hSQ]
    exact Homogenization.sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse
      (U := openCubeSet Q) (a := A) hSQ
  have hAvgPSD :
      (descendantsAverageMat Q j
        (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A)).PosSemidef := by
    refine Homogenization.descendantsAverageMat_posSemidef ?_
    intro R hR
    rcases hDesc R hR with
      ⟨sigmaR, sigmaStarR, kappaR, hAR, hSR, hKR, hSigmaR, hdetR⟩
    rw [Homogenization.sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
      (Q := R) (a := A) hSR]
    exact Homogenization.sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse
      (U := openCubeSet R) (a := A) hSR
  have hParentEq :
      coarseSigmaStarInvMatrixNorm Q a =
        matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet Q) A) := by
    simpa [A] using
      coarseSigmaStarInvMatrixNorm_eq_matrixNorm_sigmaStarInv_pointwiseCoeffField_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := Q) (k := Q.scale) le_rfl hQQ
  have hterm_eq :
      ∀ R ∈ descendantsAtDepth Q j,
        matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet R) A) =
          coarseSigmaStarInvMatrixNorm R a := by
    intro R hR
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hR
    simpa [A] using
      (coarseSigmaStarInvMatrixNorm_eq_matrixNorm_sigmaStarInv_pointwiseCoeffField_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := R) (k := k) hk hRk).symm
  calc
    coarseSigmaStarInvMatrixNorm Q a =
        matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet Q) A) := hParentEq
    _ ≤
        matrixNorm
          (descendantsAverageMat Q j
            (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A)) := by
          exact matrixNorm_le_of_matLoewnerLE_of_posSemidef
            hParentPSD hAvgPSD hLoewner
    _ ≤ finsetSupReal (descendantsAtDepth Q j)
          (fun R =>
            matrixNorm (Homogenization.sigmaStarInvCoarse (cubeSet R) A)) := by
          exact matrixNorm_descendantsAverageMat_le_finsetSupReal_matrixNorm Q j
            (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R) A)
    _ = finsetSupReal (descendantsAtDepth Q j)
          (fun R => coarseSigmaStarInvMatrixNorm R a) := by
          exact finsetSupReal_congr (descendantsAtDepth Q j) hterm_eq
    _ = maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
          unfold maxDescendantSigmaStarInvMatrixNormAtScale
          rw [descendantsAtScale_eq_descendantsAtDepth Q hk]

theorem maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    maxDescendantBMatrixNormAtScale Q k a ≤
      Homogenization.maxDescendantBBlockNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  refine finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  exact coarseBMatrixNorm_le_coarseBBlockNorm_of_mem_descendantsAtScale
    (a := a) hk hR

theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      Homogenization.maxDescendantSigmaStarInvNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  refine finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  exact coarseSigmaStarInvMatrixNorm_le_coarseSigmaStarInvBlockNorm_of_mem_descendantsAtScale
    (a := a) hk hR

theorem maxDescendantBBlockNormAtScale_le_dim_mul_maxDescendantBMatrixNormAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    Homogenization.maxDescendantBBlockNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * maxDescendantBMatrixNormAtScale Q k a := by
  have hs : (descendantsAtScale Q k).Nonempty := descendantsAtScale_nonempty Q hk
  calc
    Homogenization.maxDescendantBBlockNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
        finsetSupReal (descendantsAtScale Q k)
          (fun R => (d : ℝ) * coarseBMatrixNorm R a) := by
          refine finsetSupReal_mono (descendantsAtScale Q k) hs ?_
          intro R hR
          exact coarseBBlockNorm_le_dim_mul_coarseBMatrixNorm_of_mem_descendantsAtScale
            (a := a) hk hR
    _ ≤ (d : ℝ) * maxDescendantBMatrixNormAtScale Q k a := by
          exact finsetSupReal_const_mul_le (descendantsAtScale Q k) hs
            (Nat.cast_nonneg d) (fun R => coarseBMatrixNorm R a)

theorem maxDescendantSigmaStarInvNormAtScale_le_dim_mul_maxDescendantSigmaStarInvMatrixNormAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    Homogenization.maxDescendantSigmaStarInvNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
  have hs : (descendantsAtScale Q k).Nonempty := descendantsAtScale_nonempty Q hk
  calc
    Homogenization.maxDescendantSigmaStarInvNormAtScale Q k
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
        finsetSupReal (descendantsAtScale Q k)
          (fun R => (d : ℝ) * coarseSigmaStarInvMatrixNorm R a) := by
          refine finsetSupReal_mono (descendantsAtScale Q k) hs ?_
          intro R hR
          exact coarseSigmaStarInvBlockNorm_le_dim_mul_coarseSigmaStarInvMatrixNorm_of_mem_descendantsAtScale
            (a := a) hk hR
    _ ≤ (d : ℝ) * maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
          exact finsetSupReal_const_mul_le (descendantsAtScale Q k) hs
            (Nat.cast_nonneg d) (fun R => coarseSigmaStarInvMatrixNorm R a)

theorem maxDescendantBMatrixNormAtScale_le_old_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantBMatrixNormAtScale R l a ≤
      Homogenization.maxDescendantBBlockNormAtScale R l
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  have hRscale : R.scale = k := Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlQ : l ≤ Q.scale := by
    exact le_trans (by simpa [hRscale] using hl) hk
  refine finsetSupReal_mono (descendantsAtScale R l)
    (descendantsAtScale_nonempty R hl) ?_
  intro S hS
  exact coarseBMatrixNorm_le_coarseBBlockNorm_of_mem_descendantsAtScale
    (a := a) (Q := Q) (R := S) (k := l) hlQ
    (Homogenization.mem_descendantsAtScale_trans hR hS)

theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_old_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantSigmaStarInvMatrixNormAtScale R l a ≤
      Homogenization.maxDescendantSigmaStarInvNormAtScale R l
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  have hRscale : R.scale = k := Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlQ : l ≤ Q.scale := by
    exact le_trans (by simpa [hRscale] using hl) hk
  refine finsetSupReal_mono (descendantsAtScale R l)
    (descendantsAtScale_nonempty R hl) ?_
  intro S hS
  exact coarseSigmaStarInvMatrixNorm_le_coarseSigmaStarInvBlockNorm_of_mem_descendantsAtScale
    (a := a) (Q := Q) (R := S) (k := l) hlQ
    (Homogenization.mem_descendantsAtScale_trans hR hS)

theorem maxDescendantBMatrixNormAtScale_self {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    maxDescendantBMatrixNormAtScale Q Q.scale a = coarseBMatrixNorm Q a := by
  unfold maxDescendantBMatrixNormAtScale finsetSupReal
  simp [descendantsAtScale_self]

theorem maxDescendantSigmaStarInvMatrixNormAtScale_self {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a =
      coarseSigmaStarInvMatrixNorm Q a := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale finsetSupReal
  simp [descendantsAtScale_self]

theorem maxDescendantBMatrixNormAtScale_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (_hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) :
    0 ≤ maxDescendantBMatrixNormAtScale Q k a := by
  exact finsetSupReal_nonneg (descendantsAtScale Q k)
    (fun R => coarseBMatrixNorm R a)
    (fun R _hR => coarseBMatrixNorm_nonneg R a)

theorem maxDescendantSigmaStarInvMatrixNormAtScale_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (_hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) :
    0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
  exact finsetSupReal_nonneg (descendantsAtScale Q k)
    (fun R => coarseSigmaStarInvMatrixNorm R a)
    (fun R _hR => coarseSigmaStarInvMatrixNorm_nonneg R a)

theorem maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantBMatrixNormAtScale R l a ≤
      maxDescendantBMatrixNormAtScale Q l a := by
  refine finsetSupReal_le_of_subset (descendantsAtScale R l)
    (descendantsAtScale Q l) (descendantsAtScale_nonempty R hl) ?_
    (fun S => coarseBMatrixNorm S a)
  intro S hS
  exact Homogenization.mem_descendantsAtScale_trans hR hS

theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k l : ℤ}
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantSigmaStarInvMatrixNormAtScale R l a ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q l a := by
  refine finsetSupReal_le_of_subset (descendantsAtScale R l)
    (descendantsAtScale Q l) (descendantsAtScale_nonempty R hl) ?_
    (fun S => coarseSigmaStarInvMatrixNorm S a)
  intro S hS
  exact Homogenization.mem_descendantsAtScale_trans hR hS

theorem maxDescendantBMatrixNormAtScale_le_of_le
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {l k : ℤ} (hlk : l ≤ k) (hk : k ≤ Q.scale) :
    maxDescendantBMatrixNormAtScale Q k a ≤
      maxDescendantBMatrixNormAtScale Q l a := by
  refine finsetSupReal_le (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlR : l ≤ R.scale := by
    simpa [hRscale] using hlk
  exact (coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale R hlR a).trans
    (maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale a hR hlR)

theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    (Q : TriadicCube d) {l k : ℤ} (hlk : l ≤ k) (hk : k ≤ Q.scale) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q l a := by
  refine finsetSupReal_le (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hlR : l ≤ R.scale := by
    simpa [hRscale] using hlk
  exact
    (coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
      R hlR a).trans
    (maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale a hR hlR)

theorem summable_old_B_series_pointwiseCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      Homogenization.geometricWeight s q n *
        Real.rpow
          (Homogenization.maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ))
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
          (q / 2)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹ *
    (a.coeffOn Q).Lam ^ 2
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := q) (C := Real.rpow C (q / 2)) (mul_pos hs hq) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (Homogenization.maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) A) _
  · intro n
    have hbound :
        Homogenization.maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A ≤ C := by
      simpa [A, C] using
        Homogenization.maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          (Q := Q) (a := A) hEll hData n
    exact Real.rpow_le_rpow
      (Homogenization.maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) A)
      hbound (by positivity)

theorem summable_old_sigmaStarInv_series_pointwiseCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      Homogenization.geometricWeight s q n *
        Real.rpow
          (Homogenization.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ))
            (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
          (q / 2)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := q) (C := Real.rpow C (q / 2)) (mul_pos hs hq) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (Homogenization.maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) A) _
  · intro n
    have hbound :
        Homogenization.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A ≤ C := by
      simpa [A, C] using
        Homogenization.maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          (Q := Q) (a := A) hEll hData n
    exact Real.rpow_le_rpow
      (Homogenization.maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) A)
      hbound (by positivity)

theorem summable_B_series_pointwiseCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      geometricWeight s q n *
        Real.rpow
          (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hOld := summable_old_B_series_pointwiseCoeffField Q a hs hq
  refine Summable.of_nonneg_of_le ?_ ?_ (by simpa [A] using hOld)
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hq.le)
    · exact Real.rpow_nonneg
        (maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a) _
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight : 0 ≤ geometricWeight s q n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hq.le)
    have hmax :=
      maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2) ≤
          Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (q / 2) := by
      exact Real.rpow_le_rpow
        (maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a)
        (by simpa [A] using hmax) (by positivity)
    exact mul_le_mul_of_nonneg_left hpow hweight

theorem summable_sigmaStarInv_series_pointwiseCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      geometricWeight s q n *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hOld := summable_old_sigmaStarInv_series_pointwiseCoeffField Q a hs hq
  refine Summable.of_nonneg_of_le ?_ ?_ (by simpa [A] using hOld)
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hq.le)
    · exact Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (sub_le_self _ hn) a) _
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight : 0 ≤ geometricWeight s q n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hq.le)
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a) (q / 2) ≤
          Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (q / 2) := by
      exact Real.rpow_le_rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (sub_le_self _ hn) a)
        (by simpa [A] using hmax) (by positivity)
    exact mul_le_mul_of_nonneg_left hpow hweight

end

end Ch02
end Book
end Homogenization
