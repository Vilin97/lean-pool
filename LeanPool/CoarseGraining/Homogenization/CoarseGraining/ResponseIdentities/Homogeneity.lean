/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas

/-! # Homogeneity -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
Homogeneity statements for deterministic coarse scalar objects.
-/

theorem isSigmaStarInvCoarse_homogeneous_coeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) {lam : ℝ} (hlam : 0 < lam) :
    IsSigmaStarInvCoarse U (lam • a) (lam⁻¹ • sigmaStar⁻¹) := by
  have hInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  rcases hS with ⟨_, hresp⟩
  have hsqrt : (Real.sqrt lam) ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  have hsqInv : ((Real.sqrt lam)⁻¹ : ℝ) ^ 2 = lam⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt hlam)]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    show lam⁻¹ * sigmaStar⁻¹ j i = lam⁻¹ * sigmaStar⁻¹ i j
    rw [hInvSymm.apply j i]
  · intro q
    calc
      ResponseJ U 0 q (lam • a) =
          ResponseJ U 0 ((Real.sqrt lam)⁻¹ • q) a := by
            simpa [Real.sq_sqrt (le_of_lt hlam)] using
              responseJ_homogeneous_coeffField_sq U 0 q a (Real.sqrt lam) hsqrt
      _ = (1 / 2 : ℝ) *
            vecDot (((Real.sqrt lam)⁻¹ : ℝ) • q)
              (matVecMul sigmaStar⁻¹ (((Real.sqrt lam)⁻¹ : ℝ) • q)) := by
            simpa using hresp (((Real.sqrt lam)⁻¹ : ℝ) • q)
      _ = (1 / 2 : ℝ) * (((Real.sqrt lam)⁻¹ : ℝ) ^ 2) *
            vecDot q (matVecMul sigmaStar⁻¹ q) := by
            rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
            ring
      _ = (1 / 2 : ℝ) * lam⁻¹ * vecDot q (matVecMul sigmaStar⁻¹ q) := by
            rw [hsqInv]
      _ = (1 / 2 : ℝ) * vecDot q (matVecMul (lam⁻¹ • sigmaStar⁻¹) q) := by
            rw [smul_matVecMul, vecDot_smul_right]
            ring

theorem sigmaStarInvCoarse_homogeneous_coeffField_of_isSigmaStarCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarInvCoarse U (lam • a) = lam⁻¹ • sigmaStarInvCoarse U a := by
  calc
    sigmaStarInvCoarse U (lam • a) = lam⁻¹ • sigmaStar⁻¹ := by
      symm
      exact eq_sigmaStarInvCoarse_of_isSigmaStarInvCoarse
        (isSigmaStarInvCoarse_homogeneous_coeffField U a hS hlam)
    _ = lam⁻¹ • sigmaStarInvCoarse U a := by
      rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]

/-- Note-facing homogeneity for `\sigma_*^{-1}(U; a)` under coefficient
rescaling. -/
theorem sigmaStarInvCoarse_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarInvCoarse U (lam • a) = lam⁻¹ • sigmaStarInvCoarse U a :=
  sigmaStarInvCoarse_homogeneous_coeffField_of_isSigmaStarCoarse U a hS hlam

theorem isSigmaStarInvKappaCoarse_homogeneous_coeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa) {lam : ℝ} (hlam : 0 < lam) :
    IsSigmaStarInvKappaCoarse U (lam • a) (sigmaStar⁻¹ * kappa) := by
  have hsqrt : (Real.sqrt lam) ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  intro p q
  have hpq :
      ResponseJ U p q (lam • a) =
        ResponseJ U (Real.sqrt lam • p) (((Real.sqrt lam)⁻¹ : ℝ) • q) a := by
    simpa [Real.sq_sqrt (le_of_lt hlam)] using
      responseJ_homogeneous_coeffField_sq U p q a (Real.sqrt lam) hsqrt
  have hp0 :
      ResponseJ U p 0 (lam • a) = ResponseJ U (Real.sqrt lam • p) 0 a := by
    simpa [Real.sq_sqrt (le_of_lt hlam)] using
      responseJ_homogeneous_coeffField_sq U p 0 a (Real.sqrt lam) hsqrt
  have h0q :
      ResponseJ U 0 q (lam • a) = ResponseJ U 0 (((Real.sqrt lam)⁻¹ : ℝ) • q) a := by
    simpa [Real.sq_sqrt (le_of_lt hlam)] using
      responseJ_homogeneous_coeffField_sq U 0 q a (Real.sqrt lam) hsqrt
  calc
    ResponseJ U p q (lam • a) - ResponseJ U p 0 (lam • a) - ResponseJ U 0 q (lam • a) +
        vecDot p q =
      ResponseJ U (Real.sqrt lam • p) (((Real.sqrt lam)⁻¹ : ℝ) • q) a -
          ResponseJ U (Real.sqrt lam • p) 0 a -
          ResponseJ U 0 (((Real.sqrt lam)⁻¹ : ℝ) • q) a +
          vecDot (Real.sqrt lam • p) (((Real.sqrt lam)⁻¹ : ℝ) • q) := by
        rw [hpq, hp0, h0q]
        congr 1
        simp [vecDot_smul_left, vecDot_smul_right, hsqrt]
    _ = vecDot (((Real.sqrt lam)⁻¹ : ℝ) • q)
          (matVecMul sigmaStar⁻¹ (matVecMul kappa (Real.sqrt lam • p))) := by
        exact hK (Real.sqrt lam • p) (((Real.sqrt lam)⁻¹ : ℝ) • q)
    _ = vecDot q (matVecMul (sigmaStar⁻¹ * kappa) p) := by
        rw [matVecMul_smul, matVecMul_smul, matVecMul_mul, vecDot_smul_left, vecDot_smul_right]
        field_simp [hsqrt]

theorem sigmaStarInvKappaCoarse_homogeneous_coeffField_of_isKappaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa) {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarInvKappaCoarse U (lam • a) = sigmaStarInvKappaCoarse U a := by
  calc
    sigmaStarInvKappaCoarse U (lam • a) = sigmaStar⁻¹ * kappa := by
      symm
      exact eq_sigmaStarInvKappaCoarse_of_isSigmaStarInvKappaCoarse
        (isSigmaStarInvKappaCoarse_homogeneous_coeffField U a hK hlam)
    _ = sigmaStarInvKappaCoarse U a := by
      rw [sigmaStarInvKappaCoarse_eq_mul_of_isKappaCoarse hK]

/-- Note-facing homogeneity for `\sigma_*^{-1}(U; a)\kappa(U; a)` under
coefficient rescaling. -/
theorem sigmaStarInvKappaCoarse_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa) {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarInvKappaCoarse U (lam • a) = sigmaStarInvKappaCoarse U a :=
  sigmaStarInvKappaCoarse_homogeneous_coeffField_of_isKappaCoarse U a hK hlam

theorem isSigmaStarCoarse_homogeneous_coeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    IsSigmaStarCoarse U (lam • a) (lam • sigmaStar) := by
  have hInv :=
    isSigmaStarInvCoarse_homogeneous_coeffField U a hS hlam
  have hsymm : sigmaStar.IsSymm := hS.1
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff] at hsymm ⊢
    intro i j
    show lam * sigmaStar j i = lam * sigmaStar i j
    rw [hsymm j i]
  · intro q
    calc
      ResponseJ U 0 q (lam • a) =
          (1 / 2 : ℝ) * vecDot q (matVecMul (lam⁻¹ • sigmaStar⁻¹) q) := by
            exact hInv.2 q
      _ = (1 / 2 : ℝ) * vecDot q (matVecMul ((lam • sigmaStar)⁻¹) q) := by
            rw [nonsing_inv_smul lam hlam.ne' hdet]

theorem sigmaStarCoarse_homogeneous_coeffField_of_isSigmaStarCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarCoarse U (lam • a) = lam • sigmaStarCoarse U a := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS' hdet',
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet]

/-- Note-facing homogeneity for `\sigma_*(U; a)` under coefficient
rescaling. -/
theorem sigmaStarCoarse_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    sigmaStarCoarse U (lam • a) = lam • sigmaStarCoarse U a :=
  sigmaStarCoarse_homogeneous_coeffField_of_isSigmaStarCoarse U a hS hdet hlam

theorem isKappaCoarse_homogeneous_coeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hK : IsKappaCoarse U a sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    IsKappaCoarse U (lam • a) (lam • sigmaStar) (lam • kappa) := by
  intro p q
  calc
    ResponseJ U p q (lam • a) - ResponseJ U p 0 (lam • a) - ResponseJ U 0 q (lam • a) +
        vecDot p q =
      vecDot q (matVecMul (sigmaStar⁻¹ * kappa) p) := by
        exact (isSigmaStarInvKappaCoarse_homogeneous_coeffField U a hK hlam) p q
    _ = vecDot q (matVecMul ((lam • sigmaStar)⁻¹) (matVecMul (lam • kappa) p)) := by
        rw [nonsing_inv_smul lam hlam.ne' hdet, matVecMul_mul]
        congr 1
        rw [smul_mul_assoc, mul_smul_comm]
        simp [smul_smul, inv_mul_cancel₀ hlam.ne']

theorem kappaCoarse_homogeneous_coeffField_of_isKappaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) {lam : ℝ} (hlam : 0 < lam) :
    kappaCoarse U (lam • a) = lam • kappaCoarse U a := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [eq_kappaCoarse_of_isKappaCoarse hS' hK' hdet',
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet]

/-- Note-facing homogeneity for `\kappa(U; a)` under coefficient rescaling. -/
theorem kappaCoarse_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) {lam : ℝ} (hlam : 0 < lam) :
    kappaCoarse U (lam • a) = lam • kappaCoarse U a :=
  kappaCoarse_homogeneous_coeffField_of_isKappaCoarse U a hS hK hdet hlam

theorem isSigmaCoarse_homogeneous_coeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    IsSigmaCoarse U (lam • a) (lam • sigma) (lam • sigmaStar) (lam • kappa) := by
  rcases hSigma with ⟨hsymm, hresp⟩
  have hsqrt : (Real.sqrt lam) ≠ 0 := Real.sqrt_ne_zero'.mpr hlam
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff] at hsymm ⊢
    intro i j
    show lam * sigma j i = lam * sigma i j
    rw [hsymm j i]
  · intro p
    have hp0 :
        ResponseJ U p 0 (lam • a) = ResponseJ U (Real.sqrt lam • p) 0 a := by
      simpa using responseJ_homogeneous_coeffField U p 0 a hlam
    have hsq : Real.sqrt lam * Real.sqrt lam = lam := by
      nlinarith [Real.sq_sqrt (le_of_lt hlam)]
    have hcorr :
        vecDot p
            (matVecMul (matTranspose (lam • kappa))
              (matVecMul ((lam • sigmaStar)⁻¹) (matVecMul (lam • kappa) p))) =
          vecDot (Real.sqrt lam • p)
            (matVecMul (matTranspose kappa)
              (matVecMul sigmaStar⁻¹ (matVecMul kappa (Real.sqrt lam • p)))) := by
      rw [vecDot_matVecMul_transpose, vecDot_matVecMul_transpose,
        nonsing_inv_smul lam hlam.ne' hdet]
      simp [smul_matVecMul, matVecMul_smul, vecDot_smul_left, vecDot_smul_right,
        hsq, hlam.ne', mul_left_comm, mul_comm]
    calc
      ResponseJ U p 0 (lam • a) -
          (1 / 2 : ℝ) *
            vecDot p
              (matVecMul (matTranspose (lam • kappa))
                (matVecMul ((lam • sigmaStar)⁻¹) (matVecMul (lam • kappa) p))) =
        ResponseJ U (Real.sqrt lam • p) 0 a -
          (1 / 2 : ℝ) *
            vecDot (Real.sqrt lam • p)
              (matVecMul (matTranspose kappa)
                (matVecMul sigmaStar⁻¹ (matVecMul kappa (Real.sqrt lam • p)))) := by
          rw [hp0, hcorr]
      _ = (1 / 2 : ℝ) * vecDot (Real.sqrt lam • p) (matVecMul sigma (Real.sqrt lam • p)) := by
          exact hresp (Real.sqrt lam • p)
      _ = (1 / 2 : ℝ) * vecDot p (matVecMul (lam • sigma) p) := by
          calc
            (1 / 2 : ℝ) * vecDot (Real.sqrt lam • p) (matVecMul sigma (Real.sqrt lam • p)) =
                (1 / 2 : ℝ) * (Real.sqrt lam * (Real.sqrt lam * vecDot p (matVecMul sigma p))) := by
                  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
            _ = (1 / 2 : ℝ) * (lam * vecDot p (matVecMul sigma p)) := by
                  congr 1
                  rw [← mul_assoc, hsq]
            _ = (1 / 2 : ℝ) * vecDot p (matVecMul (lam • sigma) p) := by
                  rw [smul_matVecMul, vecDot_smul_right]

theorem sigmaCoarse_homogeneous_coeffField_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    sigmaCoarse U (lam • a) = lam • sigmaCoarse U a := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hSigma' := isSigmaCoarse_homogeneous_coeffField U a hSigma hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS' hK' hSigma' hdet',
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet]

/-- Note-facing homogeneity for `\sigma(U; a)` under coefficient rescaling. -/
theorem sigmaCoarse_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    sigmaCoarse U (lam • a) = lam • sigmaCoarse U a :=
  sigmaCoarse_homogeneous_coeffField_of_isSigmaCoarse U a hS hK hSigma hdet hlam

/-- Bundled note-facing homogeneity for the deterministic coarse matrices
`σ(U; a)`, `σ_*(U; a)`, and `κ(U; a)` under coefficient rescaling. -/
theorem cg_matrices_homogeneous_coeffField {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    sigmaCoarse U (lam • a) = lam • sigmaCoarse U a ∧
      sigmaStarCoarse U (lam • a) = lam • sigmaStarCoarse U a ∧
      kappaCoarse U (lam • a) = lam • kappaCoarse U a := by
  refine ⟨?_, ?_, ?_⟩
  · exact sigmaCoarse_homogeneous_coeffField U a hS hK hSigma hdet hlam
  · exact sigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  · exact kappaCoarse_homogeneous_coeffField U a hS hK hdet hlam

theorem deterministicCoarseBlockMatrix_upperLeft_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicCoarseBlockMatrix U (lam • a)).upperLeft =
      lam • (deterministicCoarseBlockMatrix U a).upperLeft := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hSigma' := isSigmaCoarse_homogeneous_coeffField U a hSigma hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS' hK' hSigma' hdet',
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]
  exact blockMatrixOfDeterministicData_upperLeft_smul hdet hlam

theorem deterministicCoarseBlockMatrix_upperRight_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicCoarseBlockMatrix U (lam • a)).upperRight =
      (deterministicCoarseBlockMatrix U a).upperRight := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hSigma' := isSigmaCoarse_homogeneous_coeffField U a hSigma hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS' hK' hSigma' hdet',
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]
  exact blockMatrixOfDeterministicData_upperRight_smul hdet hlam

theorem deterministicCoarseBlockMatrix_lowerLeft_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicCoarseBlockMatrix U (lam • a)).lowerLeft =
      (deterministicCoarseBlockMatrix U a).lowerLeft := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hSigma' := isSigmaCoarse_homogeneous_coeffField U a hSigma hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS' hK' hSigma' hdet',
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]
  exact blockMatrixOfDeterministicData_lowerLeft_smul hdet hlam

theorem deterministicCoarseBlockMatrix_lowerRight_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicCoarseBlockMatrix U (lam • a)).lowerRight =
      lam⁻¹ • (deterministicCoarseBlockMatrix U a).lowerRight := by
  have hS' := isSigmaStarCoarse_homogeneous_coeffField U a hS hdet hlam
  have hK' := isKappaCoarse_homogeneous_coeffField U a hK hdet hlam
  have hSigma' := isSigmaCoarse_homogeneous_coeffField U a hSigma hdet hlam
  have hdet' : IsUnit (lam • sigmaStar).det := isUnit_det_smul hdet hlam.ne'
  rw [deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS' hK' hSigma' hdet',
    deterministicCoarseBlockMatrix_eq_blockMatrixOfDeterministicData_of_isSigmaCoarse
      hS hK hSigma hdet]
  exact blockMatrixOfDeterministicData_lowerRight_smul hdet hlam

theorem deterministicStarredBlockMatrixInv_upperLeft_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicStarredBlockMatrixInv U (lam • a)).upperLeft =
      lam⁻¹ • (deterministicStarredBlockMatrixInv U a).upperLeft := by
  simpa [deterministicStarredBlockMatrixInv] using
    deterministicCoarseBlockMatrix_lowerRight_homogeneous_coeffField_of_isSigmaCoarse
      U a hS hK hSigma hdet hlam

theorem deterministicStarredBlockMatrixInv_upperRight_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicStarredBlockMatrixInv U (lam • a)).upperRight =
      (deterministicStarredBlockMatrixInv U a).upperRight := by
  simpa [deterministicStarredBlockMatrixInv] using
    deterministicCoarseBlockMatrix_lowerLeft_homogeneous_coeffField_of_isSigmaCoarse
      U a hS hK hSigma hdet hlam

theorem deterministicStarredBlockMatrixInv_lowerLeft_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicStarredBlockMatrixInv U (lam • a)).lowerLeft =
      (deterministicStarredBlockMatrixInv U a).lowerLeft := by
  simpa [deterministicStarredBlockMatrixInv] using
    deterministicCoarseBlockMatrix_upperRight_homogeneous_coeffField_of_isSigmaCoarse
      U a hS hK hSigma hdet hlam

theorem deterministicStarredBlockMatrixInv_lowerRight_homogeneous_coeffField_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) (hdet : IsUnit sigmaStar.det)
    {lam : ℝ} (hlam : 0 < lam) :
    (deterministicStarredBlockMatrixInv U (lam • a)).lowerRight =
      lam • (deterministicStarredBlockMatrixInv U a).lowerRight := by
  simpa [deterministicStarredBlockMatrixInv] using
    deterministicCoarseBlockMatrix_upperLeft_homogeneous_coeffField_of_isSigmaCoarse
      U a hS hK hSigma hdet hlam


end

end Homogenization
