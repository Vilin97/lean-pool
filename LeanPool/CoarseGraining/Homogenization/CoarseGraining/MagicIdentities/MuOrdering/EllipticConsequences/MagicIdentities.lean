/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.OriginCube

/-! # Magic Identities -/

namespace Homogenization

noncomputable section

/-!
# MuOrdering -- adjoint flipFlux magic identity wrappers

`Mu (p, -q) (adjointCoeffField a) - vecDot p q` rewritten in
sigma, sigmaStar, kappa form, plus the shifted-square completion and the
canonical-coarse versions.
-/

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isSigmaCoarse {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
  calc
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
        Mu U (p, q) a - vecDot p q := by
      simpa [blockVecFlipFlux] using
        congrArg (fun m : ℝ => m - vecDot p q)
          (Mu_adjointCoeffField_flipFlux U (p, q) a)
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
      exact magic_identity_mu_sub_vecDot_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
        (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
          (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
  have hSInvSymm : (sigmaStar⁻¹).IsSymm :=
    (isSigmaStarInvCoarse_of_isSigmaStarCoarse hS).1
  calc
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) - vecDot p q := by
      exact magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul sigma p) - vecDot p q +
          (1 / 2 : ℝ) * vecDot (q - matVecMul kappa p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul kappa p)) := by
      ring
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) -
          (1 / 2 : ℝ) * vecDot p (matVecMul (kappa + matTranspose kappa) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStar + kappa) p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul (sigmaStar + kappa) p)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (magic_adjoint_shifted_square_eq_completed_square
          (sigma := sigma) (sigmaStar := sigmaStar) (kappa := kappa) hSInvSymm hdet p q)

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_canonical_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
        vecDot p q := by
  calc
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
        Mu U (p, q) a - vecDot p q := by
      simpa [blockVecFlipFlux] using
        congrArg (fun m : ℝ => m - vecDot p q)
          (Mu_adjointCoeffField_flipFlux U (p, q) a)
    _ =
        (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
          (1 / 2 : ℝ) * vecDot (q - matVecMul (kappaCoarse U a) p)
            (matVecMul (sigmaStarInvCoarse U a) (q - matVecMul (kappaCoarse U a) p)) -
          vecDot p q := by
      exact magic_identity_mu_sub_vecDot_canonical_of_isSigmaCoarse
        U a hA hS hK hSigma hdet p q

theorem magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_canonical_of_isSigmaCoarse
    {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (p q : Vec d) :
    Mu U (p, -q) (adjointCoeffField a) - vecDot p q =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) -
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (kappaCoarse U a + matTranspose (kappaCoarse U a)) p) +
        (1 / 2 : ℝ) * vecDot (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)
          (matVecMul (sigmaStarInvCoarse U a)
            (q - matVecMul (sigmaStarCoarse U a + kappaCoarse U a) p)) := by
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet,
    sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using
    magic_identity_mu_adjointCoeffField_flipFlux_sub_vecDot_shifted_square_of_isSigmaCoarse
      U a hA hS hK hSigma hdet p q

end

end Homogenization
