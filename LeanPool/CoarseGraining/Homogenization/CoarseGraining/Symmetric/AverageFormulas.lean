/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CanonicalFormulas
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Symmetric.Response

/-! # Average Formulas -/

namespace Homogenization

noncomputable section

/-!
# Average formulas for symmetric coefficient fields

For symmetric coefficient fields, the canonical average-gradient and
average-flux formulas split into pure Dirichlet and Neumann response pieces.
The scalar maximizer for `(p, 0)` corresponds to the negative of the affine
Dirichlet solution, which accounts for the signs in the pure-gradient formulas.
-/

namespace ScalarCanonicalMaximizer

private theorem zero_matVecMul {d : ℕ} (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

theorem averageGradientFormulaCanonical_p_zero_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {p : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U p 0 a)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U
      (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) = -p := by
  have hAvg :=
    ScalarCanonicalMaximizer.averageGradientFormulaCanonical
      (v := v) hS hK hdet hInt vGrad
  have hk : kappaCoarse U a = 0 :=
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  rw [hAvg, hk]
  simp [zero_matVecMul, matVecMul_zero]

theorem averageFluxFormulaCanonical_p_zero_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {p : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U p 0 a)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      -matVecMul (sigmaCoarse U a) p := by
  have hAvg :=
    ScalarCanonicalMaximizer.averageFluxFormulaCanonical
      (v := v) hS hK hSigma hdet hInt vFlux
  have hk : kappaCoarse U a = 0 :=
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  have hb :
      bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a) =
        sigmaCoarse U a :=
    bCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix
      ha hA
  rw [hAvg, hb, hk]
  simp [matTranspose, matVecMul_zero]

theorem averageGradientFormulaCanonical_zero_q_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U 0 q a)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U
      (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      matVecMul (sigmaStarInvCoarse U a) q := by
  have hAvg :=
    ScalarCanonicalMaximizer.averageGradientFormulaCanonical
      (v := v) hS hK hdet hInt vGrad
  have hk : kappaCoarse U a = 0 :=
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  rw [hAvg, hk]
  simp [zero_matVecMul]

theorem averageFluxFormulaCanonical_zero_q_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} {q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U 0 q a)
    (ha : IsSymmetricCoeffField a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) = q := by
  have hAvg :=
    ScalarCanonicalMaximizer.averageFluxFormulaCanonical
      (v := v) hS hK hSigma hdet hInt vFlux
  have hk : kappaCoarse U a = 0 :=
    kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  rw [hAvg, hk]
  simp [matTranspose, zero_matVecMul, matVecMul_zero]

end ScalarCanonicalMaximizer

end

end Homogenization
