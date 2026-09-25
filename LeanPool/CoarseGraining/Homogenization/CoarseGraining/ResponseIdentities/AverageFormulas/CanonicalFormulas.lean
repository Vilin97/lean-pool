/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CanonicalBasic

/-! # Canonical Formulas -/

@[expose] public section

namespace Homogenization

noncomputable section

open Pointwise

namespace ScalarCanonicalMaximizer

/-!
# Average formulas (part 4) -- ScalarCanonicalMaximizer average formulas

averageGradient / averageFlux (plain and canonical) and their formula
variants (generic, canonical, deterministicCoarseBlockMatrix,
coarseBlockMatrix) inside the ScalarCanonicalMaximizer namespace.
-/

theorem averageGradient {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a := by
  exact basic_cg_identities_average_gradient_of_isResponseMaximizer
    U a p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vGrad i : AHarmonicFunction a U))
    (fun i => (vGrad i).isResponseMaximizer)

theorem averageGradientOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a :=
  averageGradient v (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vGrad

theorem averageGradientOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a := by
  exact averageGradient v hInt basis.grad

theorem averageGradientOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a :=
  averageGradientOfBasisData v (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFlux {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a := by
  exact basic_cg_identities_average_flux_of_isResponseMaximizer
    U a p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vFlux i : AHarmonicFunction a U))
    (fun i => (vFlux i).isResponseMaximizer)

theorem averageFluxOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a :=
  averageFlux v (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vFlux

theorem averageFluxOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    (v : ScalarCanonicalMaximizer U p q a) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a := by
  exact averageFlux v hInt basis.flux

theorem averageFluxOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (v : ScalarCanonicalMaximizer U p q a) (hEll : IsEllipticFieldOn lam Lam U a)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a :=
  averageFluxOfBasisData v (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormula {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) := by
  exact basic_cg_identities_average_gradient_formula_of_isResponseMaximizer
    U a hS hK p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vGrad i : AHarmonicFunction a U))
    (fun i => (vGrad i).isResponseMaximizer)

theorem averageGradientFormulaOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) :=
  averageGradientFormula v hS hK
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vGrad

theorem averageGradientFormulaOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hInt : ResponseLinearIntegrabilityData U a) (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) := by
  exact averageGradientFormula v hS hK hInt basis.grad

theorem averageGradientFormulaOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) :=
  averageGradientFormulaOfBasisData v hS hK
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormula {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p := by
  exact basic_cg_identities_average_flux_formula_of_isResponseMaximizer
    U a hS hK hSigma p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vFlux i : AHarmonicFunction a U))
    (fun i => (vFlux i).isResponseMaximizer)

theorem averageFluxFormulaOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p :=
  averageFluxFormula v hS hK hSigma
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vFlux

theorem averageFluxFormulaOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hInt : ResponseLinearIntegrabilityData U a) (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p := by
  exact averageFluxFormula v hS hK hSigma hInt basis.flux

theorem averageFluxFormulaOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p :=
  averageFluxFormulaOfBasisData v hS hK hSigma
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormulaCanonical {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) := by
  exact basic_cg_identities_average_gradient_formula_canonical_of_isResponseMaximizer
    U a hS hK hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vGrad i : AHarmonicFunction a U))
    (fun i => (vGrad i).isResponseMaximizer)

theorem averageGradientFormulaCanonicalOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) :=
  averageGradientFormulaCanonical v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vGrad

theorem averageGradientFormulaCanonicalOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) := by
  exact averageGradientFormulaCanonical v hS hK hdet hInt basis.grad

theorem averageGradientFormulaCanonicalOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) :=
  averageGradientFormulaCanonicalOfBasisData v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormulaCanonical {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p := by
  exact basic_cg_identities_average_flux_formula_canonical_of_isResponseMaximizer
    U a hS hK hSigma hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vFlux i : AHarmonicFunction a U))
    (fun i => (vFlux i).isResponseMaximizer)

theorem averageFluxFormulaCanonicalOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p :=
  averageFluxFormulaCanonical v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vFlux

theorem averageFluxFormulaCanonicalOfBasisData {d : ℕ} {U : Set (Vec d)} {p q : Vec d}
    {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p := by
  exact averageFluxFormulaCanonical v hS hK hSigma hdet hInt basis.flux

theorem averageFluxFormulaCanonicalOfBasisDataOfIsEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p :=
  averageFluxFormulaCanonicalOfBasisData v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormulaDeterministicCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p := by
  exact basic_cg_identities_average_gradient_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    U a hS hK hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vGrad i : AHarmonicFunction a U))
    (fun i => (vGrad i).isResponseMaximizer)

theorem averageGradientFormulaDeterministicCoarseBlockMatrixOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p :=
  averageGradientFormulaDeterministicCoarseBlockMatrix v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vGrad

theorem averageGradientFormulaDeterministicCoarseBlockMatrixOfBasisData
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p := by
  exact averageGradientFormulaDeterministicCoarseBlockMatrix v hS hK hdet hInt basis.grad

theorem averageGradientFormulaDeterministicCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p :=
  averageGradientFormulaDeterministicCoarseBlockMatrixOfBasisData v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormulaDeterministicCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p := by
  exact basic_cg_identities_average_flux_formula_deterministicCoarseBlockMatrix_of_isResponseMaximizer
    U a hS hK hSigma hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vFlux i : AHarmonicFunction a U))
    (fun i => (vFlux i).isResponseMaximizer)

theorem averageFluxFormulaDeterministicCoarseBlockMatrixOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p :=
  averageFluxFormulaDeterministicCoarseBlockMatrix v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vFlux

theorem averageFluxFormulaDeterministicCoarseBlockMatrixOfBasisData
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p := by
  exact averageFluxFormulaDeterministicCoarseBlockMatrix v hS hK hSigma hdet hInt basis.flux

theorem averageFluxFormulaDeterministicCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p :=
  averageFluxFormulaDeterministicCoarseBlockMatrixOfBasisData v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormulaCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p := by
  exact basic_cg_identities_average_gradient_formula_coarseBlockMatrix_of_isResponseMaximizer
    U a hA hS hK hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vGrad i : AHarmonicFunction a U))
    (fun i => (vGrad i).isResponseMaximizer)

theorem averageGradientFormulaCoarseBlockMatrixOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vGrad : ∀ i : Fin d, ScalarCanonicalMaximizer U 0 (Pi.single i 1) a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p :=
  averageGradientFormulaCoarseBlockMatrix v hA hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vGrad

theorem averageGradientFormulaCoarseBlockMatrixOfBasisData
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p := by
  exact averageGradientFormulaCoarseBlockMatrix v hA hS hK hdet hInt basis.grad

theorem averageGradientFormulaCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : GradientBasisData U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p :=
  averageGradientFormulaCoarseBlockMatrixOfBasisData
    v hA hS hK hdet (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormulaCoarseBlockMatrix
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p := by
  exact basic_cg_identities_average_flux_formula_coarseBlockMatrix_of_isResponseMaximizer
    U a hA hS hK hSigma hdet p q hInt (v : AHarmonicFunction a U) v.isResponseMaximizer
    (fun i => (vFlux i : AHarmonicFunction a U))
    (fun i => (vFlux i).isResponseMaximizer)

theorem averageFluxFormulaCoarseBlockMatrixOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (vFlux : ∀ i : Fin d, ScalarCanonicalMaximizer U (Pi.single i 1) 0 a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p :=
  averageFluxFormulaCoarseBlockMatrix v hA hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) vFlux

theorem averageFluxFormulaCoarseBlockMatrixOfBasisData
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p := by
  exact averageFluxFormulaCoarseBlockMatrix v hA hS hK hSigma hdet hInt basis.flux

theorem averageFluxFormulaCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (basis : FluxBasisData U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p :=
  averageFluxFormulaCoarseBlockMatrixOfBasisData
    v hA hS hK hSigma hdet (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem energyAverageGradientCanonicalOfIsSigmaStarCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {sigmaStar : Mat d} (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det)
    (hInt : ResponseLinearIntegrabilityData U a) (w : AHarmonicFunction a U)
    (v : ScalarCanonicalMaximizer U 0
      (matVecMul (sigmaStarCoarse U a)
        (fun i => volumeAverage U (fun x => w.toH1.grad x i))) a) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => w.toH1.grad x i))
          (matVecMul (sigmaStarCoarse U a)
            (fun i => volumeAverage U (fun x => w.toH1.grad x i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  exact basic_cg_identities_energy_average_gradient_canonical_of_isSigmaStarCoarse
    U a hEll hS hdet hInt w (v : AHarmonicFunction a U) v.isResponseMaximizer

theorem energyAverageGradientCanonicalOfIsSigmaStarCoarseOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigmaStar : Mat d} (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a U)
    (v : ScalarCanonicalMaximizer U 0
      (matVecMul (sigmaStarCoarse U a)
        (fun i => volumeAverage U (fun x => w.toH1.grad x i))) a) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => w.toH1.grad x i))
          (matVecMul (sigmaStarCoarse U a)
            (fun i => volumeAverage U (fun x => w.toH1.grad x i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) :=
  energyAverageGradientCanonicalOfIsSigmaStarCoarse hEll hS hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w v

theorem energyAverageFluxCanonicalOfIsSigmaCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    {sigma sigmaStar kappa : Mat d} (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (hInt : ResponseLinearIntegrabilityData U a)
    (w : AHarmonicFunction a U)
    (v : ScalarCanonicalMaximizer U
      (-matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))
      0 a) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
            (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  exact basic_cg_identities_energy_average_flux_canonical_of_isSigmaCoarse
    U a hEll hS hK hSigma hdet hInt w (v : AHarmonicFunction a U) v.isResponseMaximizer

theorem energyAverageFluxCanonicalOfIsSigmaCoarseOfIsEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {sigma sigmaStar kappa : Mat d} (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a U)
    (v : ScalarCanonicalMaximizer U
      (-matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
        (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i)))
      0 a) :
    (1 / 2 : ℝ) *
        vecDot (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))
          (matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a))⁻¹
            (fun i => volumeAverage U (fun x => matVecMul (a x) (w.toH1.grad x) i))) ≤
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a w) :=
  energyAverageFluxCanonicalOfIsSigmaCoarse hEll hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w v


end ScalarCanonicalMaximizer

end

end Homogenization
