/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence

/-! # Convex Average Formulas -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
Convex-domain wrappers for average formulas that discharge basis-data packages
using the bounded-open-convex existence theorems.
-/

namespace ScalarCanonicalMaximizer

theorem averageGradientOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    (v : ScalarCanonicalMaximizer U p q a) (hne : Set.Nonempty U)
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      fun i => ResponseJ U p q a + ResponseJ U 0 (Pi.single i 1) a -
        ResponseJ U p (q - Pi.single i 1) a := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageGradientOfBasisDataOfIsEllipticFieldOn v hEll basis

theorem averageFluxOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    (v : ScalarCanonicalMaximizer U p q a) (hne : Set.Nonempty U)
    (hU : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      fun i => ResponseJ U (p - Pi.single i 1) q a -
        ResponseJ U p q a - ResponseJ U (Pi.single i 1) 0 a := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageFluxOfBasisDataOfIsEllipticFieldOn v hEll basis

theorem averageGradientFormulaOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul sigmaStar⁻¹ (q + matVecMul kappa p) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageGradientFormulaOfBasisData v hS hK
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormulaOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose kappa) (matVecMul sigmaStar⁻¹ q) -
        matVecMul (bCoarse sigma sigmaStar kappa) p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageFluxFormulaOfBasisData v hS hK hSigma
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormulaCanonicalOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (sigmaStarInvCoarse U a) (q + matVecMul (kappaCoarse U a) p) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageGradientFormulaCanonicalOfBasisData v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageFluxFormulaCanonicalOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q - matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) q) -
        matVecMul (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)) p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageFluxFormulaCanonicalOfBasisData v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem
    averageGradientFormulaDeterministicCoarseBlockMatrixOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (deterministicCoarseBlockMatrix U a).lowerRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).lowerLeft p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageGradientFormulaDeterministicCoarseBlockMatrixOfBasisData v hS hK hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem
    averageFluxFormulaDeterministicCoarseBlockMatrixOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (deterministicCoarseBlockMatrix U a).upperRight q -
        matVecMul (deterministicCoarseBlockMatrix U a).upperLeft p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageFluxFormulaDeterministicCoarseBlockMatrixOfBasisData v hS hK hSigma hdet
    (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) basis

theorem averageGradientFormulaCoarseBlockMatrixOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U (fun x => (v : AHarmonicFunction a U).toH1.grad x i)) =
      -p + matVecMul (coarseBlockMatrix U a).lowerRight q -
        matVecMul (coarseBlockMatrix U a).lowerLeft p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageGradientFormulaCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    v hEll hA hS hK hdet basis

theorem averageFluxFormulaCoarseBlockMatrixOfIsEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {p q : Vec d} {a : CoeffField d} {lam Lam : ℝ}
    {sigma sigmaStar kappa : Mat d} (v : ScalarCanonicalMaximizer U p q a)
    (hne : Set.Nonempty U) (hU : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar) (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (fun i => volumeAverage U
      (fun x => matVecMul (a x) ((v : AHarmonicFunction a U).toH1.grad x) i)) =
      q + matVecMul (coarseBlockMatrix U a).upperRight q -
        matVecMul (coarseBlockMatrix U a).upperLeft p := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  rcases FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := U) (a := a) hne hU hEll with ⟨basis⟩
  exact averageFluxFormulaCoarseBlockMatrixOfBasisDataOfIsEllipticFieldOn
    v hEll hA hS hK hSigma hdet basis

end ScalarCanonicalMaximizer

end

end Homogenization
