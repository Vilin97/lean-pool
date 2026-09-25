/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Dirichlet
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Neumann
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.SymmetricDirichletNeumann.ZeroDim

/-! # Theory -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Symmetric Dirichlet-Neumann Theory Assembly

This file is split mechanically out of `Internal.Ch02.SymmetricDirichletNeumann`.
-/

theorem responseSymmetricDirichletNeumannTheory_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hsym : CoeffOn.IsSymmetric a)
    (ha : IsSymmetricCoeffField a.toCoeffField)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseSymmetricDirichletNeumannTheory U a hsym := by
  let Uset : Set (Vec d) := (U : Set (Vec d))
  let hvol : 0 < (MeasureTheory.volume Uset).toReal := domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := Uset) U.isDomain hEll hvol with
    ⟨R, sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hdet : IsUnit (Homogenization.sigmaStarCoarse Uset a.toCoeffField).det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := Uset) (a := a.toCoeffField) R U.isDomain hEll hvol compat hS
  let hInt : ResponseLinearIntegrabilityData Uset a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rcases ScalarCanonicalMaximizer.GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := Uset) (a := a.toCoeffField) U.nonempty U.isDomain hEll with
    ⟨basisGrad⟩
  rcases ScalarCanonicalMaximizer.FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := Uset) (a := a.toCoeffField) U.nonempty U.isDomain hEll with
    ⟨basisFlux⟩
  have hDirValue :
      ∀ p : Vec d,
        symmetricDirichletNu U a p =
          (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) := by
    intro p
    rcases exists_isAffineDirichletSolution_of_isEllipticFieldOn U a hEll p with
      ⟨uD, huD⟩
    have hmin : IsSymmetricDirichletMinimizer U a p uD :=
      isSymmetricDirichletMinimizer_of_isAffineDirichletSolution U a huD ha hEll
    have hnu := symmetricDirichletNu_eq_of_minimizer hmin
    have hOld :=
      huD.energy_eq_vecDot_sigmaCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn
        ha hEll hA hS hK hSigma hdet
    have hPublicEnergy :
        symmetricDirichletEnergyValue U a uD =
          (1 / 2 : ℝ) *
            volumeAverage Uset
              (scalarVariationEnergyIntegrand a.toCoeffField
                huD.toAHarmonicFunction) := by
      calc
        symmetricDirichletEnergyValue U a uD =
            volumeAverage Uset
              ((1 / 2 : ℝ) •
                scalarVariationEnergyIntegrand a.toCoeffField
                  huD.toAHarmonicFunction) := by
              change
                volumeAverage Uset
                    (fun x =>
                      (1 / 2 : ℝ) *
                        vecDot (uD.grad x)
                          (matVecMul (a.toCoeffField x) (uD.grad x))) =
                  volumeAverage Uset
                    ((1 / 2 : ℝ) •
                      scalarVariationEnergyIntegrand a.toCoeffField
                        huD.toAHarmonicFunction)
              congr 1
              funext x
              simp [scalarVariationEnergyIntegrand,
                symmPart_eq_self_of_isSymmetricCoeffField ha x]
        _ =
            (1 / 2 : ℝ) *
              volumeAverage Uset
                (scalarVariationEnergyIntegrand a.toCoeffField
                  huD.toAHarmonicFunction) :=
              volumeAverage_smul Uset (1 / 2 : ℝ)
                (scalarVariationEnergyIntegrand a.toCoeffField
                  huD.toAHarmonicFunction)
    rw [hnu, hPublicEnergy, hOld]
  have hNeuValue :
      ∀ q : Vec d,
        symmetricNeumannNu U a q =
          (1 / 2 : ℝ) *
            vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
    intro q
    rcases exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn U a hEll q with
      ⟨uN, huN⟩
    have hmax : IsSymmetricNeumannMaximizer U a q uN.toH1Function :=
      isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution U a huN ha hEll
    have hnu := symmetricNeumannNu_eq_of_maximizer hmax
    have hHalf :=
      symmetricNeumannEnergyValue_eq_half_variationEnergy_of_isConstantFluxNeumannSolution
        U a huN hEll
    have hOld :=
      huN.energy_eq_vecDot_sigmaStarInvCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn
        ha hEll hS
    rw [hnu, hHalf, hOld]
  refine
    { dirichlet_minimizer_exists := ?_
      neumann_meanZero_maximizer_exists := ?_
      response_maximizer_split := ?_
      response_dirichlet_neumann_split := ?_
      dirichlet_value_by_sigma := hDirValue
      neumann_value_by_sigmaStarInv := hNeuValue
      kappa_eq_zero := ?_
      dirichlet_average_gradient := ?_
      dirichlet_average_flux := ?_
      neumann_average_flux := ?_
      neumann_average_gradient := ?_
      response_completed_square := ?_
      derived_matrices := ?_
      dirichlet_neumann_bracketing := ?_ }
  · intro p
    rcases exists_isAffineDirichletSolution_of_isEllipticFieldOn U a hEll p with
      ⟨uD, huD⟩
    exact ⟨uD, isSymmetricDirichletMinimizer_of_isAffineDirichletSolution U a huD ha hEll⟩
  · intro q
    rcases exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn U a hEll q with
      ⟨uN, huN⟩
    exact
      ⟨uN.toH1Function, meanZeroOn_of_h1MeanZeroFunction uN,
        isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution U a huN ha hEll⟩
  · intro p q v hv uD uN huD huN
    rcases exists_isAffineDirichletSolution_of_isEllipticFieldOn U a hEll p with
      ⟨uD0, huD0⟩
    rcases exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn U a hEll q with
      ⟨uN0, huN0⟩
    let v0 : Solution U a :=
      dirichletNeumannSplitOfIsEllipticFieldOn hEll huD0 huN0
    have hv0Old :
        Homogenization.IsResponseMaximizer Uset p q a.toCoeffField v0 :=
      isResponseMaximizer_dirichletNeumannSplitOfIsEllipticFieldOn_of_isSymmetricCoeffField
        hEll huD0 huN0 ha
    have hv0 : Book.Ch02.IsResponseMaximizer U a p q v0 := by
      intro w
      exact hv0Old w
    have hvAE :
        v.toH1.grad =ᵐ[volumeMeasureOn Uset] v0.toH1.grad :=
      (responseGradientUniquenessTheory_of_isEllipticFieldOn U a hEll).unique_gradient
        p q v v0 hv hv0
    have hDAE :
        uD.grad =ᵐ[volumeMeasureOn Uset] uD0.grad :=
      sameGradientAE_of_isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
        U a huD0 ha hEll huD
    have hNAE :
        uN.grad =ᵐ[volumeMeasureOn Uset] uN0.toH1Function.grad :=
      sameGradientAE_of_isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution
        U a huN0 ha hEll huN
    filter_upwards [hvAE, hDAE, hNAE] with x hvx hDx hNx
    have hv0x :
        v0.toH1.grad x = uN0.toH1Function.grad x - uD0.grad x := by
      change
        (dirichletNeumannSplitOfIsEllipticFieldOn hEll huD0 huN0).toH1.grad x =
          uN0.toH1Function.grad x - uD0.grad x
      exact congrFun (dirichletNeumannSplitOfIsEllipticFieldOn_grad hEll huD0 huN0) x
    rw [hvx, hv0x, ← hNx, ← hDx]
  · intro p q
    have hOld :=
      responseJ_eq_half_vecDot_sigmaCoarse_add_half_vecDot_sigmaStarInvCoarse_sub_dot_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := Uset) (a := a.toCoeffField) R U.isDomain ha hEll hvol compat
        hA hS hK hSigma p q
    rw [book_responseJ_eq_ResponseJ U a p q, hOld, hDirValue p, hNeuValue q]
  · simpa [book_kappaCoarse_eq_kappaCoarse U a] using
      kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
  · intro p uD huD
    rcases exists_isAffineDirichletSolution_of_isEllipticFieldOn U a hEll p with
      ⟨uD0, huD0⟩
    have hAE :=
      sameGradientAE_of_isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
        U a huD0 ha hEll huD
    calc
      h1AverageGradient U uD = h1AverageGradient U uD0 :=
        h1AverageGradient_eq_of_grad_ae U hAE
      _ = p := by
        simpa [h1AverageGradient, averageVec] using!
          huD0.averageGradient_eq (hvol.ne')
  · intro p uD huD
    rcases exists_isAffineDirichletSolution_of_isEllipticFieldOn U a hEll p with
      ⟨uD0, huD0⟩
    have hAE :=
      sameGradientAE_of_isSymmetricDirichletMinimizer_of_isAffineDirichletSolution
        U a huD0 ha hEll huD
    have hOld :=
      huD0.averageFlux_eq_sigmaCoarse_mul_of_isSymmetricCoeffField_of_isEllipticFieldOn
        ha hEll hA hS hK hSigma hdet hInt basisFlux.flux
    calc
      h1AverageFlux U a uD = h1AverageFlux U a uD0 :=
        h1AverageFlux_eq_of_grad_ae U a hAE
      _ = matVecMul (sigmaCoarse U a) p := by
        simpa [h1AverageFlux, averageVec, book_sigmaCoarse_eq_sigmaCoarse U a] using! hOld
  · intro q uN huN
    rcases exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn U a hEll q with
      ⟨uN0, huN0⟩
    have hAE :=
      sameGradientAE_of_isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution
        U a huN0 ha hEll huN
    have hOld :=
      huN0.averageFlux_eq hEll U.isDomain.isSobolevRegularDomain hvol.ne'
    calc
      h1AverageFlux U a uN = h1AverageFlux U a uN0.toH1Function :=
        h1AverageFlux_eq_of_grad_ae U a hAE
      _ = q := by
        simpa [h1AverageFlux, averageVec] using! hOld
  · intro q uN huN
    rcases exists_isConstantFluxNeumannSolution_of_isEllipticFieldOn U a hEll q with
      ⟨uN0, huN0⟩
    have hAE :=
      sameGradientAE_of_isSymmetricNeumannMaximizer_of_isConstantFluxNeumannSolution
        U a huN0 ha hEll huN
    have hOld :=
      huN0.averageGradient_eq_sigmaStarInvCoarse_mul_of_isSymmetricCoeffField_of_isEllipticFieldOn
        ha hEll hA hS hK hdet hInt basisGrad.grad
    calc
      h1AverageGradient U uN = h1AverageGradient U uN0.toH1Function :=
        h1AverageGradient_eq_of_grad_ae U hAE
      _ = matVecMul (sigmaStarInvCoarse U a) q := by
        simpa [h1AverageGradient, averageVec,
          book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a] using! hOld
  · intro p q
    have hOld :=
      responseJ_completedSquare_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := Uset) (a := a.toCoeffField) R U.isDomain ha hEll hvol compat
        hA hS hK hSigma p q
    rw [book_responseJ_eq_ResponseJ U a p q, hOld,
      book_sigmaCoarse_eq_sigmaCoarse U a,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
      book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
      ← sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
      ← sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  · constructor
    · have hk : Book.Ch02.kappaCoarse U a = 0 := by
        simpa [book_kappaCoarse_eq_kappaCoarse U a] using
          kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
      simp [Book.Ch02.aCoarse, Book.Ch02.CoarseMatrices.coeff,
        Book.Ch02.coarseMatrices, hk, matTranspose]
    constructor
    · have hk : Book.Ch02.kappaCoarse U a = 0 := by
        simpa [book_kappaCoarse_eq_kappaCoarse U a] using
          kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
      simp [Book.Ch02.aStarCoarse, hk, matTranspose]
    · have hk : Book.Ch02.kappaCoarse U a = 0 := by
        simpa [book_kappaCoarse_eq_kappaCoarse U a] using
          kappaCoarse_eq_zero_of_isSymmetricCoeffField_of_isCoarseBlockMatrix ha hA
      simp [Book.Ch02.bCoarse, Book.Ch02.CoarseMatrices.b,
        Book.Ch02.coarseMatrices, hk, matTranspose]
  · constructor
    · have h :=
        harmonicMeanCoeffField_le_sigmaStarCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
          (U := Uset) (a := a.toCoeffField) R U.isDomain ha hEll hvol compat
      simpa [book_averagedSymmPartInv_eq_averagedSymmPartInv U a,
        averagedSymmPartInv_eq_volumeAverageMat_inv_of_isSymmetricCoeffField ha,
        book_sigmaStarCoarse_eq_sigmaStarCoarse U a] using h
    constructor
    · have h :=
        sigmaStarCoarse_le_sigmaCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
          (U := Uset) (a := a.toCoeffField) R U.isDomain ha hEll hvol compat
          hA hS hK hSigma
      simpa [book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
        book_sigmaCoarse_eq_sigmaCoarse U a] using h
    · have h :=
        sigmaCoarse_le_volumeAverageMat_of_isSymmetricCoeffField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
          (U := Uset) (a := a.toCoeffField) R U.isDomain ha hEll hvol compat
          hA hS hK hSigma
      simpa [book_sigmaCoarse_eq_sigmaCoarse U a, averageMat] using! h

theorem responseSymmetricDirichletNeumannTheory_of_neZero
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hsym : CoeffOn.IsSymmetric a) :
    ResponseSymmetricDirichletNeumannTheory U a hsym := by
  let b : CoeffOn U := pointwiseSymmetricCoeffOn U a hsym
  have hsymb : CoeffOn.IsSymmetric b := by
    exact Filter.Eventually.of_forall fun x =>
      pointwiseSymmetricCoeffOn_isSymmetricCoeffField U a hsym x
  have hb : ResponseSymmetricDirichletNeumannTheory U b hsymb :=
    responseSymmetricDirichletNeumannTheory_of_isEllipticFieldOn U b hsymb
      (by simpa [b] using pointwiseSymmetricCoeffOn_isSymmetricCoeffField U a hsym)
      (by simpa [b] using pointwiseSymmetricCoeffOn_isEllipticFieldOn U a hsym)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseSymmetricCoeffOn_ae_eq U a hsym
  exact ResponseSymmetricDirichletNeumannTheory.ofAEEq hba hb

theorem responseSymmetricDirichletNeumannTheory
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (hsym : CoeffOn.IsSymmetric a) :
    ResponseSymmetricDirichletNeumannTheory U a hsym := by
  by_cases hd : d = 0
  · subst d
    exact responseSymmetricDirichletNeumannTheory_zero_dim U a hsym
  · let : NeZero d := ⟨hd⟩
    exact responseSymmetricDirichletNeumannTheory_of_neZero U a hsym


end BookCh02

end

end Ch02
end Internal
end Homogenization
