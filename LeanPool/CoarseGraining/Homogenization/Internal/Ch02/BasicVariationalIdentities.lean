/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BasicVariationalIdentitiesDefinitions
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Adapters
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.HarmonicMean
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.UpperLeftAverage
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaLeBCoarse
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarLeSigma
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CoarseFormulas
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence

/-! # Basic Variational Identities -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem matLoewnerLE_zero_dim {A B : Mat 0} :
    MatLoewnerLE A B := by
  intro p
  have hp : p = 0 := Subsingleton.elim p 0
  subst p
  simp [vecDot, matVecMul]

private theorem responseValue_zero_zero_zero_dim (U : Domain 0)
    (a : CoeffOn U) (w : Solution U a) :
    responseValue U a 0 0 w = 0 := by
  change
    average U (responseIntegrand U a (0 : Vec 0) (0 : Vec 0) w) = 0
  rw [show responseIntegrand U a (0 : Vec 0) (0 : Vec 0) w = 0 by
    funext x
    simp [responseIntegrand, vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

private theorem variationEnergyValue_zero_dim (U : Domain 0)
    (a : CoeffOn U) (w : Solution U a) :
    variationEnergyValue U a w = 0 := by
  change average U (variationEnergyIntegrand U a w) = 0
  rw [show variationEnergyIntegrand U a w = 0 by
    funext x
    simp [variationEnergyIntegrand, vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

private theorem secondVariationEnergyValue_zero_dim (U : Domain 0)
    (a : CoeffOn U) (v w : Solution U a) :
    secondVariationEnergyValue U a v w = 0 := by
  change
    average U
      (fun x =>
        (1 / 2 : ℝ) *
          vecDot (v.toH1.grad x - w.toH1.grad x)
            (matVecMul (symmPart (a.toCoeffField x))
              (v.toH1.grad x - w.toH1.grad x))) = 0
  rw [show
      (fun x =>
        (1 / 2 : ℝ) *
          vecDot (v.toH1.grad x - w.toH1.grad x)
            (matVecMul (symmPart (a.toCoeffField x))
              (v.toH1.grad x - w.toH1.grad x))) = (0 : Vec 0 → ℝ) by
    funext x
    simp [vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

private theorem responseJ_zero_zero_of_canonical_identities (U : Domain 0)
    (a : CoeffOn U) :
    responseJ U a 0 0 = 0 := by
  have hM : CanonicalResponseMatrixIdentities U a :=
    canonicalResponseMatrixIdentities U a
  have h := hM.sigmaStarInv_response (0 : Vec 0)
  simpa [vecDot, matVecMul] using h

private theorem responseBasicVariationalIdentitiesTheory_zero_dim
    (U : Domain 0) (a : CoeffOn U) :
    ResponseBasicVariationalIdentitiesTheory U a (coarseMatrices U a) := by
  have hJ00 : responseJ U a (0 : Vec 0) (0 : Vec 0) = 0 :=
    responseJ_zero_zero_of_canonical_identities U a
  refine
    { matrix_identities := canonicalResponseMatrixIdentities U a
      sigmaStar_symm := by
        simpa using sigmaStarCoarse_isSymm U a
      harmonicMean_le_sigmaStar := matLoewnerLE_zero_dim
      sigmaStar_le_sigma := matLoewnerLE_zero_dim
      sigma_le_b := matLoewnerLE_zero_dim
      b_le_averagedSymmPartPlusCorrection := matLoewnerLE_zero_dim
      second_variation := ?_
      maximizer_energy := ?_
      average_gradient := ?_
      average_flux := ?_ }
  · intro p q v _hv w
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    rw [hJ00, responseValue_zero_zero_zero_dim U a w,
      secondVariationEnergyValue_zero_dim U a v w]
    ring
  · intro p q v _hv
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    rw [hJ00, variationEnergyValue_zero_dim U a v]
    ring
  · intro p q v _hv
    exact Subsingleton.elim _ _
  · intro p q v _hv
    exact Subsingleton.elim _ _

theorem responseSecondVariation_eq_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) (w : Solution U a) :
    responseJ U a p q - responseValue U a p q w =
      secondVariationEnergyValue U a v w := by
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  let wdiff : Solution U a :=
    AHarmonicFunction.subOfIntegrable w v (hInt.weakFlux w) (hInt.weakFlux v)
  have hsec :=
    responseJ_second_variation_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField p q v hv wdiff
      (hInt.weakFlux v) (hInt.weakFlux wdiff)
      (hInt.response p q v) (hInt.firstVariation p q v wdiff)
      (hInt.energy wdiff)
  have hgradPert :
      (scalarPerturbation v wdiff 1 (hInt.weakFlux v)
          (hInt.weakFlux wdiff)).toH1.grad = w.toH1.grad := by
    dsimp [wdiff]
    rw [scalarPerturbation_grad, AHarmonicFunction.grad_subOfIntegrable]
    funext x
    simp [sub_eq_add_neg]
  have hresp :
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField p q
            (scalarPerturbation v wdiff 1 (hInt.weakFlux v)
              (hInt.weakFlux wdiff))) =
        responseValue U a p q w := by
    change
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField p q
            (scalarPerturbation v wdiff 1 (hInt.weakFlux v)
              (hInt.weakFlux wdiff))) =
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField p q w)
    exact congrArg (volumeAverage (U : Set (Vec d)))
      (scalarResponseIntegrand_eq_of_grad_eq hgradPert)
  have henergyFun :
      ((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a.toCoeffField wdiff) =
        fun x =>
          (1 / 2 : ℝ) *
            vecDot (v.toH1.grad x - w.toH1.grad x)
              (matVecMul (symmPart (a.toCoeffField x))
                (v.toH1.grad x - w.toH1.grad x)) := by
    funext x
    dsimp [wdiff, scalarVariationEnergyIntegrand]
    rw [AHarmonicFunction.grad_subOfIntegrable]
    simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
      vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
    ring
  have henergy :
      (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (scalarVariationEnergyIntegrand a.toCoeffField wdiff) =
        secondVariationEnergyValue U a v w := by
    calc
      (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (scalarVariationEnergyIntegrand a.toCoeffField wdiff)
          =
        volumeAverage (U : Set (Vec d))
          ((1 / 2 : ℝ) • scalarVariationEnergyIntegrand a.toCoeffField wdiff) := by
            rw [volumeAverage_smul]
      _ = secondVariationEnergyValue U a v w := by
            rw [henergyFun]
            rfl
  rw [hresp] at hsec
  rw [book_responseJ_eq_ResponseJ U a p q]
  nlinarith [hsec, henergy]

theorem responseJ_eq_energy_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    responseJ U a p q = (1 / 2 : ℝ) * variationEnergyValue U a v := by
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rw [book_responseJ_eq_ResponseJ U a p q]
  change
    ResponseJ (U : Set (Vec d)) p q a.toCoeffField =
      (1 / 2 : ℝ) *
        volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField v)
  exact
    responseJ_energy_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField p q v hv
      (hInt.weakFlux v) (hInt.response p q v)
      (hInt.firstVariation p q v v) (hInt.energy v)

theorem averageGradient_eq_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (hS : IsSigmaStarCoarse (U : Set (Vec d)) a.toCoeffField
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField))
    (hK : IsKappaCoarse (U : Set (Vec d)) a.toCoeffField
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField))
    (hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det)
    (p q : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    averageGradient U a v =
      -p + matVecMul (coarseMatrices U a).sigmaStarInv
        (q + matVecMul (coarseMatrices U a).kappa p) := by
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rcases ScalarCanonicalMaximizer.GradientBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) U.nonempty U.isDomain hEll with
    ⟨basis⟩
  have hold :=
    basic_cg_identities_average_gradient_formula_canonical_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField hS hK hdet p q hInt v hv
      (fun i => (basis.grad i : AHarmonicFunction a.toCoeffField (U : Set (Vec d))))
      (fun i => (basis.grad i).isResponseMaximizer)
  calc
    averageGradient U a v =
        (fun i => volumeAverage (U : Set (Vec d)) (fun x => v.toH1.grad x i)) := rfl
    _ =
        -p + matVecMul
          (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField)
            (q + matVecMul
              (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p) := hold
    _ =
        -p + matVecMul (coarseMatrices U a).sigmaStarInv
          (q + matVecMul (coarseMatrices U a).kappa p) := by
        rw [← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a,
          ← book_kappaCoarse_eq_kappaCoarse U a]
        rfl

theorem averageFlux_eq_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (hS : IsSigmaStarCoarse (U : Set (Vec d)) a.toCoeffField
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField))
    (hK : IsKappaCoarse (U : Set (Vec d)) a.toCoeffField
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField))
    {sigma : Mat d}
    (hSigma : IsSigmaCoarse (U : Set (Vec d)) a.toCoeffField
      sigma
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField))
    (hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det)
    (p q : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    averageFlux U a v =
      q - matVecMul (matTranspose (coarseMatrices U a).kappa)
          (matVecMul (coarseMatrices U a).sigmaStarInv q) -
        matVecMul (coarseMatrices U a).b p := by
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rcases ScalarCanonicalMaximizer.FluxBasisData.nonempty_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) U.nonempty U.isDomain hEll with
    ⟨basis⟩
  have hold :=
    basic_cg_identities_average_flux_formula_canonical_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField hS hK hSigma hdet p q hInt v hv
      (fun i => (basis.flux i : AHarmonicFunction a.toCoeffField (U : Set (Vec d))))
      (fun i => (basis.flux i).isResponseMaximizer)
  calc
    averageFlux U a v =
        (fun i => volumeAverage (U : Set (Vec d))
          (fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) i)) := rfl
    _ =
        q -
          matVecMul
            (matTranspose (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField))
            (matVecMul
              (Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField) q) -
          matVecMul
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
              (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
              (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) p := hold
    _ =
        q - matVecMul (matTranspose (coarseMatrices U a).kappa)
            (matVecMul (coarseMatrices U a).sigmaStarInv q) -
          matVecMul (coarseMatrices U a).b p := by
        rw [← book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse U a hS,
          ← book_kappaCoarse_eq_kappaCoarse U a,
          ← book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse U a]
        rfl

theorem responseBasicVariationalIdentitiesTheory_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseBasicVariationalIdentitiesTheory U a (coarseMatrices U a) := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨R, sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hdet : IsUnit (Homogenization.sigmaStarCoarse
      (U : Set (Vec d)) a.toCoeffField).det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol compat hS
  have hb :
      (coarseMatrices U a).b =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
    book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse U a hS
  refine
    { matrix_identities := canonicalResponseMatrixIdentities_of_isEllipticFieldOn U a hEll
      sigmaStar_symm := by
        simpa using sigmaStarCoarse_isSymm U a
      harmonicMean_le_sigmaStar := ?_
      sigmaStar_le_sigma := ?_
      sigma_le_b := ?_
      b_le_averagedSymmPartPlusCorrection := ?_
      second_variation := ?_
      maximizer_energy := ?_
      average_gradient := ?_
      average_flux := ?_ }
  · have h :=
      harmonicMeanSymmPart_le_sigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol compat
    simpa [book_averagedSymmPartInv_eq_averagedSymmPartInv U a,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a] using h
  · intro p
    have h :=
      sigmaStarCoarse_le_sigmaCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
        compat hA hS hK hSigma p
    change
      (1 / 2 : ℝ) *
          vecDot p (matVecMul (Book.Ch02.sigmaStarCoarse U a) p) ≤
        (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p)
    rw [book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
      book_sigmaCoarse_eq_sigmaCoarse U a]
    nlinarith
  · have h :=
      sigmaCoarse_le_bCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
        compat hS hK hSigma
    simpa [book_sigmaCoarse_eq_sigmaCoarse U a, hb] using h
  · have h :=
      bCoarse_le_averagedSymmPartPlusCorrection_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) R U.isDomain hEll hvol
        compat hA hS hK hSigma
    simpa [hb, book_averagedSymmPartPlusCorrection_eq_averagedSymmPartPlusCorrection U a]
      using h
  · intro p q v hv w
    exact responseSecondVariation_eq_of_isEllipticFieldOn U a hEll p q v hv w
  · intro p q v hv
    exact responseJ_eq_energy_of_isEllipticFieldOn U a hEll p q v hv
  · intro p q v hv
    exact averageGradient_eq_of_isEllipticFieldOn U a hEll hS hK hdet p q v hv
  · intro p q v hv
    exact averageFlux_eq_of_isEllipticFieldOn U a hEll hS hK hSigma hdet p q v hv

theorem responseBasicVariationalIdentitiesTheory_of_neZero
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U) :
    ResponseBasicVariationalIdentitiesTheory U a (coarseMatrices U a) := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hb :
      ResponseBasicVariationalIdentitiesTheory U b (coarseMatrices U b) :=
    responseBasicVariationalIdentitiesTheory_of_isEllipticFieldOn U b
      (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  simpa [coarseMatrices_eq_ofAEEq hba] using
    ResponseBasicVariationalIdentitiesTheory.ofAEEq hba hb

theorem responseBasicVariationalIdentitiesTheory
    {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseBasicVariationalIdentitiesTheory U a (coarseMatrices U a) := by
  by_cases hd : d = 0
  · subst d
    exact responseBasicVariationalIdentitiesTheory_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    exact responseBasicVariationalIdentitiesTheory_of_neZero U a

end BookCh02

end

end Ch02
end Internal
end Homogenization
