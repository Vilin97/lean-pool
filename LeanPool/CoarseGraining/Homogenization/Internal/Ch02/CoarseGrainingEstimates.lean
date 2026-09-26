/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimatesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.Basics
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CoarseFormulas

/-! # Coarse Graining Estimates -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem variationEnergyValue_zero_dim (U : Domain 0)
    (a : CoeffOn U) (w : Solution U a) :
    variationEnergyValue U a w = 0 := by
  change average U (variationEnergyIntegrand U a w) = 0
  rw [show variationEnergyIntegrand U a w = 0 by
    funext x
    simp [variationEnergyIntegrand, vecDot, matVecMul]]
  exact volumeAverage_zero (U : Set (Vec 0))

private theorem responseCoarseGrainingEstimatesTheory_zero_dim
    (U : Domain 0) (a : CoeffOn U) :
    ResponseCoarseGrainingEstimatesTheory U a := by
  refine
    { linear_response := ?_
      coarse_graining := ?_
      average_gradient_energy := ?_
      average_flux_energy := ?_ }
  · intro p q w
    have hp : p = 0 := Subsingleton.elim p 0
    have hq : q = 0 := Subsingleton.elim q 0
    subst p
    subst q
    rw [show
        average U
          (fun x =>
            vecDot (0 : Vec 0) (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
              vecDot (0 : Vec 0) (w.toH1.grad x)) = 0 by
          change volumeAverage (U : Set (Vec 0)) _ = 0
          rw [show
              (fun x =>
                vecDot (0 : Vec 0) (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
                  vecDot (0 : Vec 0) (w.toH1.grad x)) = (0 : Vec 0 → ℝ) by
            funext x
            simp [vecDot, matVecMul]]
          exact volumeAverage_zero (U : Set (Vec 0))]
    simpa using
      mul_nonneg (Real.sqrt_nonneg (variationEnergyValue U a w))
        (Real.sqrt_nonneg ((2 : ℝ) * responseJ U a 0 0))
  · intro p w
    have hp : p = 0 := Subsingleton.elim p 0
    subst p
    simp [vecDot, matVecMul]
  · intro w
    rw [variationEnergyValue_zero_dim U a w]
    simp [vecDot, matVecMul]
  · intro w
    rw [variationEnergyValue_zero_dim U a w]
    simp [vecDot, matVecMul]

/-- The linear-response estimate follows from a response maximizer and integrability,
independently of the canonical coarse-matrix constructions. -/
private theorem linear_response_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p q : Vec d) (w : Solution U a) :
    |average U
      (fun x =>
        vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
          vecDot q (w.toH1.grad x))| ≤
      Real.sqrt (variationEnergyValue U a w) *
        Real.sqrt ((2 : ℝ) * responseJ U a p q) := by
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rcases (responseExistenceTheory U a).exists_maximizer p q with
    ⟨u, _hmean, hmax⟩
  have hOld :=
    basic_cg_identities_linear_response_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField hEll p q hInt u hmax w
  have hAvg :
      average U
          (fun x =>
            vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
              vecDot q (w.toH1.grad x)) =
        volumeAverage (U : Set (Vec d))
            (fun x => vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x))) -
          volumeAverage (U : Set (Vec d))
            (fun x => vecDot q (w.toH1.grad x)) := by
    change
      volumeAverage (U : Set (Vec d))
          (fun x =>
            vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
              vecDot q (w.toH1.grad x)) =
        volumeAverage (U : Set (Vec d))
            (fun x => vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x))) -
          volumeAverage (U : Set (Vec d))
            (fun x => vecDot q (w.toH1.grad x))
    exact volumeAverage_sub (hInt.flux p w) (hInt.grad q w)
  rw [hAvg, abs_sub_comm]
  simpa [variationEnergyValue, book_responseJ_eq_ResponseJ U a p q] using! hOld

private theorem responseCoarseGrainingEstimatesTheory_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseCoarseGrainingEstimatesTheory U a := by
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEll hvol with
    ⟨_R, _sigma0, _compat, hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hEllAdj :
      IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
        (adjointCoeffField a.toCoeffField) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEllAdj hvol with
    ⟨_RAdj, _sigmaAdj, _compatAdj, hAAdj, _hSInvAdj, hSAdj0, hKAdj0,
      hSigmaAdj0, _hSigmaCanonicalAdj⟩
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det := by
    exact
      isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := a.toCoeffField) _R U.isDomain hEll hvol
        _compat hS
  have hStarAdjEq :
      Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaStarCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hKappaAdjEq :
      Homogenization.kappaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        -(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
    kappaCoarse_adjointCoeffField_eq_neg_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hSigmaAdjEq :
      Homogenization.sigmaCoarse (U : Set (Vec d))
          (adjointCoeffField a.toCoeffField) =
        Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField :=
    sigmaCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix
      (U := (U : Set (Vec d))) (a := a.toCoeffField) hA hAAdj
  have hdetAdj : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d))
        (adjointCoeffField a.toCoeffField)).det := by
    simpa [hStarAdjEq] using hdet
  have hSigmaCanon :
      IsSigmaCoarse (U : Set (Vec d)) a.toCoeffField
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet] using hSigma
  have hSAdj :
      IsSigmaStarCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) := by
    simpa [hStarAdjEq] using hSAdj0
  have hKAdj :
      IsKappaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (-(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) := by
    simpa [hStarAdjEq, hKappaAdjEq] using hKAdj0
  have hSigmaAdjCanon0 :
      IsSigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField))
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField))
        (Homogenization.kappaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)) := by
    simpa [sigmaCoarse_eq_of_isSigmaCoarse hSAdj0 hKAdj0 hSigmaAdj0 hdetAdj]
      using hSigmaAdj0
  have hSigmaAdj :
      IsSigmaCoarse (U : Set (Vec d)) (adjointCoeffField a.toCoeffField)
        (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (-(Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)) := by
    simpa [hSigmaAdjEq, hStarAdjEq, hKappaAdjEq] using hSigmaAdjCanon0
  have hb :
      Book.Ch02.bCoarse U a =
        Homogenization.bCoarse
          (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
          (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) :=
    book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse U a hS
  refine
    { linear_response := ?_
      coarse_graining := ?_
      average_gradient_energy := ?_
      average_flux_energy := ?_ }
  · exact linear_response_of_isEllipticFieldOn U a hEll
  · intro p w
    let q0 : Vec d :=
      matVecMul (Book.Ch02.sigmaStarCoarse U a - Book.Ch02.kappaCoarse U a) p
    rcases (responseExistenceTheory U a).exists_maximizer p q0 with
      ⟨u, _hmean, hmax⟩
    have hmaxOld :
        Book.Ch02.IsResponseMaximizer U a p
          (matVecMul
            (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField -
              Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) p) u := by
      simpa [q0, book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
        book_kappaCoarse_eq_kappaCoarse U a] using hmax
    have hOld :=
      basic_cg_identities_coarse_graining_average_difference_canonical_of_isSigmaCoarse
        (U : Set (Vec d)) a.toCoeffField hEll hS hK hSigmaCanon hSAdj hKAdj
        hSigmaAdj hdet p hInt u hmaxOld w
    have hDefNonneg :
        0 ≤ vecDot p
          (matVecMul
            (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
              Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p) := by
      have hle :=
        sigmaStarCoarse_le_sigmaCoarse_of_isSigmaCoarse
          (U := (U : Set (Vec d))) (a := a.toCoeffField)
          hS hK hSigmaCanon hSAdj hKAdj hSigmaAdj hdet p
      have hsplit :
          vecDot p
              (matVecMul
                (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                  Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p) =
            vecDot p
                (matVecMul
                  (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) p) -
              vecDot p
                (matVecMul
                  (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p) := by
        simp [sub_eq_add_neg, add_matVecMul, neg_matVecMul, vecDot_add_right,
          vecDot_neg_right]
      nlinarith
    have hRhs :
        Real.sqrt
            (volumeAverage (U : Set (Vec d))
              (scalarVariationEnergyIntegrand a.toCoeffField w)) *
          Real.sqrt
            (2 *
              vecDot p
                (matVecMul
                  (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                    Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p)) =
        Real.sqrt (2 : ℝ) *
            Real.sqrt
              (vecDot p
                (matVecMul
                  (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField -
                    Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) p)) *
          Real.sqrt
            (volumeAverage (U : Set (Vec d))
              (scalarVariationEnergyIntegrand a.toCoeffField w)) := by
      rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by norm_num)]
      ring
    rw [hRhs] at hOld
    simpa [variationEnergyValue, averageGradient, averageFlux, aStarCoarse,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a,
      book_kappaCoarse_eq_kappaCoarse U a,
      book_sigmaCoarse_eq_sigmaCoarse U a] using! hOld
  · intro w
    let q0 : Vec d :=
      matVecMul (Book.Ch02.sigmaStarCoarse U a) (averageGradient U a w)
    rcases (responseExistenceTheory U a).exists_maximizer 0 q0 with
      ⟨u, _hmean, hmax⟩
    have hmaxOld :
        Book.Ch02.IsResponseMaximizer U a 0
          (matVecMul
            (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
            (fun i => volumeAverage (U : Set (Vec d)) (fun x => w.toH1.grad x i))) u := by
      simpa [q0, averageGradient, averageVec,
        book_sigmaStarCoarse_eq_sigmaStarCoarse U a] using! hmax
    have hOld :=
      basic_cg_identities_energy_average_gradient_canonical_of_isSigmaStarCoarse
        (U : Set (Vec d)) a.toCoeffField hEll hS hdet hInt w u hmaxOld
    simpa [variationEnergyValue, averageGradient, averageVec,
      book_sigmaStarCoarse_eq_sigmaStarCoarse U a] using! hOld
  · intro w
    let p0 : Vec d := -matVecMul (Book.Ch02.bCoarse U a)⁻¹ (averageFlux U a w)
    rcases (responseExistenceTheory U a).exists_maximizer p0 0 with
      ⟨u, _hmean, hmax⟩
    have hmaxOld :
        Book.Ch02.IsResponseMaximizer U a
          (-matVecMul
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
              (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
              (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField))⁻¹
            (fun i =>
              volumeAverage (U : Set (Vec d))
                (fun x => matVecMul (a.toCoeffField x) (w.toH1.grad x) i))) 0 u := by
      simpa [p0, averageFlux, averageVec, hb] using! hmax
    have hOld :=
      basic_cg_identities_energy_average_flux_canonical_of_isSigmaCoarse
        (U : Set (Vec d)) a.toCoeffField hEll hS hK hSigmaCanon hdet hInt w u
        hmaxOld
    simpa [variationEnergyValue, averageFlux, averageVec, hb] using! hOld

private theorem responseCoarseGrainingEstimatesTheory_of_neZero
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U) :
    ResponseCoarseGrainingEstimatesTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hb : ResponseCoarseGrainingEstimatesTheory U b :=
    responseCoarseGrainingEstimatesTheory_of_isEllipticFieldOn U b
      (by simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a)
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseCoarseGrainingEstimatesTheory.ofAEEq hba hb

theorem responseCoarseGrainingEstimatesTheory
    {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseCoarseGrainingEstimatesTheory U a := by
  by_cases hd : d = 0
  · subst d
    exact responseCoarseGrainingEstimatesTheory_zero_dim U a
  · let : NeZero d := ⟨hd⟩
    exact responseCoarseGrainingEstimatesTheory_of_neZero U a

end BookCh02

end

end Ch02
end Internal
end Homogenization
