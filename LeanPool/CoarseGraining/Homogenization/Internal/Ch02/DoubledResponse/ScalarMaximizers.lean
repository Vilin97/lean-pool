/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.ResponseSpace

/-! # Scalar Maximizers -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Scalar Maximizers and Doubled Maximizers

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

theorem doubled_response_by_scalar_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ p pStar q qStar : Vec d,
      doubledResponseJ U a (p, q) (qStar, pStar) =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) := by
  intro p pStar q qStar
  have hBlock :=
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a.toCoeffField) U.isDomain hEll (domain_volume_pos U).ne'
      p pStar q qStar
  calc
    doubledResponseJ U a (p, q) (qStar, pStar) =
        BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField := by
          rw [book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn U a hEll]
    _ =
        (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d)) (p - pStar) (qStar - q)
            a.toCoeffField +
          (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d)) (pStar + p) (qStar + q)
            (Homogenization.adjointCoeffField a.toCoeffField) := hBlock
    _ =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) := by
          rw [book_responseJ_eq_ResponseJ U a,
            book_responseJ_eq_ResponseJ U a.transpose]
          rfl

theorem doubledFieldOfScalarMaximizers_eq_pairHalf {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (v : Solution U a)
    (vStar : Solution U a.transpose) :
    doubledFieldOfScalarMaximizers a v vStar =
      doubledFieldOfBlockState
        (blockResponsePairHalfState a.toCoeffField v vStar) := by
  apply doubledField_ext
  · funext x
    change
      ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x)) x =
        ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x)) x
    rfl
  · funext x
    change
      ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x))) x =
        ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (matTranspose (a.toCoeffField x)) (vStar.toH1.grad x))) x
    simp [CoeffOn.transpose_apply]

theorem old_isResponseMaximizer_of_public {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d)
    (v : Solution U a) (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q a.toCoeffField v := by
  intro w
  simpa [book_responseValue_eq_volumeAverage_scalarResponseIntegrand] using hv w

theorem doubledResponseValue_scalarMaximizers_eq_scalar_responseJ_of_isEllipticFieldOn
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p pStar q qStar : Vec d)
    (v : Solution U a) (vStar : Solution U a.transpose)
    (hv : Book.Ch02.IsResponseMaximizer U a (p - pStar) (qStar - q) v)
    (hvStar : Book.Ch02.IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStar) :
    doubledResponseValue U a (p, q) (qStar, pStar)
        (doubledFieldOfScalarMaximizers a v vStar) =
      (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) := by
  have hEq := doubledFieldOfScalarMaximizers_eq_pairHalf U a v vStar
  have hvOld :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) (p - pStar) (qStar - q)
        a.toCoeffField v :=
    old_isResponseMaximizer_of_public U a (p - pStar) (qStar - q) v hv
  have hvStarOld :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) (pStar + p) (qStar + q)
        (Homogenization.adjointCoeffField a.toCoeffField) vStar := by
    simpa [Homogenization.adjointCoeffField] using!
      old_isResponseMaximizer_of_public U a.transpose (pStar + p) (qStar + q) vStar hvStar
  calc
    doubledResponseValue U a (p, q) (qStar, pStar)
        (doubledFieldOfScalarMaximizers a v vStar) =
      volumeAverage (U : Set (Vec d))
        (blockResponseIntegrand a.toCoeffField (p, q) (qStar, pStar)
          (blockResponsePairHalfState a.toCoeffField v vStar)) := by
        rw [hEq]
        rfl
    _ =
        (1 / 2 : ℝ) *
            volumeAverage (U : Set (Vec d))
              (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField
                (p - pStar) (qStar - q) v) +
          (1 / 2 : ℝ) *
            volumeAverage (U : Set (Vec d))
              (scalarResponseIntegrand (U : Set (Vec d))
                (Homogenization.adjointCoeffField a.toCoeffField)
                (pStar + p) (qStar + q) vStar) :=
        volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
          (a := a.toCoeffField) U.measurableSet hEll p pStar q qStar v vStar
    _ =
        (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d)) (p - pStar) (qStar - q)
            a.toCoeffField +
          (1 / 2 : ℝ) * ResponseJ (U : Set (Vec d)) (pStar + p) (qStar + q)
            (Homogenization.adjointCoeffField a.toCoeffField) := by
        rw [responseJ_eq_of_isResponseMaximizer (U : Set (Vec d)) (p - pStar)
            (qStar - q) a.toCoeffField hvOld,
          responseJ_eq_of_isResponseMaximizer (U : Set (Vec d)) (pStar + p)
            (qStar + q) (Homogenization.adjointCoeffField a.toCoeffField) hvStarOld]
    _ =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) := by
        rw [book_responseJ_eq_ResponseJ U a,
          book_responseJ_eq_ResponseJ U a.transpose]
        rfl

theorem doubledResponseValue_eq_of_sameAE {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d)
    {X Y : DoubledField d} (hXY : DoubledField.SameAE (U := U) X Y) :
    doubledResponseValue U a P Q X = doubledResponseValue U a P Q Y := by
  unfold doubledResponseValue average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hXY.1, hXY.2] with x hxPot hxFlux
  simp [doubledResponseIntegrand, blockEnergyDensityAt, DoubledField.eval, hxPot, hxFlux]

theorem isDoubledResponseMaximizer_of_sameAE {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d)
    {X Y : DoubledField d} (hXY : DoubledField.SameAE (U := U) X Y)
    (hY : IsDoubledResponseMaximizer U a P Q Y) :
    IsDoubledResponseMaximizer U a P Q X := by
  refine ⟨isDoubledResponseField_of_sameAE U a hXY hY.1, ?_⟩
  intro Z hZ
  calc
    doubledResponseValue U a P Q Z ≤ doubledResponseValue U a P Q Y :=
      hY.2 Z hZ
    _ = doubledResponseValue U a P Q X := by
      exact (doubledResponseValue_eq_of_sameAE U a P Q hXY).symm

theorem doubledResponseJ_eq_value_of_maximizer {d : ℕ}
    {U : Domain d} {a : CoeffOn U} {P Q : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledResponseMaximizer U a P Q X) :
    doubledResponseJ U a P Q = doubledResponseValue U a P Q X := by
  unfold doubledResponseJ
  have hGreatest :
      IsGreatest (doubledResponseValueSet U a P Q) (doubledResponseValue U a P Q X) := by
    refine ⟨⟨X, hX.1, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨Y, hY, rfl⟩
    exact hX.2 Y hY
  exact hGreatest.csSup_eq

theorem doubledResponseValue_scalarPair_eq_scalar_values_of_isEllipticFieldOn
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p pStar q qStar : Vec d)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    doubledResponseValue U a (p, q) (qStar, pStar)
        (doubledFieldOfScalarMaximizers a v vStar) =
      (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField
              (p - pStar) (qStar - q) v) +
        (1 / 2 : ℝ) *
          volumeAverage (U : Set (Vec d))
            (scalarResponseIntegrand (U : Set (Vec d))
              (Homogenization.adjointCoeffField a.toCoeffField)
              (pStar + p) (qStar + q) vStar) := by
  have hEq := doubledFieldOfScalarMaximizers_eq_pairHalf U a v vStar
  calc
    doubledResponseValue U a (p, q) (qStar, pStar)
        (doubledFieldOfScalarMaximizers a v vStar) =
      volumeAverage (U : Set (Vec d))
        (blockResponseIntegrand a.toCoeffField (p, q) (qStar, pStar)
          (blockResponsePairHalfState a.toCoeffField v vStar)) := by
        rw [hEq]
        rfl
    _ =
        (1 / 2 : ℝ) *
            volumeAverage (U : Set (Vec d))
              (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField
                (p - pStar) (qStar - q) v) +
          (1 / 2 : ℝ) *
            volumeAverage (U : Set (Vec d))
              (scalarResponseIntegrand (U : Set (Vec d))
                (Homogenization.adjointCoeffField a.toCoeffField)
                (pStar + p) (qStar + q) vStar) :=
        volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
          (a := a.toCoeffField) U.measurableSet hEll p pStar q qStar v vStar

theorem old_isResponseMaximizer_of_value_eq_responseJ {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q : Vec d) (v : AHarmonicFunction a U)
    (hval :
      volumeAverage U (scalarResponseIntegrand U a p q v) =
        ResponseJ U p q a) :
    Homogenization.IsResponseMaximizer U p q a v := by
  intro w
  calc
    volumeAverage U (scalarResponseIntegrand U a p q w) ≤
        ResponseJ U p q a :=
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEll hvol p q (responseJValueSet_mem U p q a w)
    _ = volumeAverage U (scalarResponseIntegrand U a p q v) := hval.symm

theorem public_isResponseMaximizer_of_old {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (p q : Vec d) (v : Solution U a)
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q a.toCoeffField v) :
    Book.Ch02.IsResponseMaximizer U a p q v := by
  intro w
  simpa [book_responseValue_eq_volumeAverage_scalarResponseIntegrand] using hv w

theorem doubledFieldOfScalarMaximizers_mem_responseField_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    IsDoubledResponseField U a (doubledFieldOfScalarMaximizers a v vStar) := by
  have hOld :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d))
        (blockResponsePairHalfState a.toCoeffField v vStar) := by
    simpa [blockResponsePairHalfState, blockResponsePairState,
      Homogenization.adjointCoeffField] using
      blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll v vStar
  have hInt :
      BlockResponseIntegrabilityData (U : Set (Vec d)) a.toCoeffField
        (blockResponsePairHalfState a.toCoeffField v vStar) := by
    simpa [Homogenization.adjointCoeffField] using
      blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll v vStar
  simpa [doubledFieldOfScalarMaximizers, doubledFieldOfSolutions,
    doubledFieldOfBlockState, blockResponsePairHalfState, blockResponsePairState,
    Homogenization.adjointCoeffField] using!
    isDoubledResponseField_of_blockResponseSpace U a hOld hInt.flux_memL2

theorem scalar_maximizers_give_doubled_maximizer_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ p pStar q qStar : Vec d,
      ∀ v : Solution U a, ∀ vStar : Solution U a.transpose,
        Book.Ch02.IsResponseMaximizer U a (p - pStar) (qStar - q) v →
          Book.Ch02.IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStar →
            IsDoubledResponseMaximizer U a (p, q) (qStar, pStar)
              (doubledFieldOfScalarMaximizers a v vStar) := by
  intro p pStar q qStar v vStar hv hvStar
  refine ⟨doubledFieldOfScalarMaximizers_mem_responseField_of_isEllipticFieldOn U a hEll v vStar, ?_⟩
  intro Y hY
  have hYOld :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled Y) :=
    blockResponseSpace_of_isDoubledResponseField_of_isEllipticFieldOn U a hEll hY
  have hYInt :
      BlockResponseIntegrabilityData (U : Set (Vec d)) a.toCoeffField
        (blockStateOfDoubled Y) :=
    blockResponseIntegrabilityData_of_flux_memL2_of_mem_responseSpace_of_isEllipticFieldOn
      hYOld hY.1.2.1 hEll
  have hYmem :
      volumeAverage (U : Set (Vec d))
          (blockResponseIntegrand a.toCoeffField (p, q) (qStar, pStar)
            (blockStateOfDoubled Y)) ∈
        blockJValueSet (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField :=
    ⟨blockStateOfDoubled Y, hYOld, hYInt, rfl⟩
  have hYle :
      volumeAverage (U : Set (Vec d))
          (blockResponseIntegrand a.toCoeffField (p, q) (qStar, pStar)
            (blockStateOfDoubled Y)) ≤
        BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField :=
    le_blockJ_of_mem_blockJValueSet_of_isEllipticFieldOn
      U.measurableSet hEll (domain_volume_pos U).ne' (p, q) (qStar, pStar) hYmem
  have hCand :
      doubledResponseValue U a (p, q) (qStar, pStar)
          (doubledFieldOfScalarMaximizers a v vStar) =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
    doubledResponseValue_scalarMaximizers_eq_scalar_responseJ_of_isEllipticFieldOn
      U a hEll p pStar q qStar v vStar hv hvStar
  calc
    doubledResponseValue U a (p, q) (qStar, pStar) Y =
        volumeAverage (U : Set (Vec d))
          (blockResponseIntegrand a.toCoeffField (p, q) (qStar, pStar)
            (blockStateOfDoubled Y)) := by
          rfl
    _ ≤ BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField := hYle
    _ = doubledResponseJ U a (p, q) (qStar, pStar) := by
          rw [book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn U a hEll]
    _ =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
          doubled_response_by_scalar_of_isEllipticFieldOn U a hEll p pStar q qStar
    _ = doubledResponseValue U a (p, q) (qStar, pStar)
          (doubledFieldOfScalarMaximizers a v vStar) := hCand.symm

theorem maximizer_exists_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ P Q : BlockVec d, DoubledResponseMaximizerExists U a P Q := by
  intro P Q
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rcases responseMaximizerExists_of_isEllipticFieldOn U a hEll
      (p - pStar) (qStar - q) with
    ⟨v, _hvMean, hv⟩
  have hEllAdj :
      IsEllipticFieldOn a.transpose.lam a.transpose.Lam (U : Set (Vec d))
        a.transpose.toCoeffField := by
    simpa [Homogenization.adjointCoeffField] using!
      isEllipticFieldOn_adjointCoeffField hEll
  rcases responseMaximizerExists_of_isEllipticFieldOn U a.transpose hEllAdj
      (pStar + p) (qStar + q) with
    ⟨vStar, _hvStarMean, hvStar⟩
  exact
    ⟨doubledFieldOfScalarMaximizers a v vStar,
      scalar_maximizers_give_doubled_maximizer_of_isEllipticFieldOn
        U a hEll p pStar q qStar v vStar hv hvStar⟩

theorem doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ p pStar q qStar : Vec d, ∀ X : DoubledField d,
      IsDoubledResponseMaximizer U a (p, q) (qStar, pStar) X →
        ∃ v : Solution U a, ∃ vStar : Solution U a.transpose,
          Book.Ch02.IsResponseMaximizer U a (p - pStar) (qStar - q) v ∧
            Book.Ch02.IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStar ∧
              DoubledField.SameAE (U := U) X (doubledFieldOfScalarMaximizers a v vStar) := by
  intro p pStar q qStar X hXmax
  have hOld :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled X) :=
    blockResponseSpace_of_isDoubledResponseField_of_isEllipticFieldOn U a hEll hXmax.1
  have hLowerL2 :
      MemVectorL2 (U : Set (Vec d))
        (fun x =>
          (blockMatVecMul (blockCoeffField a.toCoeffField x)
            ((blockStateOfDoubled X).eval x)).2) := by
    exact
      lowerImage_memVectorL2_of_memVectorL2_of_isEllipticFieldOn
        (a := a.toCoeffField) (X := blockStateOfDoubled X)
        hXmax.1.1.1.1 hXmax.1.1.2.1 hEll
  rcases
    exists_blockResponsePairHalfState_ae_eq_of_mem_responseSpace_of_lowerImage_memVectorL2_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a.toCoeffField) U.isDomain hOld hLowerL2 hEll with
    ⟨v, vStarOld, hhalf⟩
  let vStar : Solution U a.transpose := by
    simpa [Homogenization.adjointCoeffField] using! vStarOld
  have hEq :
      doubledFieldOfScalarMaximizers a v vStar =
        doubledFieldOfBlockState
          (blockResponsePairHalfState a.toCoeffField v vStarOld) := by
    simpa [vStar, Homogenization.adjointCoeffField] using
      doubledFieldOfScalarMaximizers_eq_pairHalf U a v vStar
  have hSamePair :
      DoubledField.SameAE (U := U) X
        (doubledFieldOfBlockState
          (blockResponsePairHalfState a.toCoeffField v vStarOld)) := by
    constructor
    · filter_upwards [hhalf] with x hx
      exact (congrArg Prod.fst hx).symm
    · filter_upwards [hhalf] with x hx
      exact (congrArg Prod.snd hx).symm
  have hSame :
      DoubledField.SameAE (U := U) X (doubledFieldOfScalarMaximizers a v vStar) := by
    rw [hEq]
    exact hSamePair
  have hValueSame :
      doubledResponseValue U a (p, q) (qStar, pStar) X =
        doubledResponseValue U a (p, q) (qStar, pStar)
          (doubledFieldOfScalarMaximizers a v vStar) :=
    doubledResponseValue_eq_of_sameAE U a (p, q) (qStar, pStar) hSame
  have hCandScalar :=
    doubledResponseValue_scalarPair_eq_scalar_values_of_isEllipticFieldOn
      U a hEll p pStar q qStar v vStar
  have hMaxValue :
      doubledResponseJ U a (p, q) (qStar, pStar) =
        doubledResponseValue U a (p, q) (qStar, pStar) X :=
    doubledResponseJ_eq_value_of_maximizer hXmax
  have hBlockSplit :=
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a.toCoeffField) U.isDomain hEll (domain_volume_pos U).ne'
      p pStar q qStar
  let val := volumeAverage (U : Set (Vec d))
      (scalarResponseIntegrand (U : Set (Vec d)) a.toCoeffField
        (p - pStar) (qStar - q) v)
  let valStar := volumeAverage (U : Set (Vec d))
      (scalarResponseIntegrand (U : Set (Vec d))
        (Homogenization.adjointCoeffField a.toCoeffField)
        (pStar + p) (qStar + q) vStar)
  let J := ResponseJ (U : Set (Vec d)) (p - pStar) (qStar - q) a.toCoeffField
  let JStar := ResponseJ (U : Set (Vec d)) (pStar + p) (qStar + q)
      (Homogenization.adjointCoeffField a.toCoeffField)
  have hSumEq :
      (1 / 2 : ℝ) * val + (1 / 2 : ℝ) * valStar =
        (1 / 2 : ℝ) * J + (1 / 2 : ℝ) * JStar := by
    calc
      (1 / 2 : ℝ) * val + (1 / 2 : ℝ) * valStar =
          doubledResponseValue U a (p, q) (qStar, pStar)
            (doubledFieldOfScalarMaximizers a v vStar) := by
            simpa [val, valStar] using hCandScalar.symm
      _ = doubledResponseValue U a (p, q) (qStar, pStar) X := hValueSame.symm
      _ = doubledResponseJ U a (p, q) (qStar, pStar) := hMaxValue.symm
      _ = BlockJ (U : Set (Vec d)) (p, q) (qStar, pStar) a.toCoeffField := by
            rw [book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn U a hEll]
      _ = (1 / 2 : ℝ) * J + (1 / 2 : ℝ) * JStar := by
            simpa [J, JStar] using hBlockSplit
  have hValLe : val ≤ J := by
    exact
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEll (domain_volume_pos U).ne' (p - pStar) (qStar - q)
        (responseJValueSet_mem (U : Set (Vec d)) (p - pStar) (qStar - q)
          a.toCoeffField v)
  have hEllAdj :
      IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d))
        (Homogenization.adjointCoeffField a.toCoeffField) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hValStarLe : valStar ≤ JStar := by
    exact
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEllAdj (domain_volume_pos U).ne' (pStar + p) (qStar + q)
        (responseJValueSet_mem (U : Set (Vec d)) (pStar + p) (qStar + q)
          (Homogenization.adjointCoeffField a.toCoeffField) vStar)
  have hValEq : val = J := by
    nlinarith [hSumEq, hValLe, hValStarLe]
  have hValStarEq : valStar = JStar := by
    nlinarith [hSumEq, hValLe, hValStarLe]
  have hvOld :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) (p - pStar) (qStar - q)
        a.toCoeffField v :=
    old_isResponseMaximizer_of_value_eq_responseJ
      hEll (domain_volume_pos U).ne' (p - pStar) (qStar - q) v
      (by simpa [val, J] using hValEq)
  have hvStarOld :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) (pStar + p) (qStar + q)
        (Homogenization.adjointCoeffField a.toCoeffField) vStar :=
    old_isResponseMaximizer_of_value_eq_responseJ
      hEllAdj (domain_volume_pos U).ne' (pStar + p) (qStar + q) vStar
      (by simpa [valStar, JStar] using hValStarEq)
  refine ⟨v, vStar, ?_, ?_, hSame⟩
  · exact public_isResponseMaximizer_of_old U a (p - pStar) (qStar - q) v hvOld
  · exact
      public_isResponseMaximizer_of_old U a.transpose (pStar + p) (qStar + q) vStar
        (by simpa [Homogenization.adjointCoeffField] using! hvStarOld)

end BookCh02

end

end Ch02
end Internal
end Homogenization
