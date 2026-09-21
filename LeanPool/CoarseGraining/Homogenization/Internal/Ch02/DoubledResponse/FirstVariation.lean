/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.MaximizerAlgebra

/-! # First Variation -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Doubled Response First Variation

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

theorem first_variation_scalar_representatives_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p pStar q qStar : Vec d)
    (v : Solution U a) (vStar : Solution U a.transpose)
    (hv : Book.Ch02.IsResponseMaximizer U a (p - pStar) (qStar - q) v)
    (hvStar :
      Book.Ch02.IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStar)
    (w : Solution U a) (z : Solution U a.transpose) :
    average U
        (doubledResponseFirstVariationLeft U a (p, q) (qStar, pStar)
          (doubledFieldOfSolutions a w z)) =
      average U
        (doubledResponseFirstVariationRight U a
          (doubledFieldOfScalarMaximizers a v vStar)
          (doubledFieldOfSolutions a w z)) := by
  let S : DoubledField d := doubledFieldOfScalarMaximizers a v vStar
  let T : DoubledField d := doubledFieldOfSolutions a w z
  let w2 : Solution U a := solutionSMul U a (2 : ℝ) w
  let z2 : Solution U a.transpose := solutionSMul U a.transpose (2 : ℝ) z
  have hEllAdj :
      IsEllipticFieldOn a.transpose.lam a.transpose.Lam (U : Set (Vec d))
        a.transpose.toCoeffField := by
    simpa [Homogenization.adjointCoeffField] using!
      isEllipticFieldOn_adjointCoeffField hEll
  have hFirst := responseFirstVariationTheory_of_isEllipticFieldOn U a hEll
  have hFirstAdj := responseFirstVariationTheory_of_isEllipticFieldOn U a.transpose hEllAdj
  have hfirstPublic :=
    hFirst.first_variation (p - pStar) (qStar - q) v hv w2
  have hfirst :
      volumeAverage (U : Set (Vec d))
        (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField
          (p - pStar) (qStar - q) v w2) = 0 := by
    change
      volumeAverage (U : Set (Vec d))
        (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField
          (p - pStar) (qStar - q) v w2) = 0 at hfirstPublic
    exact hfirstPublic
  have hfirstStarPublic :=
    hFirstAdj.first_variation (pStar + p) (qStar + q) vStar hvStar z2
  have hfirstStar :
      volumeAverage (U : Set (Vec d))
        (scalarFirstVariationIntegrand (U : Set (Vec d))
          (Homogenization.adjointCoeffField a.toCoeffField)
          (pStar + p) (qStar + q) vStar z2) = 0 := by
    change
      volumeAverage (U : Set (Vec d))
        (scalarFirstVariationIntegrand (U : Set (Vec d)) a.transpose.toCoeffField
          (pStar + p) (qStar + q) vStar z2) = 0 at hfirstStarPublic
    simpa [Homogenization.adjointCoeffField] using! hfirstStarPublic
  have hSplit :=
    volumeAverage_blockFirstVariationIntegrand_pair_half_eq_scalarFirstVariation_sum_of_isEllipticFieldOn
      (a := a.toCoeffField) U.measurableSet hEll p pStar q qStar v w2 vStar z2
  have hBlockZero :
      volumeAverage (U : Set (Vec d))
        (blockFirstVariationIntegrand a.toCoeffField (p, q) (qStar, pStar)
          (blockResponsePairHalfState a.toCoeffField v vStar)
          (blockResponsePairHalfState a.toCoeffField w2 z2)) = 0 := by
    rw [hSplit, hfirst, hfirstStar]
    ring
  have hSstate : blockStateOfDoubled S =
      blockResponsePairHalfState a.toCoeffField v vStar := by
    simpa [S] using blockStateOfDoubled_scalarMaximizers_eq_pairHalf U a v vStar
  have hTstate : blockStateOfDoubled T =
      blockResponsePairHalfState a.toCoeffField w2 z2 := by
    simpa [T, w2, z2] using blockStateOfDoubled_solutions_eq_pairHalf_two U a w z
  have hBlockZeroStates :
      volumeAverage (U : Set (Vec d))
        (blockFirstVariationIntegrand a.toCoeffField (p, q) (qStar, pStar)
          (blockStateOfDoubled S) (blockStateOfDoubled T)) = 0 := by
    simpa [hSstate, hTstate] using hBlockZero
  let f : Vec d → ℝ := doubledResponseFirstVariationLeft U a (p, q) (qStar, pStar) T
  let g : Vec d → ℝ := doubledResponseFirstVariationRight U a S T
  have hfun :
      blockFirstVariationIntegrand a.toCoeffField (p, q) (qStar, pStar)
          (blockStateOfDoubled S) (blockStateOfDoubled T) =
        f - g := by
    funext x
    simp [f, g, doubledResponseFirstVariationLeft, doubledResponseFirstVariationRight,
      blockFirstVariationIntegrand, blockStateOfDoubled, DoubledField.eval, BlockState.eval,
      book_blockMatrixField_eq_blockCoeffField, sub_eq_add_neg]
    ring
  have hzeroFG : average U (fun x => f x - g x) = 0 := by
    change volumeAverage (U : Set (Vec d)) (f - g) = 0
    simpa [hfun] using hBlockZeroStates
  have hSspace :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled S) := by
    simpa [hSstate, blockResponsePairHalfState, blockResponsePairState] using
      blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll v vStar
  have hSint :
      BlockResponseIntegrabilityData (U : Set (Vec d)) a.toCoeffField
        (blockStateOfDoubled S) := by
    simpa [hSstate] using
      blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll v vStar
  have hSmem :
      MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled S).eval :=
    blockResponse_memBlockL2_of_mem_responseSpace_of_integrabilityData hSspace hSint
  have hTspace :
      BlockResponseSpace a.toCoeffField (U : Set (Vec d)) (blockStateOfDoubled T) := by
    simpa [hTstate, blockResponsePairHalfState, blockResponsePairState] using
      blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll w2 z2
  have hTint :
      BlockResponseIntegrabilityData (U : Set (Vec d)) a.toCoeffField
        (blockStateOfDoubled T) := by
    simpa [hTstate] using
      blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn
        (a := a.toCoeffField) hEll w2 z2
  have hTmem :
      MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled T).eval :=
    blockResponse_memBlockL2_of_mem_responseSpace_of_integrabilityData hTspace hTint
  let Pconst : BlockState d := { potential := fun _ => p, flux := fun _ => q }
  have hPconst :
      MemBlockL2 (U : Set (Vec d)) Pconst.eval := by
    simpa [Pconst, BlockState.eval, blockField] using!
      memBlockL2_blockField
        (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d))) (c := p))
        (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d))) (c := q))
  have hTpot : MemVectorL2 (U : Set (Vec d)) fun x => ((blockStateOfDoubled T).eval x).1 :=
    memVectorL2_fst_of_memBlockL2 hTmem
  have hTflux : MemVectorL2 (U : Set (Vec d)) fun x => ((blockStateOfDoubled T).eval x).2 :=
    memVectorL2_snd_of_memBlockL2 hTmem
  have hQpot :
      MeasureTheory.IntegrableOn
        (fun x => vecDot qStar (((blockStateOfDoubled T).eval x).1))
        (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2
      (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d))) (c := qStar))
      hTpot
  have hQflux :
      MeasureTheory.IntegrableOn
        (fun x => vecDot pStar (((blockStateOfDoubled T).eval x).2))
        (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2
      (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d))) (c := pStar))
      hTflux
  have hQInt :
      MeasureTheory.IntegrableOn
        (fun x => blockVecDot (qStar, pStar) ((blockStateOfDoubled T).eval x))
        (U : Set (Vec d)) := by
    simpa [MeasureTheory.IntegrableOn, blockVecDot] using!
      hQpot.integrable.add hQflux.integrable
  have hPInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          blockVecDot (p, q)
            (blockMatVecMul (blockMatrixField a x) ((blockStateOfDoubled T).eval x)))
        (U : Set (Vec d)) := by
    simpa [Pconst, blockPairingIntegrand, BlockState.eval,
      book_blockMatrixField_eq_blockCoeffField] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (U := (U : Set (Vec d))) (a := a.toCoeffField)
        (X := Pconst) (Y := blockStateOfDoubled T) hPconst hTmem hEll
  have hf : MeasureTheory.IntegrableOn f (U : Set (Vec d)) := by
    simpa [f, doubledResponseFirstVariationLeft, T, blockStateOfDoubled,
      DoubledField.eval, sub_eq_add_neg, MeasureTheory.IntegrableOn] using!
      hQInt.integrable.sub hPInt.integrable
  have hg : MeasureTheory.IntegrableOn g (U : Set (Vec d)) := by
    simpa [g, doubledResponseFirstVariationRight, S, T, blockStateOfDoubled,
      DoubledField.eval, blockPairingIntegrand, BlockState.eval, blockMatrixField,
      book_blockMatrixField_eq_blockCoeffField] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (U := (U : Set (Vec d))) (a := a.toCoeffField)
        (X := blockStateOfDoubled T) (Y := blockStateOfDoubled S)
        hTmem hSmem hEll
  exact average_eq_of_average_sub_eq_zero U hf hg hzeroFG

theorem first_variation_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ P Q : BlockVec d, ∀ S T : DoubledField d,
      IsDoubledResponseMaximizer U a P Q S →
        IsDoubledResponseField U a T →
          average U
              (fun x =>
                blockVecDot Q (T.eval x) -
                  blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))) =
            average U
              (fun x =>
                blockVecDot (T.eval x)
                  (blockMatVecMul (blockMatrixField a x) (S.eval x))) := by
  intro P Q S T hS hT
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p pStar q qStar S hS with
    ⟨v, vStar, hv, hvStar, hSsame⟩
  rcases (response_space_by_solutions_of_isEllipticFieldOn U a hEll T).mp hT with
    ⟨w, z, hTsame⟩
  change
    average U (doubledResponseFirstVariationLeft U a (p, q) (qStar, pStar) T) =
      average U (doubledResponseFirstVariationRight U a S T)
  calc
    average U (doubledResponseFirstVariationLeft U a (p, q) (qStar, pStar) T) =
        average U
          (doubledResponseFirstVariationLeft U a (p, q) (qStar, pStar)
            (doubledFieldOfSolutions a w z)) :=
      doubledResponseFirstVariationLeft_average_eq_of_sameAE U a (p, q) (qStar, pStar) hTsame
    _ =
        average U
          (doubledResponseFirstVariationRight U a
            (doubledFieldOfScalarMaximizers a v vStar)
            (doubledFieldOfSolutions a w z)) :=
      first_variation_scalar_representatives_of_isEllipticFieldOn
        U a hEll p pStar q qStar v vStar hv hvStar w z
    _ = average U (doubledResponseFirstVariationRight U a S T) := by
      exact
        (doubledResponseFirstVariationRight_average_eq_of_sameAE U a hSsame hTsame).symm

end BookCh02

end

end Ch02
end Internal
end Homogenization
