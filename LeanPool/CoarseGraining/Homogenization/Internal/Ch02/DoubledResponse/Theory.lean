/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.FirstVariation

/-! # Theory -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Doubled Response Theory Assembly

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

theorem doubledResponseTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    DoubledResponseTheory U a where
  response_space_by_solutions :=
    response_space_by_solutions_of_isEllipticFieldOn U a hEll
  doubled_response_by_scalar :=
    doubled_response_by_scalar_of_isEllipticFieldOn U a hEll
  scalar_maximizers_give_doubled_maximizer :=
    scalar_maximizers_give_doubled_maximizer_of_isEllipticFieldOn U a hEll
  maximizer_exists :=
    maximizer_exists_of_isEllipticFieldOn U a hEll
  maximizer_unique_ae :=
    maximizer_unique_ae_of_isEllipticFieldOn U a hEll
  maximizer_add_sameAE :=
    maximizer_add_sameAE_of_isEllipticFieldOn U a hEll
  maximizer_smul_sameAE :=
    maximizer_smul_sameAE_of_isEllipticFieldOn U a hEll
  first_variation :=
    first_variation_of_isEllipticFieldOn U a hEll

theorem doubledResponseTheory_ofAEEq {d : ℕ}
    {U : Domain d} {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (ha : DoubledResponseTheory U a) :
    DoubledResponseTheory U b where
  response_space_by_solutions := by
    intro X
    constructor
    · intro hXb
      have hXa : IsDoubledResponseField U a X :=
        IsDoubledResponseField.ofAEEq h.symm hXb
      rcases (ha.response_space_by_solutions X).mp hXa with
        ⟨va, vStara, hXsame⟩
      refine
        ⟨Solution.ofAEEq h va, Solution.ofAEEq h.transpose vStara,
          doubledSameAE_trans hXsame ?_⟩
      exact doubledFieldOfSolutions_sameAE_ofAEEq h va vStara
    · rintro ⟨vb, vStarb, hXsame⟩
      let va : Solution U a := Solution.ofAEEq h.symm vb
      let vStara : Solution U a.transpose := Solution.ofAEEq h.symm.transpose vStarb
      have hAfield :
          IsDoubledResponseField U a (doubledFieldOfSolutions a va vStara) := by
        exact
          (ha.response_space_by_solutions
            (doubledFieldOfSolutions a va vStara)).mpr
            ⟨va, vStara, doubledSameAE_refl _⟩
      have hAfield_b :
          IsDoubledResponseField U b (doubledFieldOfSolutions a va vStara) :=
        IsDoubledResponseField.ofAEEq h hAfield
      have hSame :
          DoubledField.SameAE (U := U)
            (doubledFieldOfSolutions a va vStara)
            (doubledFieldOfSolutions b (Solution.ofAEEq h va)
              (Solution.ofAEEq h.transpose vStara)) :=
        doubledFieldOfSolutions_sameAE_ofAEEq h va vStara
      have hBfield :
          IsDoubledResponseField U b (doubledFieldOfSolutions b vb vStarb) := by
        have hSame' :
            DoubledField.SameAE (U := U)
              (doubledFieldOfSolutions b vb vStarb)
              (doubledFieldOfSolutions a va vStara) := by
          simpa [va, vStara] using! doubledSameAE_symm hSame
        exact isDoubledResponseField_of_sameAE U b hSame' hAfield_b
      exact isDoubledResponseField_of_sameAE U b hXsame hBfield
  doubled_response_by_scalar := by
    intro p pStar q qStar
    calc
      doubledResponseJ U b (p, q) (qStar, pStar) =
          doubledResponseJ U a (p, q) (qStar, pStar) := by
        exact (doubledResponseJ_eq_ofAEEq h (p, q) (qStar, pStar)).symm
      _ =
          (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
            (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
        ha.doubled_response_by_scalar p pStar q qStar
      _ =
          (1 / 2 : ℝ) * responseJ U b (p - pStar) (qStar - q) +
            (1 / 2 : ℝ) * responseJ U b.transpose (pStar + p) (qStar + q) := by
        rw [responseJ_eq_ofAEEq h (p - pStar) (qStar - q),
          responseJ_eq_ofAEEq h.transpose (pStar + p) (qStar + q)]
  scalar_maximizers_give_doubled_maximizer := by
    intro p pStar q qStar vb vStarb hvb hvStarb
    let va : Solution U a := Solution.ofAEEq h.symm vb
    let vStara : Solution U a.transpose := Solution.ofAEEq h.symm.transpose vStarb
    have hva :
        Book.Ch02.IsResponseMaximizer U a (p - pStar) (qStar - q) va := by
      simpa [va] using hvb.ofAEEq h.symm
    have hvStara :
        Book.Ch02.IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStara := by
      simpa [vStara] using hvStarb.ofAEEq h.symm.transpose
    have hAmax :
        IsDoubledResponseMaximizer U a (p, q) (qStar, pStar)
          (doubledFieldOfScalarMaximizers a va vStara) :=
      ha.scalar_maximizers_give_doubled_maximizer p pStar q qStar va vStara hva hvStara
    have hAmax_b :
        IsDoubledResponseMaximizer U b (p, q) (qStar, pStar)
          (doubledFieldOfScalarMaximizers a va vStara) :=
      IsDoubledResponseMaximizer.ofAEEq h hAmax
    have hSame :
        DoubledField.SameAE (U := U)
          (doubledFieldOfScalarMaximizers b vb vStarb)
          (doubledFieldOfScalarMaximizers a va vStara) := by
      have hAB := doubledFieldOfScalarMaximizers_sameAE_ofAEEq h va vStara
      simpa [va, vStara] using! doubledSameAE_symm hAB
    exact
      isDoubledResponseMaximizer_of_sameAE U b (p, q) (qStar, pStar)
        hSame hAmax_b
  maximizer_exists := by
    intro P Q
    rcases ha.maximizer_exists P Q with ⟨X, hX⟩
    exact ⟨X, IsDoubledResponseMaximizer.ofAEEq h hX⟩
  maximizer_unique_ae := by
    intro P Q X Y hX hY
    exact ha.maximizer_unique_ae P Q X Y
      (IsDoubledResponseMaximizer.ofAEEq h.symm hX)
      (IsDoubledResponseMaximizer.ofAEEq h.symm hY)
  maximizer_add_sameAE := by
    intro P1 Q1 P2 Q2 X12 X1 X2 h12 h1 h2
    exact
      ha.maximizer_add_sameAE P1 Q1 P2 Q2 X12 X1 X2
        (IsDoubledResponseMaximizer.ofAEEq h.symm h12)
        (IsDoubledResponseMaximizer.ofAEEq h.symm h1)
        (IsDoubledResponseMaximizer.ofAEEq h.symm h2)
  maximizer_smul_sameAE := by
    intro c P Q Xc X hc hX
    exact
      ha.maximizer_smul_sameAE c P Q Xc X
        (IsDoubledResponseMaximizer.ofAEEq h.symm hc)
        (IsDoubledResponseMaximizer.ofAEEq h.symm hX)
  first_variation := by
    intro P Q S T hS hT
    have hSa : IsDoubledResponseMaximizer U a P Q S :=
      IsDoubledResponseMaximizer.ofAEEq h.symm hS
    have hTa : IsDoubledResponseField U a T :=
      IsDoubledResponseField.ofAEEq h.symm hT
    have hFirstA := ha.first_variation P Q S T hSa hTa
    change
      average U (doubledResponseFirstVariationLeft U b P Q T) =
        average U (doubledResponseFirstVariationRight U b S T)
    calc
      average U (doubledResponseFirstVariationLeft U b P Q T) =
          average U (doubledResponseFirstVariationLeft U a P Q T) := by
        exact (doubledResponseFirstVariationLeft_average_eq_ofAEEq h P Q T).symm
      _ = average U (doubledResponseFirstVariationRight U a S T) := hFirstA
      _ = average U (doubledResponseFirstVariationRight U b S T) := by
        exact doubledResponseFirstVariationRight_average_eq_ofAEEq h S T

theorem doubledResponseTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    DoubledResponseTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : DoubledResponseTheory U b :=
    doubledResponseTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact doubledResponseTheory_ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
