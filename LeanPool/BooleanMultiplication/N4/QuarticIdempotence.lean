/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticAnnihilator

/-!
# ANF bridge for the quartic idempotence equation

Only the nine quartic coordinates used by the rational-annihilator
certificate are projected.  Their product formula is proved on the
`7 × 3` target/rational basis and extended bilinearly.  This avoids a dense
representation of all 210 coordinates of `Λ⁴(F₂⁸)`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Extract a designated quartic-annihilator coefficient from an ANF. -/
@[expose]
def anfQuarticAnnihilatorProbe (p : ANF 8) (k : Fin 9) : F₂ :=
  let ijkl := quarticAnnihilatorCoord k
  anfFourProjection p ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2

/-- One quartic-annihilator coefficient projection as a linear map. -/
@[expose]
def anfQuarticAnnihilatorProbeLinear (k : Fin 9) : ANF 8 →ₗ[F₂] F₂ where
  toFun := fun p => anfQuarticAnnihilatorProbe p k
  map_add' p q := by
    simp [anfQuarticAnnihilatorProbe, map_add, Pi.add_apply]
  map_smul' a p := by
    simp [anfQuarticAnnihilatorProbe, map_smul, Pi.smul_apply]

@[simp] theorem anfQuarticAnnihilatorProbeLinear_apply
    (k : Fin 9) (p : ANF 8) :
    anfQuarticAnnihilatorProbeLinear k p =
      anfQuarticAnnihilatorProbe p k := rfl

@[simp] theorem anfQuarticAnnihilatorProbe_add
    (p q : ANF 8) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (p + q) k =
      anfQuarticAnnihilatorProbe p k + anfQuarticAnnihilatorProbe q k := by
  simp [anfQuarticAnnihilatorProbe, map_add, Pi.add_apply]

@[simp] theorem anfQuarticAnnihilatorProbe_smul
    (a : F₂) (p : ANF 8) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (a • p) k =
      a • anfQuarticAnnihilatorProbe p k := by
  simp [anfQuarticAnnihilatorProbe, map_smul, Pi.smul_apply]

/-- The squarefree monomial underlying a quartic-annihilator coordinate. -/
@[expose]
def quarticAnnihilatorSet (k : Fin 9) : Finset (Fin 8) :=
  let ijkl := quarticAnnihilatorCoord k
  {ijkl.1, ijkl.2.1, ijkl.2.2.1, ijkl.2.2.2}

@[simp] theorem quarticAnnihilatorSet_card (k : Fin 9) :
    (quarticAnnihilatorSet k).card = 4 := by
  fin_cases k <;> decide

@[simp] theorem anfQuarticAnnihilatorProbe_monomial
    (s : Finset (Fin 8)) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (monomial s) k =
      if s = quarticAnnihilatorSet k then 1 else 0 := by
  change
    (if (quarticAnnihilatorSet k).card = 4 then
      (monomial s).coeff ⟨quarticAnnihilatorSet k⟩ else 0) = _
  rw [quarticAnnihilatorSet_card]
  simp [coeff_monomial]

theorem anfQuarticAnnihilatorProbe_monomial_mul
    (s t : Finset (Fin 8)) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (monomial s * monomial t) k =
      if s ∪ t = quarticAnnihilatorSet k then 1 else 0 := by
  simp [monomial_mul]

private theorem targetANF_targetBasis (s : Fin 7) :
    targetANF (targetBasis s) = Mul 4 s := by
  simp [targetANF, targetBasis_apply]

private theorem anfQuarticAnnihilatorProbe_target_mul
    (c d : TargetCoeff) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (targetANF c * targetANF d) k =
      ∑ u : Fin 4, ∑ v : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        (c (hankelIndex i j) * d (hankelIndex u v)) •
          (if targetPair i j ∪ targetPair u v = quarticAnnihilatorSet k
            then (1 : F₂) else 0) := by
  change anfQuarticAnnihilatorProbeLinear k _ = _
  rw [targetANF_eq_double_sum, targetANF_eq_double_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul,
    anfQuarticAnnihilatorProbeLinear_apply, anfQuarticAnnihilatorProbe_monomial_mul]

private theorem anfQuarticAnnihilatorProbe_basis_zero_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 0 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 0) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_zero_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 0 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 0) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_zero_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 0 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 0) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_one_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 1 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 1) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_one_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 1 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 1) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_one_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 1 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 1) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_two_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 2 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 2) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_two_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 2 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 2) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_two_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 2 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 2) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_three_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 3 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 3) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_three_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 3 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 3) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_three_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 3 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 3) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_four_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 4 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 4) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_four_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 4 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 4) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_four_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 4 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 4) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_five_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 5 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 5) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_five_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 5 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 5) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_five_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 5 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 5) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_six_zero
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 6 * targetANF (rationalPlaceCoeff 0)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 6) (rationalSingleton 0) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_six_one
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 6 * targetANF (rationalPlaceCoeff 1)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 6) (rationalSingleton 1) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_six_two
    (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 6 * targetANF (rationalPlaceCoeff 2)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 6) (rationalSingleton 2) k := by
  rw [← targetANF_targetBasis, anfQuarticAnnihilatorProbe_target_mul]
  simp only [targetBasis, Pi.basisFun_apply, smul_eq_mul]
  revert k
  decide +kernel

private theorem anfQuarticAnnihilatorProbe_basis_zero
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 0 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 0) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_zero_zero k
  · exact anfQuarticAnnihilatorProbe_basis_zero_one k
  · exact anfQuarticAnnihilatorProbe_basis_zero_two k

private theorem anfQuarticAnnihilatorProbe_basis_one
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 1 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 1) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_one_zero k
  · exact anfQuarticAnnihilatorProbe_basis_one_one k
  · exact anfQuarticAnnihilatorProbe_basis_one_two k

private theorem anfQuarticAnnihilatorProbe_basis_two
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 2 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 2) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_two_zero k
  · exact anfQuarticAnnihilatorProbe_basis_two_one k
  · exact anfQuarticAnnihilatorProbe_basis_two_two k

private theorem anfQuarticAnnihilatorProbe_basis_three
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 3 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 3) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_three_zero k
  · exact anfQuarticAnnihilatorProbe_basis_three_one k
  · exact anfQuarticAnnihilatorProbe_basis_three_two k

private theorem anfQuarticAnnihilatorProbe_basis_four
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 4 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 4) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_four_zero k
  · exact anfQuarticAnnihilatorProbe_basis_four_one k
  · exact anfQuarticAnnihilatorProbe_basis_four_two k

private theorem anfQuarticAnnihilatorProbe_basis_five
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 5 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 5) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_five_zero k
  · exact anfQuarticAnnihilatorProbe_basis_five_one k
  · exact anfQuarticAnnihilatorProbe_basis_five_two k

private theorem anfQuarticAnnihilatorProbe_basis_six
    (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 6 * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis 6) (rationalSingleton theta) k := by
  fin_cases theta
  · exact anfQuarticAnnihilatorProbe_basis_six_zero k
  · exact anfQuarticAnnihilatorProbe_basis_six_one k
  · exact anfQuarticAnnihilatorProbe_basis_six_two k

private theorem anfQuarticAnnihilatorProbe_basis
    (s : Fin 7) (theta : Fin 3) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (Mul 4 s * targetANF (rationalPlaceCoeff theta)) k =
      quarticAnnihilatorCoeffProbe
        (targetBasis s) (rationalSingleton theta) k := by
  fin_cases s
  · exact anfQuarticAnnihilatorProbe_basis_zero theta k
  · exact anfQuarticAnnihilatorProbe_basis_one theta k
  · exact anfQuarticAnnihilatorProbe_basis_two theta k
  · exact anfQuarticAnnihilatorProbe_basis_three theta k
  · exact anfQuarticAnnihilatorProbe_basis_four theta k
  · exact anfQuarticAnnihilatorProbe_basis_five theta k
  · exact anfQuarticAnnihilatorProbe_basis_six theta k

theorem anfQuarticAnnihilatorProbe_target_mul_rational
    (c : TargetCoeff) (delta : Fin 3 → F₂) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (targetANF c * rationalANF delta) k =
      quarticAnnihilatorCoeffProbe c delta k := by
  rw [targetANF, rationalANF_eq_sum]
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.mul_sum, mul_smul_comm]
  change anfQuarticAnnihilatorProbeLinear k _ = _
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [anfQuarticAnnihilatorProbeLinear_apply]
  calc
    (∑ theta : Fin 3, delta theta *
        ∑ s : Fin 7, c s *
          anfQuarticAnnihilatorProbe
            (Mul 4 s * targetANF (rationalPlaceCoeff theta)) k) =
        ∑ theta : Fin 3, delta theta *
          ∑ s : Fin 7, c s * quarticAnnihilatorCoeffProbe
            (targetBasis s) (rationalSingleton theta) k := by
      apply Finset.sum_congr rfl
      intro theta _
      apply congrArg (fun z => delta theta * z)
      apply Finset.sum_congr rfl
      intro s _
      rw [anfQuarticAnnihilatorProbe_basis]
    _ = quarticAnnihilatorCoeffProbe c delta k := by
      fin_cases k <;>
        simp [quarticAnnihilatorCoeffProbe, rationalSingleton, targetBasis, Pi.basisFun,
          Fin.sum_univ_succ] <;>
        ring

end

end N4
end UnrestrictedBooleanMul
