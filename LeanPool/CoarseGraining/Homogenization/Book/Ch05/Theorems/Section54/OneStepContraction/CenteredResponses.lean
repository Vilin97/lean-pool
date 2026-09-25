/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.RealAlgebra

/-! # Centered Responses -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Centered-response identities for the one-step contraction

This file proves the Section 5.4 special-vector bridge from the Section 5.2
centered-response identities to the scalar contrast `Theta_m - 1`.
-/

private theorem vecDot_specialP_specialQ_eq_vecNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    vecDot (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e) =
      vecNormSq e := by
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  have hσ_pos : 0 < σ := by
    simpa [σ] using GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  calc
    vecDot (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e) =
        (σ ^ (-(1 / 2 : ℝ)) * σ ^ (1 / 2 : ℝ)) * vecNormSq e := by
          simp [σ, specialPAtScale, specialQAtScale, vecDot_smul_left,
            vecDot_smul_right, vecNormSq, mul_comm, mul_left_comm]
    _ = vecNormSq e := by
      rw [GoodScale.rpow_neg_half_mul_rpow_half_eq_one hσ_pos]
      simp

private theorem centeredResponseExpectationFormula_special_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d) :
    centeredResponseExpectationFormula hP hStruct (m : ℤ)
        (specialPAtScale hP hStruct (m : ℤ) e)
        (specialQAtScale hP hStruct (m : ℤ) e) =
      (1 / 2 : ℝ) * (thetaAtScale hP hStruct (m : ℤ) - 1) *
        vecNormSq e := by
  have hpq := vecDot_specialP_specialQ_eq_vecNormSq hP hStruct hP4 m e
  rw [centeredResponseExpectationFormula_eq, vecDot_smul_right]
  rw [hpq]
  ring

/-- Special-vector centered responses sum to `Theta_m - 1` for vectors with
unit squared norm. -/
theorem thetaAtScale_sub_one_eq_centeredResponses_special_of_vecNormSq_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : vecNormSq e = 1) :
    thetaAtScale hP hStruct (m : ℤ) - 1 =
      expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) +
        expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) := by
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hcent :=
    Section52.centeredResponses_homogenizationScale hP hStruct hP4 m p_e q_e
  have hformula :
      centeredResponseExpectationFormula hP hStruct (m : ℤ) p_e q_e =
        (1 / 2 : ℝ) * (thetaAtScale hP hStruct (m : ℤ) - 1) := by
    have hraw := centeredResponseExpectationFormula_special_eq hP hStruct hP4 m e
    simpa [p_e, q_e, he] using hraw
  calc
    thetaAtScale hP hStruct (m : ℤ) - 1 =
        centeredResponseExpectationFormula hP hStruct (m : ℤ) p_e q_e +
          centeredResponseExpectationFormula hP hStruct (m : ℤ) p_e q_e := by
          rw [hformula]
          ring
    _ =
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e +
          expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ) p_e q_e := by
          rw [hcent.1, hcent.2]

/-- Special-vector centered responses sum to `Theta_m - 1` for unit vectors,
in the same norm convention used by the good-scale theorem. -/
theorem thetaAtScale_sub_one_eq_centeredResponses_special
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : Ch02.vecNorm e = 1) :
    thetaAtScale hP hStruct (m : ℤ) - 1 =
      expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) +
        expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) := by
  exact
    thetaAtScale_sub_one_eq_centeredResponses_special_of_vecNormSq_eq_one
      hP hStruct hP4 m e (GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he)

/-- The centered adjoint response has the same expectation as the centered
primal response.  This is the Section 5.2 identity in a rewrite-friendly form
for the one-step proof. -/
theorem expectedCenteredResponseJStarAtScale_eq_expectedCenteredResponseJAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ)
    (p q : Vec d) :
    expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ) p q =
      expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p q := by
  have hcent :=
    Section52.centeredResponses_homogenizationScale hP hStruct hP4 m p q
  rw [hcent.1, hcent.2]

/-- Special-vector form of the one-step centered-response identity using only
the primal centered response. -/
theorem thetaAtScale_sub_one_eq_two_centeredResponse_special
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) (e : Vec d)
    (he : Ch02.vecNorm e = 1) :
    thetaAtScale hP hStruct (m : ℤ) - 1 =
      2 *
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ)
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) := by
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hsum :=
    thetaAtScale_sub_one_eq_centeredResponses_special hP hStruct hP4 m e he
  have hstar :
      expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ) p_e q_e =
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e :=
    expectedCenteredResponseJStarAtScale_eq_expectedCenteredResponseJAtScale
      hP hStruct hP4 m p_e q_e
  rw [hsum, hstar]
  ring

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
