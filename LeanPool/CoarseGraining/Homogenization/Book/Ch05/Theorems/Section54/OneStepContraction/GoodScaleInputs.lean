/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CenteredResponses

/-! # Good Scale Inputs -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Good-scale inputs for the one-step contraction

This file repackages the public good-scale parameter bounds into the exact
pieces consumed by the one-step contraction proof.
-/

/-- At a good scale, the unit-scale annealed response for the special vectors
is controlled by `sqrt(Theta_0)`. -/
theorem goodScale_J_zero_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    Ch04.annealedResponseJAtScale P (0 : ℤ) p_e q_e ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
  dsimp only
  have hGS :=
    GoodScale.goodScaleParameterBounds_homogenizationScale
      hP hStruct hP4 hdelta_pos hdelta_le m hgood_upper hgood_lower e he
  exact (hGS.2.2.2.2.2 0 (Nat.zero_le m)).1

/-- At a good scale, all lower-scale additivity defects for the special
vectors are controlled by `delta * sqrt(Theta_0)`. -/
theorem goodScale_tau_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m j : ℕ} (hj : j ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    tauAtScale P (m : ℤ) (j : ℤ) p_e q_e ≤
      delta * Real.sqrt (thetaAtScale hP hStruct 0) := by
  dsimp only
  have hGS :=
    GoodScale.goodScaleParameterBounds_homogenizationScale
      hP hStruct hP4 hdelta_pos hdelta_le m hgood_upper hgood_lower e he
  exact (hGS.2.2.2.2.2 j hj).2

/-- Good-scale upper scalar-chain comparison in the normalized variables. -/
theorem goodScale_sigmaHat_inv_barSigma_zero_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        hP.barSigmaAtScale hStruct 0 ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
  have hGS :=
    GoodScale.goodScaleParameterBounds_homogenizationScale
      hP hStruct hP4 hdelta_pos hdelta_le m hgood_upper hgood_lower e he
  exact hGS.2.2.2.1

/-- Good-scale lower scalar-chain comparison in the normalized variables. -/
theorem goodScale_sigmaHat_barSigmaStar_zero_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    sigmaHatAtScale hP hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
      (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) := by
  have hGS :=
    GoodScale.goodScaleParameterBounds_homogenizationScale
      hP hStruct hP4 hdelta_pos hdelta_le m hgood_upper hgood_lower e he
  exact hGS.2.2.2.2.1

/-- The scalar weight multiplying the tau sum is bounded by a harmless
constant times `sqrt(Theta_0)` at a good scale. -/
theorem goodScale_oneStepScalarWeight_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    {m : ℕ}
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
    (e : Vec d) (he : Ch02.vecNorm e = 1) :
    oneStepScalarWeightAtScale hP hStruct m ≤
      3 * Real.sqrt (thetaAtScale hP hStruct 0) := by
  have hupper :=
    goodScale_sigmaHat_inv_barSigma_zero_le
      hP hStruct hP4 hdelta_pos hdelta_le
      hgood_upper hgood_lower e he
  have hlower :=
    goodScale_sigmaHat_barSigmaStar_zero_inv_le
      hP hStruct hP4 hdelta_pos hdelta_le
      hgood_upper hgood_lower e he
  have hsqrt_nonneg : 0 ≤ Real.sqrt (thetaAtScale hP hStruct 0) :=
    Real.sqrt_nonneg _
  calc
    oneStepScalarWeightAtScale hP hStruct m =
        sigmaHatAtScale hP hStruct (m : ℤ) *
            (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
          (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
            hP.barSigmaAtScale hStruct 0 := rfl
    _ ≤
        (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) +
          (1 + delta) * Real.sqrt (thetaAtScale hP hStruct 0) :=
        add_le_add hlower hupper
    _ = (2 * (1 + delta)) * Real.sqrt (thetaAtScale hP hStruct 0) := by
        ring
    _ ≤ 3 * Real.sqrt (thetaAtScale hP hStruct 0) := by
        have hcoeff : 2 * (1 + delta) ≤ 3 := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoeff hsqrt_nonneg

/-- At scale zero, `(P4)` implies `Theta_0 >= 1`. -/
theorem one_le_thetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    1 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
  simpa using GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 0

/-- At scale zero, `sqrt(Theta_0) <= Theta_0`. -/
theorem sqrt_thetaAtScale_zero_le_thetaAtScale_zero_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    Real.sqrt (thetaAtScale hP hStruct (0 : ℤ)) ≤
      thetaAtScale hP hStruct (0 : ℤ) := by
  have htheta := one_le_thetaAtScale_zero_of_P4 hP hStruct hP4
  exact (Real.sqrt_le_iff).2
    ⟨le_trans zero_le_one htheta, by nlinarith [htheta]⟩

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
