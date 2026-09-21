/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.TwoStep

/-! # Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem thetaAtScale_zero_le_widetildeThetaAtScale_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    thetaAtScale hP hStruct 0 ≤ widetildeThetaAtScale P 0 hP4 := by
  have hBlock :
      ∀ l : ℕ,
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (l : ℤ))) P :=
    fun l => Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hUpperPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (Ch04.LambdaSqCoeffField (originCube d (l : ℤ)) hP4.sUpper (.finite 1) a) ^
              hP4.xi) P :=
    fun l => Section52.upperFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  have hLowerPowInt :
      ∀ l : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((Ch04.lambdaSqCoeffField (originCube d (l : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
              hP4.xi) P :=
    fun l => Section52.lowerFactorPowerIntegrableAtScale_from_P4 hP hStruct hP4 l
  simpa using
    Section52.thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
      hP hStruct hP4 hBlock hUpperPowInt hLowerPowInt 0

private theorem widetildeThetaAtScale_nonneg
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) :
    0 ≤ widetildeThetaAtScale P m hP4 := by
  unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos)

/-- Section 5.5 shifted localization for the high-moment ellipticity contrast.

The constant is chosen after the explicit manuscript parameters `xi` and `β`,
and before the law, structural hypotheses, and window `[k,n]`. -/
theorem shiftedWidetildeThetaBound_homogenizationScale
    {d : ℕ} [NeZero d] (xi : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P),
        hP4.xi = xi →
        section53CoarseFluctuationBeta hP4 = β →
        ∀ {k n : ℕ}, k ≤ n →
          thetaAtScale hP hStruct (n : ℤ) ≤
              shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β) ∧
            shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β) ≤
              thetaAtScale hP hStruct (k : ℤ) +
                C * Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ)) *
                  widetildeThetaAtScale P 0 hP4 := by
  obtain ⟨Cβ, hCβ_nonneg, hCβ⟩ :=
    shiftedWidetildeThetaAtScale_shifted_bound_homogenizationScale
      (d := d) xi β hβ
  obtain ⟨C2β, hC2β_nonneg, hC2β⟩ :=
    twoBetaShiftedWidetildeThetaAtScale_shifted_bound_homogenizationScale
      (d := d) xi β hβ
  let C : ℝ := C2β * (1 + Cβ)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 hxi hβ k n hkn
  constructor
  · have htheta := thetaAtScale_le_twoBetaShiftedWidetildeThetaAtScale hP hStruct hP4 n
    simpa [hβ]
      using htheta
  · have htwo := hC2β hP hStruct hP4 hxi hβ hkn
    have hone :=
      hCβ hP hStruct hP4 hxi hβ (k := 0) (n := k) (Nat.zero_le k)
    let decay0k : ℝ := Real.rpow (3 : ℝ) (-β * ((k - 0 : ℕ) : ℝ))
    let decaykn : ℝ := Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ))
    have hdecay0k_nonneg : 0 ≤ decay0k := by
      dsimp [decay0k]
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hdecay0k_le_one : decay0k ≤ 1 := by
      dsimp [decay0k]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) ?_
      have hk_nonneg : 0 ≤ ((k - 0 : ℕ) : ℝ) := by positivity
      nlinarith
    have hW0_nonneg : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
      widetildeThetaAtScale_nonneg P hP4 0
    have htheta0 : thetaAtScale hP hStruct 0 ≤ widetildeThetaAtScale P 0 hP4 :=
      thetaAtScale_zero_le_widetildeThetaAtScale_zero hP hStruct hP4
    have hSβk :
        shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β ≤
          (1 + Cβ) * widetildeThetaAtScale P 0 hP4 := by
      have hterm_le :
          Cβ * decay0k * widetildeThetaAtScale P 0 hP4 ≤
            Cβ * widetildeThetaAtScale P 0 hP4 := by
        have hcoeff_le : Cβ * decay0k ≤ Cβ * 1 :=
          mul_le_mul_of_nonneg_left hdecay0k_le_one hCβ_nonneg
        calc
          Cβ * decay0k * widetildeThetaAtScale P 0 hP4
              ≤ (Cβ * 1) * widetildeThetaAtScale P 0 hP4 :=
                mul_le_mul_of_nonneg_right hcoeff_le hW0_nonneg
          _ = Cβ * widetildeThetaAtScale P 0 hP4 := by ring
      calc
        shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β
            ≤ thetaAtScale hP hStruct (0 : ℤ) +
                Cβ * decay0k * widetildeThetaAtScale P (0 : ℤ) hP4 := by
              simpa [decay0k] using hone
        _ ≤ widetildeThetaAtScale P 0 hP4 +
              Cβ * widetildeThetaAtScale P 0 hP4 := by
              exact add_le_add htheta0 hterm_le
        _ = (1 + Cβ) * widetildeThetaAtScale P 0 hP4 := by ring
    have hdecaykn_nonneg : 0 ≤ decaykn := by
      dsimp [decaykn]
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hcoeff_nonneg : 0 ≤ C2β * decaykn :=
      mul_nonneg hC2β_nonneg hdecaykn_nonneg
    calc
      shiftedWidetildeThetaAtScale P (n : ℤ) hP4 (2 * β)
          ≤ thetaAtScale hP hStruct (k : ℤ) +
              C2β * decaykn *
                shiftedWidetildeThetaAtScale P (k : ℤ) hP4 β := by
            simpa [decaykn] using htwo
      _ ≤ thetaAtScale hP hStruct (k : ℤ) +
            C2β * decaykn *
              ((1 + Cβ) * widetildeThetaAtScale P 0 hP4) := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hSβk hcoeff_nonneg)
      _ = thetaAtScale hP hStruct (k : ℤ) +
            C * decaykn * widetildeThetaAtScale P 0 hP4 := by
            dsimp [C]
            ring
      _ = thetaAtScale hP hStruct (k : ℤ) +
            C * Real.rpow (3 : ℝ) (-β * ((n - k : ℕ) : ℝ)) *
              widetildeThetaAtScale P 0 hP4 := by
            simp [decaykn]

end

end Section55
end Ch05
end Book
end Homogenization
