/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.Final

/-! # Shifted One Step Contraction -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem section53CoarseFluctuationBetaCoreParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaCoreParams params := by
  have hgap : 0 < 1 - params.sUpper - params.sLower := by
    linarith [params.sum_lt_one]
  have hupper : 0 < params.sUpper := params.sUpper_pos
  have hlower : 0 < params.sLower := params.sLower_pos
  have hupper_gain : 0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sUpper]
  have hlower_gain : 0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCoreParams
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

private theorem section53CoarseFluctuationBetaParams_pos {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams
  exact div_pos (section53CoarseFluctuationBetaCoreParams_pos params) (by norm_num)

private theorem section53CoarseFluctuationBetaCoreParams_le_sum_gap {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    section53CoarseFluctuationBetaCoreParams params ≤
      1 - params.sUpper - params.sLower := by
  unfold section53CoarseFluctuationBetaCoreParams
  exact min_le_left _ _

private theorem betaShiftedParams_sUpper_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    params.sUpper + section53CoarseFluctuationBetaParams params < 1 := by
  have hcore_le := section53CoarseFluctuationBetaCoreParams_le_sum_gap params
  have hcore_pos := section53CoarseFluctuationBetaCoreParams_pos params
  have hlower_nonneg := params.sLower_nonneg
  unfold section53CoarseFluctuationBetaParams
  linarith

private theorem betaShiftedParams_sLower_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    params.sLower + section53CoarseFluctuationBetaParams params < 1 := by
  have hcore_le := section53CoarseFluctuationBetaCoreParams_le_sum_gap params
  have hcore_pos := section53CoarseFluctuationBetaCoreParams_pos params
  have hupper_nonneg := params.sUpper_nonneg
  unfold section53CoarseFluctuationBetaParams
  linarith

private theorem betaShiftedParams_sum_lt_one {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (params.sUpper + section53CoarseFluctuationBetaParams params) +
        (params.sLower + section53CoarseFluctuationBetaParams params) < 1 := by
  have hcore_le := section53CoarseFluctuationBetaCoreParams_le_sum_gap params
  have hcore_pos := section53CoarseFluctuationBetaCoreParams_pos params
  unfold section53CoarseFluctuationBetaParams
  linarith

/-- Parameter-only `(P4)` data with both regularity exponents shifted by the
Section 5.3/5.5 exponent `β`. -/
def betaShiftedParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := params.sUpper + section53CoarseFluctuationBetaParams params
  sLower := params.sLower + section53CoarseFluctuationBetaParams params
  xi := params.xi
  two_le_dim := params.two_le_dim
  sUpper_nonneg :=
    add_nonneg params.sUpper_nonneg
      (section53CoarseFluctuationBetaParams_pos params).le
  sUpper_lt_one := betaShiftedParams_sUpper_lt_one params
  sLower_nonneg :=
    add_nonneg params.sLower_nonneg
      (section53CoarseFluctuationBetaParams_pos params).le
  sLower_lt_one := betaShiftedParams_sLower_lt_one params
  xi_gt_two_mul_dim := params.xi_gt_two_mul_dim
  sum_lt_one := betaShiftedParams_sum_lt_one params
  dim_div_xi_lt_min := by
    rw [lt_min_iff]
    constructor
    · linarith [params.dim_div_xi_lt_sUpper,
        section53CoarseFluctuationBetaParams_pos params]
    · linarith [params.dim_div_xi_lt_sLower,
        section53CoarseFluctuationBetaParams_pos params]

@[simp]
theorem betaShiftedP4_params {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (betaShiftedP4 hP hStruct hP4).params = betaShiftedParams hP4.params := rfl

/-- Shifted one-step contraction on a window `[k,n]`, with the local shifted
moment budget at scale `k` left explicit.

This is the direct dilation of Section 5.4 after shifting the `(P4)`
exponents by one `β`.  The constant is chosen from the parameter-only data
before the law and the window. -/
theorem shiftedOneStepContraction_homogenizationScale_of_local_shifted_budget
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta : ℝ}, 0 < delta → delta ≤ 1 / 2 →
      ∀ {k n : ℕ}, k ≤ n →
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params)) ≤
            ((n - k : ℕ) : ℝ) →
        hP.barSigmaAtScale hStruct (k : ℤ) ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (n : ℤ) →
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
          (1 + delta) * (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ →
        thetaAtScale hP hStruct (n : ℤ) ≤
          1 + C * Real.rpow delta (1 / 4 : ℝ) *
            thetaAtScale hP hStruct (k : ℤ) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    Section54.OneStepContraction.oneStepContraction_homogenizationScale
      (betaShiftedParams params)
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams delta hdelta_pos hdelta_le k n hkn hsep
    hgood_upper hgood_lower
  let Pk := Ch04.restrictionScaleNormalizedLaw k P
  let hPk := hP.scaleNormalized k
  let hStructPk := hStruct.scaleNormalized k
  let hP4k := hP4.scaleNormalized hP hStruct k
  let hP4kβ := betaShiftedP4 hPk hStructPk hP4k
  let m : ℕ := n - k
  have hβeq :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hparamsβ : hP4kβ.params = betaShiftedParams params := by
    calc
      hP4kβ.params = betaShiftedParams hP4k.params := by
        simp [hP4kβ]
      _ = betaShiftedParams hP4.params := rfl
      _ = betaShiftedParams params := by rw [hparams]
  have hW :
      widetildeThetaAtScale Pk (0 : ℤ) hP4kβ =
        shiftedWidetildeThetaAtScale P (k : ℤ) hP4
          (section53CoarseFluctuationBetaParams params) := by
    have hβeq_k :
        section53CoarseFluctuationBeta hP4k =
          section53CoarseFluctuationBetaParams params := by
      simpa [hP4k, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using! hβeq
    have hshift :=
      shiftedWidetildeThetaAtScale_restrictionScaleNormalizedLaw hP hStruct hP4
        (η := section53CoarseFluctuationBetaParams params)
        (by
          have hβpos : 0 < section53CoarseFluctuationBetaParams params := by
            simpa [← hβeq] using section53CoarseFluctuationBeta_pos hP4
          linarith [hP4.sUpper_pos])
        (by
          have hβpos : 0 < section53CoarseFluctuationBetaParams params := by
            simpa [← hβeq] using section53CoarseFluctuationBeta_pos hP4
          linarith [hP4.sLower_pos])
        k 0
    simpa [Pk, hP4k, hP4kβ, betaShiftedP4, hβeq,
      hβeq_k, shiftedWidetildeThetaAtScale] using hshift
  have hsep_k :
      C * ((betaShiftedParams params).xi : ℝ) *
        Real.log (2 + delta⁻¹ * ((betaShiftedParams params).xi : ℝ) *
          widetildeThetaAtScale Pk (0 : ℤ) hP4kβ) ≤ (m : ℝ) := by
    rw [hW]
    simpa [m, betaShiftedParams] using hsep
  have hgood_upper_k :
      hPk.barSigmaAtScale hStructPk (0 : ℤ) ≤
        (1 + delta) * hPk.barSigmaAtScale hStructPk (m : ℤ) := by
    have h0 :
        hPk.barSigmaAtScale hStructPk (0 : ℤ) =
          hP.barSigmaAtScale hStruct (k : ℤ) := by
      simpa [hPk, hStructPk] using
        hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k 0
    have hm :
        hPk.barSigmaAtScale hStructPk (m : ℤ) =
          hP.barSigmaAtScale hStruct (n : ℤ) := by
      simpa [hPk, hStructPk, m, Nat.add_sub_of_le hkn] using
        hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k m
    simpa [h0, hm] using hgood_upper
  have hgood_lower_k :
      (hPk.barSigmaStarAtScale hStructPk (0 : ℤ))⁻¹ ≤
        (1 + delta) * (hPk.barSigmaStarAtScale hStructPk (m : ℤ))⁻¹ := by
    have h0 :
        hPk.barSigmaStarAtScale hStructPk (0 : ℤ) =
          hP.barSigmaStarAtScale hStruct (k : ℤ) := by
      simpa [hPk, hStructPk] using
        hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k 0
    have hm :
        hPk.barSigmaStarAtScale hStructPk (m : ℤ) =
          hP.barSigmaStarAtScale hStruct (n : ℤ) := by
      simpa [hPk, hStructPk, m, Nat.add_sub_of_le hkn] using
        hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k m
    simpa [h0, hm] using hgood_lower
  have hlocal :=
    hC hPk hStructPk hP4kβ hparamsβ hdelta_pos hdelta_le
      (m := m) hsep_k hgood_upper_k hgood_lower_k
  have htheta0 :
      hPk.thetaAtScale hStructPk (0 : ℤ) =
        hP.thetaAtScale hStruct (k : ℤ) := by
    simpa [hPk, hStructPk] using
      hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct k 0
  have hthetam :
      hPk.thetaAtScale hStructPk (m : ℤ) =
        hP.thetaAtScale hStruct (n : ℤ) := by
    simpa [hPk, hStructPk, m, Nat.add_sub_of_le hkn] using
      hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct k m
  simpa [htheta0, hthetam] using hlocal

private theorem widetildeThetaAtScale_nonneg
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) :
    0 ≤ widetildeThetaAtScale P m hP4 := by
  unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos)

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

private theorem log_two_add_mul_le_const_mul_log_two_add
    {A x : ℝ} (hA : 1 ≤ A) (hx : 0 ≤ x) :
    Real.log (2 + x * A) ≤ (1 + 2 * A) * Real.log (2 + x) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hxarg_pos : 0 < 2 + x := by positivity
  have hleft_pos : 0 < 2 + x * A := by positivity
  have harg_le : 2 + x * A ≤ A * (2 + x) := by
    have htwo_le_twoA : (2 : ℝ) ≤ 2 * A := by linarith
    calc
      2 + x * A = x * A + 2 := by ring
      _ ≤ x * A + 2 * A := add_le_add_right htwo_le_twoA (x * A)
      _ = 2 * A + x * A := by ring
      _ = A * (2 + x) := by ring
  have hlog_le :
      Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) :=
    Real.log_le_log hleft_pos harg_le
  have hmul_log :
      Real.log (A * (2 + x)) = Real.log A + Real.log (2 + x) := by
    rw [Real.log_mul hA_pos.ne' hxarg_pos.ne']
  have hlogA_le : Real.log A ≤ A := Real.log_le_self hA_pos.le
  have hlog_two_le : Real.log 2 ≤ Real.log (2 + x) := by
    have htwo_le : (2 : ℝ) ≤ 2 + x := by
      simpa using add_le_add_left hx (2 : ℝ)
    exact Real.log_le_log (by norm_num) htwo_le
  have hone_le_two_log : (1 : ℝ) ≤ 2 * Real.log (2 + x) := by
    have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact htwo.trans (mul_le_mul_of_nonneg_left hlog_two_le (by norm_num))
  have hA_le : A ≤ 2 * A * Real.log (2 + x) := by
    have hmul := mul_le_mul_of_nonneg_right hone_le_two_log hA_pos.le
    calc
      A = 1 * A := by ring
      _ ≤ (2 * Real.log (2 + x)) * A := hmul
      _ = 2 * A * Real.log (2 + x) := by ring
  calc
    Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) := hlog_le
    _ = Real.log A + Real.log (2 + x) := hmul_log
    _ ≤ 2 * A * Real.log (2 + x) + Real.log (2 + x) := by
      calc
        Real.log A + Real.log (2 + x) = Real.log (2 + x) + Real.log A := by ring
        _ ≤ Real.log (2 + x) + 2 * A * Real.log (2 + x) :=
          add_le_add_right (hlogA_le.trans hA_le) (Real.log (2 + x))
        _ = 2 * A * Real.log (2 + x) + Real.log (2 + x) := by ring
    _ = (1 + 2 * A) * Real.log (2 + x) := by ring

/-- Shifted one-step contraction with the global scale-zero moment budget.

The constant is chosen from the parameter-only `(P4)` data before the law,
the scale window, and `δ`. -/
theorem shiftedOneStepContraction_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta : ℝ}, 0 < delta → delta ≤ 1 / 2 →
      ∀ {k n : ℕ}, k ≤ n →
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤
            ((n - k : ℕ) : ℝ) →
        hP.barSigmaAtScale hStruct (k : ℤ) ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (n : ℤ) →
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ ≤
          (1 + delta) * (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ →
        thetaAtScale hP hStruct (n : ℤ) ≤
          1 + C * Real.rpow delta (1 / 4 : ℝ) *
            thetaAtScale hP hStruct (k : ℤ) := by
  obtain ⟨Cstep, hCstep_pos, hCstep⟩ :=
    shiftedOneStepContraction_homogenizationScale_of_local_shifted_budget
      (d := d) params
  have hβpos : 0 < section53CoarseFluctuationBetaParams params :=
    section53CoarseFluctuationBetaParams_pos params
  obtain ⟨Cshift, hCshift_nonneg, hCshift⟩ :=
    shiftedWidetildeThetaAtScale_shifted_bound_homogenizationScale
      (d := d) params.xi (section53CoarseFluctuationBetaParams params) hβpos
  let A : ℝ := 1 + Cshift
  let L : ℝ := 1 + 2 * A
  let C : ℝ := max (Cstep * L) Cstep
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    linarith
  have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA_ge_one
  have hL_ge_one : 1 ≤ L := by
    dsimp [L]
    linarith
  have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCstep_pos (le_max_right _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams delta hdelta_pos hdelta_le k n hkn hsep
    hgood_upper hgood_lower
  have hxi : hP4.xi = params.xi := by
    simp [← hparams]
  have hβeq :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hW0_nonneg : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_nonneg P hP4 0
  have htheta0_le :
      thetaAtScale hP hStruct 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    thetaAtScale_zero_le_widetildeThetaAtScale_zero hP hStruct hP4
  have hlocal_shift :=
    hCshift hP hStruct hP4 hxi hβeq (k := 0) (n := k) (Nat.zero_le k)
  let decay0k : ℝ :=
    Real.rpow (3 : ℝ)
      (-(section53CoarseFluctuationBetaParams params) * ((k - 0 : ℕ) : ℝ))
  have hdecay0k_nonneg : 0 ≤ decay0k := by
    dsimp [decay0k]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hdecay0k_le_one : decay0k ≤ 1 := by
    dsimp [decay0k]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3) ?_
    have hk_nonneg : 0 ≤ ((k - 0 : ℕ) : ℝ) := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβpos.le) hk_nonneg
  have hSβk :
      shiftedWidetildeThetaAtScale P (k : ℤ) hP4
          (section53CoarseFluctuationBetaParams params) ≤
        A * widetildeThetaAtScale P 0 hP4 := by
    have hterm_le :
        Cshift * decay0k * widetildeThetaAtScale P 0 hP4 ≤
          Cshift * widetildeThetaAtScale P 0 hP4 := by
      have hcoeff_le : Cshift * decay0k ≤ Cshift * 1 :=
        mul_le_mul_of_nonneg_left hdecay0k_le_one hCshift_nonneg
      calc
        Cshift * decay0k * widetildeThetaAtScale P 0 hP4
            ≤ (Cshift * 1) * widetildeThetaAtScale P 0 hP4 :=
              mul_le_mul_of_nonneg_right hcoeff_le hW0_nonneg
        _ = Cshift * widetildeThetaAtScale P 0 hP4 := by ring
    calc
      shiftedWidetildeThetaAtScale P (k : ℤ) hP4
          (section53CoarseFluctuationBetaParams params)
          ≤ thetaAtScale hP hStruct (0 : ℤ) +
              Cshift * decay0k * widetildeThetaAtScale P (0 : ℤ) hP4 := by
            simpa [decay0k] using hlocal_shift
      _ ≤ widetildeThetaAtScale P 0 hP4 +
            Cshift * widetildeThetaAtScale P 0 hP4 := by
          exact add_le_add htheta0_le hterm_le
      _ = A * widetildeThetaAtScale P 0 hP4 := by
          dsimp [A]
          ring
  have harg_nonneg :
      0 ≤ delta⁻¹ * (params.xi : ℝ) * widetildeThetaAtScale P 0 hP4 := by
    have hdelta_inv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta_pos.le
    have hxi_nonneg : 0 ≤ (params.xi : ℝ) := by positivity
    positivity
  have hlog_compare :
      Real.log
          (2 + delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params)) ≤
        L * Real.log
          (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) := by
    let x : ℝ := delta⁻¹ * (params.xi : ℝ) *
      widetildeThetaAtScale P (0 : ℤ) hP4
    have hx : 0 ≤ x := by simpa [x] using harg_nonneg
    have hlocal_arg_le :
        2 + delta⁻¹ * (params.xi : ℝ) *
              shiftedWidetildeThetaAtScale P (k : ℤ) hP4
                (section53CoarseFluctuationBetaParams params) ≤
          2 + x * A := by
      have hcoef_nonneg : 0 ≤ delta⁻¹ * (params.xi : ℝ) := by positivity
      calc
        2 + delta⁻¹ * (params.xi : ℝ) *
              shiftedWidetildeThetaAtScale P (k : ℤ) hP4
                (section53CoarseFluctuationBetaParams params)
            ≤ 2 + delta⁻¹ * (params.xi : ℝ) *
                (A * widetildeThetaAtScale P 0 hP4) := by
              have hmul := mul_le_mul_of_nonneg_left hSβk hcoef_nonneg
              calc
                2 + delta⁻¹ * (params.xi : ℝ) *
                    shiftedWidetildeThetaAtScale P (k : ℤ) hP4
                      (section53CoarseFluctuationBetaParams params)
                    = delta⁻¹ * (params.xi : ℝ) *
                      shiftedWidetildeThetaAtScale P (k : ℤ) hP4
                        (section53CoarseFluctuationBetaParams params) + 2 := by
                      ring
                _ ≤ delta⁻¹ * (params.xi : ℝ) *
                      (A * widetildeThetaAtScale P 0 hP4) + 2 :=
                      add_le_add_left hmul 2
                _ = 2 + delta⁻¹ * (params.xi : ℝ) *
                      (A * widetildeThetaAtScale P 0 hP4) := by ring
        _ = 2 + x * A := by
              dsimp [x]
              ring
    have hleft_pos :
        0 < 2 + delta⁻¹ * (params.xi : ℝ) *
              shiftedWidetildeThetaAtScale P (k : ℤ) hP4
                (section53CoarseFluctuationBetaParams params) := by
      have hS_nonneg :
          0 ≤ shiftedWidetildeThetaAtScale P (k : ℤ) hP4
            (section53CoarseFluctuationBetaParams params) := by
        unfold shiftedWidetildeThetaAtScale Ch04.widetildeThetaAtScale
        exact mul_nonneg
          (Ch04.LambdaMomentAtScale_nonneg P (k : ℤ) hP4.xi
            (by
              have hβp : 0 < section53CoarseFluctuationBetaParams params := hβpos
              linarith [hP4.sUpper_pos]))
          (Ch04.lambdaInvMomentAtScale_nonneg P (k : ℤ) hP4.xi
            (by
              have hβp : 0 < section53CoarseFluctuationBetaParams params := hβpos
              linarith [hP4.sLower_pos]))
      have hcoef_nonneg : 0 ≤ delta⁻¹ * (params.xi : ℝ) := by positivity
      have hprod_nonneg :
          0 ≤ delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params) :=
        mul_nonneg hcoef_nonneg hS_nonneg
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        (by simpa using add_le_add_left hprod_nonneg (2 : ℝ))
    have hmono :=
      Real.log_le_log hleft_pos hlocal_arg_le
    have hconst :=
      log_two_add_mul_le_const_mul_log_two_add (A := A) (x := x)
        hA_ge_one hx
    calc
      Real.log
          (2 + delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params))
          ≤ Real.log (2 + x * A) := hmono
      _ ≤ (1 + 2 * A) * Real.log (2 + x) := hconst
      _ = L * Real.log
          (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) := by
          dsimp [L, x]
  have hsep_local :
      Cstep * (params.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
          shiftedWidetildeThetaAtScale P (k : ℤ) hP4
            (section53CoarseFluctuationBetaParams params)) ≤
          ((n - k : ℕ) : ℝ) := by
    have hlog_nonneg :
        0 ≤ Real.log
          (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) := by
      apply Real.log_nonneg
      exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
        (by simpa using add_le_add_left harg_nonneg (2 : ℝ))
    have hxi_nonneg : 0 ≤ (params.xi : ℝ) := by positivity
    have hleft_le :
        Cstep * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params)) ≤
        (Cstep * L) * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) := by
      calc
        Cstep * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            shiftedWidetildeThetaAtScale P (k : ℤ) hP4
              (section53CoarseFluctuationBetaParams params))
            ≤ Cstep * (params.xi : ℝ) *
                (L * Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
                  widetildeThetaAtScale P (0 : ℤ) hP4)) := by
              exact mul_le_mul_of_nonneg_left hlog_compare
                (mul_nonneg hCstep_pos.le hxi_nonneg)
        _ = (Cstep * L) * (params.xi : ℝ) *
              Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
                widetildeThetaAtScale P (0 : ℤ) hP4) := by ring
    have hCstepL_le_C : Cstep * L ≤ C := by
      dsimp [C]
      exact le_max_left _ _
    have hright_le :
        (Cstep * L) * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCstepL_le_C hxi_nonneg) hlog_nonneg
    exact hleft_le.trans (hright_le.trans hsep)
  have hresult :=
    hCstep hP hStruct hP4 hparams hdelta_pos hdelta_le hkn
      hsep_local hgood_upper hgood_lower
  have hCstep_le_C : Cstep ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have htheta_nonneg : 0 ≤ thetaAtScale hP hStruct (k : ℤ) := by
    have hθ :=
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        (hP.scaleNormalized k) (hStruct.scaleNormalized k)
        (hP4.scaleNormalized hP hStruct k) 0
    have hrewrite := thetaAtScale_zero_restrictionScaleNormalizedLaw hP hStruct k
    have : 1 ≤ thetaAtScale hP hStruct (k : ℤ) := by
      rw [thetaAtScale_eq] at hθ
      change
        1 ≤ (hP.scaleNormalized k).thetaAtScale
          (hStruct.scaleNormalized k) (0 : ℤ) at hθ
      rw [hrewrite] at hθ
      simpa [thetaAtScale_eq] using hθ
    exact le_trans zero_le_one this
  have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / 4 : ℝ) :=
    Real.rpow_nonneg hdelta_pos.le _
  have htail_le :
      Cstep * Real.rpow delta (1 / 4 : ℝ) *
          thetaAtScale hP hStruct (k : ℤ) ≤
        C * Real.rpow delta (1 / 4 : ℝ) *
          thetaAtScale hP hStruct (k : ℤ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCstep_le_C hdelta_pow_nonneg) htheta_nonneg
  calc
    thetaAtScale hP hStruct (n : ℤ)
        ≤ 1 + Cstep * Real.rpow delta (1 / 4 : ℝ) *
            thetaAtScale hP hStruct (k : ℤ) := hresult
    _ ≤ 1 + C * Real.rpow delta (1 / 4 : ℝ) *
            thetaAtScale hP hStruct (k : ℤ) := by
          calc
            1 + Cstep * Real.rpow delta (1 / 4 : ℝ) *
                thetaAtScale hP hStruct (k : ℤ)
                = Cstep * Real.rpow delta (1 / 4 : ℝ) *
                    thetaAtScale hP hStruct (k : ℤ) + 1 := by ring
            _ ≤ C * Real.rpow delta (1 / 4 : ℝ) *
                  thetaAtScale hP hStruct (k : ℤ) + 1 :=
                  add_le_add_left htail_le 1
            _ = 1 + C * Real.rpow delta (1 / 4 : ℝ) *
                  thetaAtScale hP hStruct (k : ℤ) := by ring

end

end Section55
end Ch05
end Book
end Homogenization
