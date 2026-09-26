/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedOneStepContraction

/-! # Annealed Improvement -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# One annealed improvement step

This file formalizes the scalar iteration step from Section 5.5.  The first
bridge below is a windowed version of the Section 5.4 pigeonhole lemma,
obtained by applying the existing result to the scale-normalized law.
-/

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
  nlinarith [section53CoarseFluctuationBetaCoreParams_pos params]

/-- Pigeonhole on an arbitrary scale window `[k, k + M]`.

Either there is a good subwindow of length `h`, or the annealed contrast has
already contracted from scale `k` to scale `k + M`. -/
theorem windowPigeonhole_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta sigma : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1 / 2)
    {k M h : ℕ}
    (hsep : (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)) * h ≤ M) :
    (∃ n : ℕ,
      k + h ≤ n ∧ n ≤ k + M ∧
      hP.barSigmaAtScale hStruct ((n - h : ℕ) : ℤ) ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (n : ℤ) ∧
      (hP.barSigmaStarAtScale hStruct ((n - h : ℕ) : ℤ))⁻¹ ≤
        (1 + delta) *
          (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹) ∨
    thetaAtScale hP hStruct ((k + M : ℕ) : ℤ) ≤
      sigma * thetaAtScale hP hStruct (k : ℤ) := by
  classical
  let Pk := Ch04.restrictionScaleNormalizedLaw k P
  let hPk := hP.scaleNormalized k
  let hStructPk := hStruct.scaleNormalized k
  let hP4k := hP4.scaleNormalized hP hStruct k
  have hpigeon :=
    Section54.pigeonhole_homogenizationScale
      hPk hStructPk hP4k hdelta_pos hdelta_le hsigma_pos hsigma_le hsep
  rcases hpigeon with hgood | hcontract
  · left
    rcases hgood with ⟨j, hhj, hjM, hupper, hlower⟩
    refine ⟨k + j, ?_, ?_, ?_, ?_⟩
    · exact Nat.add_le_add_left hhj k
    · exact Nat.add_le_add_left hjM k
    · have hleft :
          hPk.barSigmaAtScale hStructPk ((j - h : ℕ) : ℤ) =
            hP.barSigmaAtScale hStruct (((k + (j - h : ℕ)) : ℕ) : ℤ) := by
        simpa [hPk, hStructPk] using
          hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k (j - h)
      have hright :
          hPk.barSigmaAtScale hStructPk (j : ℤ) =
            hP.barSigmaAtScale hStruct (((k + j) : ℕ) : ℤ) := by
        simpa [hPk, hStructPk] using
          hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k j
      have hsub : k + (j - h) = k + j - h := by omega
      simpa [hleft, hright, hsub] using hupper
    · have hleft :
          hPk.barSigmaStarAtScale hStructPk ((j - h : ℕ) : ℤ) =
            hP.barSigmaStarAtScale hStruct (((k + (j - h : ℕ)) : ℕ) : ℤ) := by
        simpa [hPk, hStructPk] using
          hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k (j - h)
      have hright :
          hPk.barSigmaStarAtScale hStructPk (j : ℤ) =
            hP.barSigmaStarAtScale hStruct (((k + j) : ℕ) : ℤ) := by
        simpa [hPk, hStructPk] using
          hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k j
      have hsub : k + (j - h) = k + j - h := by omega
      simpa [hleft, hright, hsub] using hlower
  · right
    have hM :
        hPk.thetaAtScale hStructPk (M : ℤ) =
          hP.thetaAtScale hStruct ((k + M : ℕ) : ℤ) := by
      simpa [hPk, hStructPk] using
        hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct k M
    have h0 :
        hPk.thetaAtScale hStructPk (0 : ℤ) =
          hP.thetaAtScale hStruct (k : ℤ) := by
      simpa [hPk, hStructPk] using
        hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct k 0
    simpa [thetaAtScale_eq, hM, h0] using hcontract

private theorem rpow_three_neg_mul_antitone_nat
    {β : ℝ} (hβ : 0 < β) {h l : ℕ} (hl : h ≤ l) :
    Real.rpow (3 : ℝ) (-β * (l : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (h : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hcast : (h : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  exact mul_le_mul_of_nonpos_left hcast (neg_nonpos.mpr hβ.le)

private theorem thetaAtScale_le_of_le_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {n m : ℕ} (hnm : n ≤ m) :
    thetaAtScale hP hStruct (m : ℤ) ≤
      thetaAtScale hP hStruct (n : ℤ) := by
  have hchain := Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hnm
  have hupper :
      hP.barSigmaAtScale hStruct (m : ℤ) ≤
        hP.barSigmaAtScale hStruct (n : ℤ) := hchain.2.2
  have hlower :
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤
        (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ := hchain.2.1
  have hlower_nonneg :
      0 ≤ (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    (Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4 hP hStruct hP4 m).le
  have hupper_nonneg :
      0 ≤ hP.barSigmaAtScale hStruct (n : ℤ) :=
    (Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 n).le
  have hprod := mul_le_mul hupper hlower hlower_nonneg hupper_nonneg
  simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using hprod

private theorem one_le_thetaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    1 ≤ thetaAtScale hP hStruct (m : ℤ) := by
  simpa [thetaAtScale_eq] using
    Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m

private theorem widetildeThetaAtScale_nonneg
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) :
    0 ≤ widetildeThetaAtScale P m hP4 := by
  unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos)

private theorem log_two_add_mul_le_const_mul_log_two_add
    {A x : ℝ} (hA : 1 ≤ A) (hx : 0 ≤ x) :
    Real.log (2 + x * A) ≤ (1 + 2 * A) * Real.log (2 + x) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hxarg_pos : 0 < 2 + x :=
    add_pos_of_pos_of_nonneg (by norm_num) hx
  have hleft_pos : 0 < 2 + x * A :=
    add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hx hA_pos.le)
  have harg_le : 2 + x * A ≤ A * (2 + x) := by
    calc
      2 + x * A ≤ 2 * A + x * A := by
        have htwo_le : (2 : ℝ) ≤ 2 * A := by
          simpa using
            mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right htwo_le (x * A)
      _ = A * (2 + x) := by ring
  have hlog_le :
      Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) :=
    Real.log_le_log hleft_pos harg_le
  have hmul_log :
      Real.log (A * (2 + x)) = Real.log A + Real.log (2 + x) := by
    rw [Real.log_mul hA_pos.ne' hxarg_pos.ne']
  have hlogA_le : Real.log A ≤ A := Real.log_le_self hA_pos.le
  have hlog_two_le : Real.log 2 ≤ Real.log (2 + x) := by
    exact Real.log_le_log (by norm_num) (le_add_of_nonneg_right hx)
  have hone_le_two_log : (1 : ℝ) ≤ 2 * Real.log (2 + x) := by
    have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact htwo.trans (mul_le_mul_of_nonneg_left hlog_two_le (by norm_num))
  have hA_le : A ≤ 2 * A * Real.log (2 + x) := by
    calc
      A = A * 1 := by ring
      _ ≤ A * (2 * Real.log (2 + x)) :=
        mul_le_mul_of_nonneg_left hone_le_two_log hA_pos.le
      _ = 2 * A * Real.log (2 + x) := by ring
  calc
    Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) := hlog_le
    _ = Real.log A + Real.log (2 + x) := hmul_log
    _ ≤ 2 * A * Real.log (2 + x) + Real.log (2 + x) := by
      exact add_le_add (hlogA_le.trans hA_le) le_rfl
    _ = (1 + 2 * A) * Real.log (2 + x) := by ring

private theorem natCeil_le_three_mul_of_half_le {x : ℝ} (hx : (2 : ℝ)⁻¹ ≤ x) :
    (Nat.ceil x : ℝ) ≤ 3 * x := by
  have hx_nonneg : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹).trans hx
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx_nonneg).le
  have htail : x + 1 ≤ 3 * x := by
    have hone_le_two_mul : (1 : ℝ) ≤ 2 * x := by
      calc
        (1 : ℝ) = 2 * (2 : ℝ)⁻¹ := by norm_num
        _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx (by norm_num)
    calc
      x + 1 ≤ x + 2 * x := add_le_add le_rfl hone_le_two_mul
      _ = 3 * x := by ring
  exact hceil.trans htail

private theorem rpow_three_neg_mul_le_inv_of_log_gap
    {β A : ℝ} {h : ℕ} (hβ : 0 < β) (hA : 1 ≤ A)
    (hh : (β * Real.log 3)⁻¹ * Real.log A ≤ (h : ℝ)) :
    Real.rpow (3 : ℝ) (-β * (h : ℝ)) ≤ A⁻¹ := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hβlog : 0 < β * Real.log 3 := mul_pos hβ hlog3
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlogA_nonneg : 0 ≤ Real.log A := Real.log_nonneg hA
  have hmain : Real.log A ≤ β * Real.log 3 * (h : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hh hβlog.le
    have hcancel : β * Real.log 3 * ((β * Real.log 3)⁻¹ * Real.log A) =
        Real.log A := by
      field_simp [hβlog.ne']
    rw [← hcancel]
    exact hmul
  have hexp :
      Real.log (3 : ℝ) * (-β * (h : ℝ)) ≤ -Real.log A := by
    calc
      Real.log (3 : ℝ) * (-β * (h : ℝ)) =
          -(β * Real.log 3 * (h : ℝ)) := by ring
      _ ≤ -Real.log A := neg_le_neg hmain
  calc
    Real.rpow (3 : ℝ) (-β * (h : ℝ)) =
        Real.exp (Real.log (3 : ℝ) * (-β * (h : ℝ))) := by
        simpa using
          (Real.rpow_def_of_pos (x := (3 : ℝ))
            (y := -β * (h : ℝ)) (by norm_num : 0 < (3 : ℝ)))
    _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr hexp
    _ = A⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hA_pos]

/-- The core Section 5.5 improvement step with the auxiliary gap `h` and
smallness conditions left explicit.

The final note-facing lemma will choose `δ` and `h` from `σ`; this theorem
locks down the mathematical iteration once those scalar choices are supplied. -/
theorem oneStepAnnealedImprovement_homogenizationScale_of_auxiliary
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta sigma : ℝ}, 0 < delta → delta ≤ 1 / 2 →
        0 < sigma → sigma ≤ 1 / 2 →
      ∀ {k M h : ℕ},
        (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)) * h ≤ M →
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (h : ℝ) →
        C * Real.rpow delta (1 / 4 : ℝ) ≤ sigma / 2 →
        C * Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBetaParams params) * (h : ℝ)) *
            widetildeThetaAtScale P (0 : ℤ) hP4 ≤ sigma / 2 →
        thetaAtScale hP hStruct ((k + M + h : ℕ) : ℤ) ≤
          1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by
  obtain ⟨Cstep, hCstep_pos, hCstep⟩ :=
    shiftedOneStepContraction_homogenizationScale (d := d) params
  have hβpos : 0 < section53CoarseFluctuationBetaParams params :=
    section53CoarseFluctuationBetaParams_pos params
  obtain ⟨Cshift, hCshift_nonneg, hCshift⟩ :=
    shiftedWidetildeThetaBound_homogenizationScale
      (d := d) params.xi (section53CoarseFluctuationBetaParams params) hβpos
  let C : ℝ := max Cstep Cshift
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCstep_pos (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams delta sigma hdelta_pos hdelta_le
    hsigma_pos hsigma_le k M h hpigeon hsep hsmall_delta hsmall_tail
  have hxi : hP4.xi = params.xi := by
    simp [← hparams]
  have hβeq :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hCstep_le_C : Cstep ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hCshift_le_C : Cshift ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hW0_nonneg : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_nonneg P hP4 0
  have hlog_nonneg :
      0 ≤ Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
        widetildeThetaAtScale P (0 : ℤ) hP4) := by
    apply Real.log_nonneg
    have harg_nonneg :
        0 ≤ delta⁻¹ * (params.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4 := by
      have hdelta_inv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta_pos.le
      have hxi_nonneg : 0 ≤ (params.xi : ℝ) := by positivity
      positivity
    nlinarith
  have hsep_step :
      Cstep * (params.xi : ℝ) *
        Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
          widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (h : ℝ) := by
    have hxi_nonneg : 0 ≤ (params.xi : ℝ) := by positivity
    exact
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCstep_le_C hxi_nonneg) hlog_nonneg).trans hsep
  have htail_at_le {l : ℕ} (hl : h ≤ l) :
      Cshift * Real.rpow (3 : ℝ)
          (-(section53CoarseFluctuationBetaParams params) * (l : ℝ)) *
          widetildeThetaAtScale P (0 : ℤ) hP4 ≤ sigma / 2 := by
    have hdecay := rpow_three_neg_mul_antitone_nat hβpos hl
    have hcoefficient := mul_le_mul_of_nonneg_right hCshift_le_C
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ))
        (-(section53CoarseFluctuationBetaParams params) * (l : ℝ)))
    exact (mul_le_mul_of_nonneg_right
      (hcoefficient.trans (mul_le_mul_of_nonneg_left hdecay hC_pos.le))
      hW0_nonneg).trans hsmall_tail
  have hdelta_at_le :
      Cstep * Real.rpow delta (1 / 4 : ℝ) ≤ sigma / 2 := by
    have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / 4 : ℝ) :=
      Real.rpow_nonneg hdelta_pos.le _
    exact (mul_le_mul_of_nonneg_right hCstep_le_C hdelta_pow_nonneg).trans
      hsmall_delta
  have hwindow :=
    windowPigeonhole_homogenizationScale hP hStruct hP4 hdelta_pos hdelta_le
      hsigma_pos hsigma_le (k := k) (M := M) (h := h) hpigeon
  let F : ℕ := k + M + h
  rcases hwindow with hgood | hcontract
  · rcases hgood with ⟨n, hkhn, hnM, hgood_upper, hgood_lower⟩
    have hnh_le_n : n - h ≤ n := Nat.sub_le n h
    have hsep_good :
        Cstep * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤
            ((n - (n - h) : ℕ) : ℝ) := by
      have hn_sub : n - (n - h) = h := by omega
      simpa [hn_sub] using hsep_step
    have hlocal :=
      hCstep hP hStruct hP4 hparams hdelta_pos hdelta_le hnh_le_n
        hsep_good hgood_upper hgood_lower
    have hk_le_nh : k ≤ n - h := by omega
    have htheta_nh_le_k :
        thetaAtScale hP hStruct ((n - h : ℕ) : ℤ) ≤
          thetaAtScale hP hStruct (k : ℤ) :=
      thetaAtScale_le_of_le_P4 hP hStruct hP4 hk_le_nh
    have htheta_k_nonneg : 0 ≤ thetaAtScale hP hStruct (k : ℤ) :=
      le_trans zero_le_one (one_le_thetaAtScale_of_P4 hP hStruct hP4 k)
    have htheta_n_le :
        thetaAtScale hP hStruct (n : ℤ) ≤
          1 + (sigma / 2) * thetaAtScale hP hStruct (k : ℤ) := by
      calc
        thetaAtScale hP hStruct (n : ℤ)
            ≤ 1 + Cstep * Real.rpow delta (1 / 4 : ℝ) *
                thetaAtScale hP hStruct ((n - h : ℕ) : ℤ) := hlocal
        _ ≤ 1 + (sigma / 2) *
                thetaAtScale hP hStruct ((n - h : ℕ) : ℤ) := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_right hdelta_at_le
                  (le_trans zero_le_one
                    (one_le_thetaAtScale_of_P4 hP hStruct hP4 (n - h))))
        _ ≤ 1 + (sigma / 2) * thetaAtScale hP hStruct (k : ℤ) := by
              have hsigma_half_nonneg : 0 ≤ sigma / 2 := by positivity
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left htheta_nh_le_k hsigma_half_nonneg)
    have hnF : n ≤ F := by
      dsimp [F]
      omega
    have hshift := hCshift hP hStruct hP4 hxi hβeq (k := n) (n := F) hnF
    have htail_F :
        Cshift *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBetaParams params) *
                ((F - n : ℕ) : ℝ)) *
            widetildeThetaAtScale P (0 : ℤ) hP4 ≤ sigma / 2 := by
      have hh_le : h ≤ F - n := by
        dsimp [F]
        omega
      exact htail_at_le hh_le
    calc
      thetaAtScale hP hStruct (F : ℤ)
          ≤ shiftedWidetildeThetaAtScale P (F : ℤ) hP4
              (2 * section53CoarseFluctuationBetaParams params) := by
            simpa [F] using hshift.1
      _ ≤ thetaAtScale hP hStruct (n : ℤ) +
            Cshift *
              Real.rpow (3 : ℝ)
                (-(section53CoarseFluctuationBetaParams params) *
                  ((F - n : ℕ) : ℝ)) *
              widetildeThetaAtScale P (0 : ℤ) hP4 := by
            simpa [F] using hshift.2
      _ ≤ (1 + (sigma / 2) * thetaAtScale hP hStruct (k : ℤ)) +
            sigma / 2 := add_le_add htheta_n_le htail_F
      _ ≤ 1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by
            have hhalf_le :
                sigma / 2 ≤ (sigma / 2) * thetaAtScale hP hStruct (k : ℤ) := by
              have hone := one_le_thetaAtScale_of_P4 hP hStruct hP4 k
              have hsigma_half_nonneg : 0 ≤ sigma / 2 := by positivity
              simpa using mul_le_mul_of_nonneg_left hone hsigma_half_nonneg
            calc
              (1 + (sigma / 2) * thetaAtScale hP hStruct (k : ℤ)) +
                    sigma / 2
                  ≤ (1 + (sigma / 2) * thetaAtScale hP hStruct (k : ℤ)) +
                    (sigma / 2) * thetaAtScale hP hStruct (k : ℤ) :=
                add_le_add le_rfl hhalf_le
              _ = 1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by ring
  · have hshift := hCshift hP hStruct hP4 hxi hβeq
      (k := k + M) (n := F) (by dsimp [F]; omega)
    have htail_F :
        Cshift *
            Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBetaParams params) *
                ((F - (k + M) : ℕ) : ℝ)) *
            widetildeThetaAtScale P (0 : ℤ) hP4 ≤ sigma / 2 := by
      have hh_le : h ≤ F - (k + M) := by
        dsimp [F]
        omega
      exact htail_at_le hh_le
    calc
      thetaAtScale hP hStruct (F : ℤ)
          ≤ shiftedWidetildeThetaAtScale P (F : ℤ) hP4
              (2 * section53CoarseFluctuationBetaParams params) := by
            simpa [F] using hshift.1
      _ ≤ thetaAtScale hP hStruct ((k + M : ℕ) : ℤ) +
            Cshift *
              Real.rpow (3 : ℝ)
                (-(section53CoarseFluctuationBetaParams params) *
                  ((F - (k + M) : ℕ) : ℝ)) *
              widetildeThetaAtScale P (0 : ℤ) hP4 := by
            simpa [F] using hshift.2
      _ ≤ sigma * thetaAtScale hP hStruct (k : ℤ) + sigma / 2 :=
            add_le_add hcontract htail_F
      _ ≤ 1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by
            have hsigma_half_le_one : sigma / 2 ≤ 1 := by
              calc
                sigma / 2 ≤ (1 / 2 : ℝ) / 2 :=
                  div_le_div_of_nonneg_right hsigma_le (by norm_num)
                _ ≤ 1 := by norm_num
            calc
              sigma * thetaAtScale hP hStruct (k : ℤ) + sigma / 2
                  ≤ sigma * thetaAtScale hP hStruct (k : ℤ) + 1 :=
                add_le_add le_rfl hsigma_half_le_one
              _ = 1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by ring

/-- The auxiliary improvement step restated with the final endpoint `N` and
the exact discrete gap condition used in the manuscript proof. -/
theorem oneStepAnnealedImprovement_homogenizationScale_of_discrete_gap
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {delta sigma : ℝ}, 0 < delta → delta ≤ 1 / 2 →
        0 < sigma → sigma ≤ 1 / 2 →
      ∀ {k N h : ℕ}, k ≤ N →
        (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|) + 1) * h ≤ N - k →
        C * (params.xi : ℝ) *
          Real.log (2 + delta⁻¹ * (params.xi : ℝ) *
            widetildeThetaAtScale P (0 : ℤ) hP4) ≤ (h : ℝ) →
        C * Real.rpow delta (1 / 4 : ℝ) ≤ sigma / 2 →
        C * Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBetaParams params) * (h : ℝ)) *
            widetildeThetaAtScale P (0 : ℤ) hP4 ≤ sigma / 2 →
        thetaAtScale hP hStruct (N : ℤ) ≤
          1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    oneStepAnnealedImprovement_homogenizationScale_of_auxiliary (d := d) params
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams delta sigma hdelta_pos hdelta_le
    hsigma_pos hsigma_le k N h hkN hgap hsep hsmall_delta hsmall_tail
  let r : ℕ := Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)
  let M : ℕ := N - k - h
  have hgap_add : r * h + h ≤ N - k := by
    have hgap_one : (1 + r) * h ≤ N - k := by
      simpa [r, add_comm] using hgap
    have hone : (1 + r) * h = r * h + h := by
      rw [Nat.add_mul, one_mul, add_comm]
    simpa [hone] using hgap_one
  have hh_le_Nk : h ≤ N - k :=
    le_trans (Nat.le_add_left h (r * h)) hgap_add
  have hpigeon : r * h ≤ M := by
    dsimp [M]
    exact Nat.le_sub_of_add_le hgap_add
  have hfinal : k + M + h = N := by
    have hMh : M + h = N - k := by
      dsimp [M]
      exact Nat.sub_add_cancel hh_le_Nk
    calc
      k + M + h = k + (M + h) := by omega
      _ = k + (N - k) := by rw [hMh]
      _ = N := Nat.add_sub_of_le hkN
  have haux :=
    hC hP hStruct hP4 hparams hdelta_pos hdelta_le hsigma_pos hsigma_le
      (k := k) (M := M) (h := h) (by simpa [r] using hpigeon)
      hsep hsmall_delta hsmall_tail
  simpa [hfinal] using haux

private theorem oneStepAnnealedImprovement_scalar_discreteInputs
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {C0 : ℝ} (hC0_pos : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma T : ℝ}, 0 < sigma → sigma ≤ 1 / 2 → 0 ≤ T →
      ∀ {k N : ℕ},
        C * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) * |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) ≤
          ((N - k : ℕ) : ℝ) →
        ∃ delta : ℝ, ∃ h : ℕ,
          0 < delta ∧
          delta ≤ 1 / 2 ∧
          (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|) + 1) * h ≤ N - k ∧
          C0 * (params.xi : ℝ) *
              Real.log (2 + delta⁻¹ * (params.xi : ℝ) * T) ≤ (h : ℝ) ∧
          C0 * Real.rpow delta (1 / 4 : ℝ) ≤ sigma / 2 ∧
          C0 * Real.rpow (3 : ℝ)
              (-(section53CoarseFluctuationBetaParams params) * (h : ℝ)) *
              T ≤ sigma / 2 := by
  let B : ℝ := max C0 1
  let β : ℝ := section53CoarseFluctuationBetaParams params
  let D : ℝ := max B ((β * Real.log 3)⁻¹)
  let Aconst : ℝ := (2 * B) ^ (4 : ℕ)
  let Klog : ℝ := 1 + 2 * Aconst
  let C : ℝ := max (30 * D * Aconst * Klog) 1
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hB_ge_C0 : C0 ≤ B := by dsimp [B]; exact le_max_left _ _
  have hB_ge_one : 1 ≤ B := by dsimp [B]; exact le_max_right _ _
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBetaParams_pos params
  have hlog3_pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hβlog_pos : 0 < β * Real.log 3 := mul_pos hβ_pos hlog3_pos
  have hD_ge_B : B ≤ D := by dsimp [D]; exact le_max_left _ _
  have hD_ge_inv : (β * Real.log 3)⁻¹ ≤ D := by
    dsimp [D]
    exact le_max_right _ _
  have hD_pos : 0 < D := lt_of_lt_of_le hB_pos hD_ge_B
  have hAconst_pos : 0 < Aconst := by
    dsimp [Aconst]
    positivity
  have hAconst_ge_one : 1 ≤ Aconst := by
    dsimp [Aconst]
    have htwoB : 1 ≤ 2 * B := by
      calc
        (1 : ℝ) ≤ 2 * 1 := by norm_num
        _ ≤ 2 * B := mul_le_mul_of_nonneg_left hB_ge_one (by norm_num)
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) htwoB 4
  have hKlog_pos : 0 < Klog := by
    dsimp [Klog]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (by norm_num) hAconst_pos.le)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro sigma T hsigma_pos hsigma_le hT_nonneg k N hgap
  let ξ : ℝ := (params.xi : ℝ)
  let sigInv4 : ℝ := sigma⁻¹ ^ (4 : ℕ)
  let x : ℝ := sigma / (2 * B)
  let delta : ℝ := x ^ (4 : ℕ)
  let Aδ : ℝ := 2 + delta⁻¹ * ξ * T
  let Bσ : ℝ := 2 + sigInv4 * ξ * T
  let H : ℝ := D * ξ * Real.log Aδ
  let h : ℕ := Nat.ceil H
  change C * ξ * sigInv4 * |Real.log sigma| * Real.log Bσ ≤
    ((N - k : ℕ) : ℝ) at hgap
  have hξ_ge_one : 1 ≤ ξ := by
    dsimp [ξ]
    exact_mod_cast (Nat.succ_le_of_lt params.xi_pos)
  have hξ_nonneg : 0 ≤ ξ := le_trans zero_le_one hξ_ge_one
  have hsig_nonneg : 0 ≤ sigma := hsigma_pos.le
  have hsigInv4_nonneg : 0 ≤ sigInv4 := by
    dsimp [sigInv4]
    positivity
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hx_le_half : x ≤ 1 / 2 := by
    dsimp [x]
    have hden_pos : 0 < 2 * B := by positivity
    have hden_ge_two : (2 : ℝ) ≤ 2 * B :=
      by
        simpa using
          mul_le_mul_of_nonneg_left hB_ge_one (by norm_num : (0 : ℝ) ≤ 2)
    have hinv_le : (2 * B)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden_ge_two
    calc
      sigma / (2 * B) = sigma * (2 * B)⁻¹ := by ring
      _ ≤ sigma * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv_le hsigma_pos.le
      _ ≤ (1 / 2 : ℝ) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hsigma_le (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hx_le_one : x ≤ 1 := hx_le_half.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact pow_pos hx_pos 4
  have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
  have hdelta_le_x : delta ≤ x := by
    have hx3_le_one : x ^ (3 : ℕ) ≤ 1 := pow_le_one₀ hx_nonneg hx_le_one
    calc
      delta = x * x ^ (3 : ℕ) := by
        dsimp [delta]
        ring
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx3_le_one hx_nonneg
      _ = x := by ring
  have hdelta_le : delta ≤ 1 / 2 := hdelta_le_x.trans hx_le_half
  have hdelta_inv_eq : delta⁻¹ = Aconst * sigInv4 := by
    dsimp [delta, x, Aconst, sigInv4]
    field_simp [hsigma_pos.ne', hB_pos.ne']
  have hAδ_ge_two : 2 ≤ Aδ := by
    have hprod : 0 ≤ delta⁻¹ * ξ * T := by positivity
    dsimp [Aδ]
    exact le_add_of_nonneg_right hprod
  have hAδ_ge_one : 1 ≤ Aδ :=
    (by norm_num : (1 : ℝ) ≤ 2).trans hAδ_ge_two
  have hAδ_pos : 0 < Aδ := lt_of_lt_of_le zero_lt_one hAδ_ge_one
  have hBσ_ge_two : 2 ≤ Bσ := by
    have hprod : 0 ≤ sigInv4 * ξ * T := by positivity
    dsimp [Bσ]
    exact le_add_of_nonneg_right hprod
  have hBσ_pos : 0 < Bσ :=
    (by norm_num : (0 : ℝ) < 2).trans_le hBσ_ge_two
  have hlogAδ_nonneg : 0 ≤ Real.log Aδ := Real.log_nonneg hAδ_ge_one
  have hlogBσ_nonneg : 0 ≤ Real.log Bσ :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans hBσ_ge_two)
  have hAδ_log_le :
      Real.log Aδ ≤ Klog * Real.log Bσ := by
    have hAδ_le : Aδ ≤ 2 + (sigInv4 * ξ * T) * Aconst := by
      calc
        Aδ = 2 + (sigInv4 * ξ * T) * Aconst := by
          dsimp [Aδ]
          rw [hdelta_inv_eq]
          ring
        _ ≤ 2 + (sigInv4 * ξ * T) * Aconst := le_rfl
    have hleft :=
      Real.log_le_log hAδ_pos hAδ_le
    have hcomp :=
      log_two_add_mul_le_const_mul_log_two_add
        (A := Aconst) (x := sigInv4 * ξ * T) hAconst_ge_one
        (by positivity)
    calc
      Real.log Aδ ≤ Real.log (2 + (sigInv4 * ξ * T) * Aconst) := hleft
      _ ≤ (1 + 2 * Aconst) * Real.log (2 + sigInv4 * ξ * T) := hcomp
      _ = Klog * Real.log Bσ := by simp [Klog, Bσ]
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hceilH : H ≤ (h : ℝ) := by
    simpa [h] using Nat.le_ceil H
  have hsep_aux :
      C0 * ξ * Real.log Aδ ≤ (h : ℝ) := by
    have hC0_le_D : C0 ≤ D := hB_ge_C0.trans hD_ge_B
    calc
      C0 * ξ * Real.log Aδ ≤ D * ξ * Real.log Aδ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC0_le_D hξ_nonneg) hlogAδ_nonneg
      _ = H := by simp [H]
      _ ≤ (h : ℝ) := hceilH
  have hdelta_root :
      Real.rpow delta (1 / 4 : ℝ) = x := by
    have hroot :=
      Real.pow_rpow_inv_natCast hx_nonneg (by norm_num : (4 : ℕ) ≠ 0)
    simpa [delta, one_div, x] using hroot
  have hsmall_delta :
      C0 * Real.rpow delta (1 / 4 : ℝ) ≤ sigma / 2 := by
    calc
      C0 * Real.rpow delta (1 / 4 : ℝ) = C0 * x := by rw [hdelta_root]
      _ ≤ B * x := mul_le_mul_of_nonneg_right hB_ge_C0 hx_nonneg
      _ = sigma / 2 := by
        dsimp [x]
        field_simp [hB_pos.ne']
  have hT_le_delta_Aδ : T ≤ delta * Aδ := by
    have hcore : delta⁻¹ * T ≤ Aδ := by
      have hξT : delta⁻¹ * T ≤ delta⁻¹ * ξ * T := by
        have hδinv_nonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta_nonneg
        have hT_le_ξT : T ≤ ξ * T :=
          calc
            T = 1 * T := by ring
            _ ≤ ξ * T := mul_le_mul_of_nonneg_right hξ_ge_one hT_nonneg
        calc
          delta⁻¹ * T ≤ delta⁻¹ * (ξ * T) :=
            mul_le_mul_of_nonneg_left hT_le_ξT hδinv_nonneg
          _ = delta⁻¹ * ξ * T := by ring
      dsimp [Aδ]
      exact le_trans hξT (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
    have hmul := mul_le_mul_of_nonneg_left hcore hdelta_nonneg
    have hcancel : delta * (delta⁻¹ * T) = T := by
      field_simp [hdelta_pos.ne']
    rw [hcancel] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdecay_le :
      Real.rpow (3 : ℝ) (-(β) * (h : ℝ)) ≤ Aδ⁻¹ := by
    apply rpow_three_neg_mul_le_inv_of_log_gap hβ_pos hAδ_ge_one
    calc
      (β * Real.log 3)⁻¹ * Real.log Aδ ≤ D * Real.log Aδ :=
        mul_le_mul_of_nonneg_right hD_ge_inv hlogAδ_nonneg
      _ ≤ D * ξ * Real.log Aδ := by
        calc
          D * Real.log Aδ = 1 * (D * Real.log Aδ) := by ring
          _ ≤ ξ * (D * Real.log Aδ) := by
              exact mul_le_mul_of_nonneg_right hξ_ge_one
                (mul_nonneg hD_pos.le hlogAδ_nonneg)
          _ = D * ξ * Real.log Aδ := by ring
      _ = H := by ring
      _ ≤ (h : ℝ) := hceilH
  have hsmall_tail :
      C0 * Real.rpow (3 : ℝ) (-(β) * (h : ℝ)) * T ≤ sigma / 2 := by
    have hdecay_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-(β) * (h : ℝ)) :=
      Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hAinvT_le_delta : Aδ⁻¹ * T ≤ delta := by
      have hmul := mul_le_mul_of_nonneg_left hT_le_delta_Aδ (inv_nonneg.mpr hAδ_pos.le)
      have hcancel : Aδ⁻¹ * (delta * Aδ) = delta := by
        field_simp [hAδ_pos.ne']
      rw [hcancel] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    calc
      C0 * Real.rpow (3 : ℝ) (-(β) * (h : ℝ)) * T
          ≤ B * Real.rpow (3 : ℝ) (-(β) * (h : ℝ)) * T := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hB_ge_C0 hdecay_nonneg) hT_nonneg
      _ ≤ B * Aδ⁻¹ * T := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdecay_le hB_pos.le) hT_nonneg
      _ = B * (Aδ⁻¹ * T) := by ring
      _ ≤ B * delta := mul_le_mul_of_nonneg_left hAinvT_le_delta hB_pos.le
      _ ≤ B * x := mul_le_mul_of_nonneg_left hdelta_le_x hB_pos.le
      _ = sigma / 2 := by
        dsimp [x]
        field_simp [hB_pos.ne']
  let R : ℝ := 2 * delta⁻¹ * |Real.log sigma|
  have hlog_sigma_nonpos : Real.log sigma ≤ 0 :=
    Real.log_nonpos hsigma_pos.le
      (hsigma_le.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have habs_log_ge : (2 : ℝ)⁻¹ ≤ |Real.log sigma| := by
    have hlog_half : Real.log sigma ≤ Real.log (1 / 2 : ℝ) := by
      exact Real.log_le_log hsigma_pos hsigma_le
    have hlog_inv : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      rw [Real.log_inv]
    have hlog2_half : (2 : ℝ)⁻¹ ≤ Real.log 2 :=
      (by norm_num : (2 : ℝ)⁻¹ ≤ 0.6931471803).trans
        Real.log_two_gt_d9.le
    have hneg : Real.log 2 ≤ -Real.log sigma := by linarith
    rw [abs_of_nonpos hlog_sigma_nonpos]
    exact hlog2_half.trans hneg
  have hdelta_inv_ge_two : 2 ≤ delta⁻¹ := by
    have hdelta_le_one_half : delta ≤ 1 / 2 := hdelta_le
    have hinv : (1 / 2 : ℝ)⁻¹ ≤ delta⁻¹ :=
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 2) hdelta_pos).2
        hdelta_le_one_half
    norm_num at hinv ⊢
    exact hinv
  have hR_ge_two : 2 ≤ R := by
    have hmul_ge_one : 1 ≤ delta⁻¹ * |Real.log sigma| := by
      calc
        (1 : ℝ) = 2 * (2 : ℝ)⁻¹ := by norm_num
        _ ≤ delta⁻¹ * |Real.log sigma| :=
            mul_le_mul hdelta_inv_ge_two habs_log_ge
              (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
              (by linarith)
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (delta⁻¹ * |Real.log sigma|) :=
          mul_le_mul_of_nonneg_left hmul_ge_one (by norm_num)
      _ = R := by
          simp [R]
          ring
  have hR_half : (2 : ℝ)⁻¹ ≤ R :=
    (by norm_num : (2 : ℝ)⁻¹ ≤ 2).trans hR_ge_two
  have hR_nonneg : 0 ≤ R :=
    (by norm_num : (0 : ℝ) ≤ 2).trans hR_ge_two
  have hR_ge_one : 1 ≤ R :=
    (by norm_num : (1 : ℝ) ≤ 2).trans hR_ge_two
  have hH_half : (2 : ℝ)⁻¹ ≤ H := by
    have hlog2_le : Real.log 2 ≤ Real.log Aδ :=
      Real.log_le_log (by norm_num) hAδ_ge_two
    have hhalf_log2 : (2 : ℝ)⁻¹ ≤ Real.log 2 := by
      exact (by norm_num : (2 : ℝ)⁻¹ ≤ 0.6931471803).trans
        Real.log_two_gt_d9.le
    calc
      (2 : ℝ)⁻¹ ≤ Real.log 2 := hhalf_log2
      _ ≤ Real.log Aδ := hlog2_le
      _ ≤ D * ξ * Real.log Aδ := by
        have hDξ_ge_one : 1 ≤ D * ξ := by
          have hD_ge_one : 1 ≤ D := hB_ge_one.trans hD_ge_B
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ D * ξ := mul_le_mul hD_ge_one hξ_ge_one
                (by norm_num) (by linarith)
        exact le_mul_of_one_le_left hlogAδ_nonneg hDξ_ge_one
      _ = H := by ring
  have hrceil : ((Nat.ceil R + 1 : ℕ) : ℝ) ≤ 5 * R := by
    have hr : (Nat.ceil R : ℝ) ≤ 3 * R :=
      natCeil_le_three_mul_of_half_le hR_half
    have hone : (1 : ℝ) ≤ 2 * R := by
      calc
        (1 : ℝ) ≤ 2 * 1 := by norm_num
        _ ≤ 2 * R := mul_le_mul_of_nonneg_left hR_ge_one (by norm_num)
    calc
      ((Nat.ceil R + 1 : ℕ) : ℝ) = (Nat.ceil R : ℝ) + 1 := by norm_num
      _ ≤ 3 * R + 2 * R := add_le_add hr hone
      _ = 5 * R := by ring
  have hhceil : (h : ℝ) ≤ 3 * H := by
    change (Nat.ceil H : ℝ) ≤ 3 * H
    exact natCeil_le_three_mul_of_half_le hH_half
  have hR_le :
      R ≤ 2 * Aconst * sigInv4 * |Real.log sigma| := by
    dsimp [R]
    rw [hdelta_inv_eq]
    ring_nf
    exact le_rfl
  have hH_le :
      H ≤ D * ξ * Klog * Real.log Bσ := by
    dsimp [H]
    calc
      D * ξ * Real.log Aδ ≤ D * ξ * (Klog * Real.log Bσ) := by
        exact mul_le_mul_of_nonneg_left hAδ_log_le
          (mul_nonneg hD_pos.le hξ_nonneg)
      _ = D * ξ * Klog * Real.log Bσ := by ring
  have hprod_cast :
      (((Nat.ceil R + 1) * h : ℕ) : ℝ) ≤
        30 * D * Aconst * Klog * ξ * sigInv4 *
          |Real.log sigma| * Real.log Bσ := by
    calc
      (((Nat.ceil R + 1) * h : ℕ) : ℝ)
          = ((Nat.ceil R + 1 : ℕ) : ℝ) * (h : ℝ) := by norm_num
      _ ≤ (5 * R) * (3 * H) := by
            exact mul_le_mul hrceil hhceil (by positivity) (by positivity)
      _ ≤ (5 * (2 * Aconst * sigInv4 * |Real.log sigma|)) *
            (3 * (D * ξ * Klog * Real.log Bσ)) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hR_le (by norm_num))
              (mul_le_mul_of_nonneg_left hH_le (by norm_num))
              (mul_nonneg (by norm_num) hH_nonneg)
              (by positivity)
      _ = 30 * D * Aconst * Klog * ξ * sigInv4 *
            |Real.log sigma| * Real.log Bσ := by ring
  have hC_gap :
      30 * D * Aconst * Klog * ξ * sigInv4 *
          |Real.log sigma| * Real.log Bσ ≤
        C * ξ * sigInv4 * |Real.log sigma| * Real.log Bσ := by
    have hbase_le_C : 30 * D * Aconst * Klog ≤ C := by
      dsimp [C]
      exact le_max_left _ _
    have htail_nonneg :
        0 ≤ ξ * sigInv4 * |Real.log sigma| * Real.log Bσ := by positivity
    calc
      30 * D * Aconst * Klog * ξ * sigInv4 *
          |Real.log sigma| * Real.log Bσ
          = (30 * D * Aconst * Klog) *
              (ξ * sigInv4 * |Real.log sigma| * Real.log Bσ) := by ring
        _ ≤ C * (ξ * sigInv4 * |Real.log sigma| * Real.log Bσ) :=
              mul_le_mul_of_nonneg_right hbase_le_C htail_nonneg
        _ = C * ξ * sigInv4 * |Real.log sigma| * Real.log Bσ := by ring
  have hgap_nat :
      (Nat.ceil R + 1) * h ≤ N - k := by
    have hcast :
        (((Nat.ceil R + 1) * h : ℕ) : ℝ) ≤ ((N - k : ℕ) : ℝ) :=
      hprod_cast.trans (hC_gap.trans hgap)
    exact Nat.cast_le.mp hcast
  refine ⟨delta, h, hdelta_pos, hdelta_le, ?_, ?_, hsmall_delta, ?_⟩
  · simpa [R] using hgap_nat
  · simpa [Aδ, ξ] using hsep_aux
  · simpa [β] using hsmall_tail

/-- One improvement step for the annealed scalar contrast.

This is the note-facing Section 5.5 form, with the constant chosen from the
parameter record before the law, the window, and `σ`.  The Lean statement uses
`(σ⁻¹)^4` for the manuscript factor `σ^{-4}`. -/
theorem oneStepAnnealedImprovement_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {sigma : ℝ}, 0 < sigma → sigma ≤ 1 / 2 →
      ∀ {k N : ℕ}, k ≤ N →
        C * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) * |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) *
              widetildeThetaAtScale P (0 : ℤ) hP4) ≤ ((N - k : ℕ) : ℝ) →
        thetaAtScale hP hStruct (N : ℤ) ≤
          1 + sigma * thetaAtScale hP hStruct (k : ℤ) := by
  obtain ⟨C0, hC0_pos, hC0⟩ :=
    oneStepAnnealedImprovement_homogenizationScale_of_discrete_gap (d := d) params
  obtain ⟨C, hC_pos, hCscalar⟩ :=
    oneStepAnnealedImprovement_scalar_discreteInputs (d := d) params hC0_pos
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams sigma hsigma_pos hsigma_le k N hkN hgap
  have hT_nonneg :
      0 ≤ widetildeThetaAtScale P (0 : ℤ) hP4 :=
    widetildeThetaAtScale_nonneg P hP4 0
  obtain ⟨delta, h, hdelta_pos, hdelta_le, hgap_nat, hsep_aux,
      hsmall_delta, hsmall_tail⟩ :=
    hCscalar (sigma := sigma) (T := widetildeThetaAtScale P (0 : ℤ) hP4)
      hsigma_pos hsigma_le hT_nonneg (k := k) (N := N) hgap
  exact
    hC0 hP hStruct hP4 hparams hdelta_pos hdelta_le hsigma_pos hsigma_le
      hkN hgap_nat hsep_aux hsmall_delta hsmall_tail

end

end Section55
end Ch05
end Book
end Homogenization
