/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Seminorms

/-! # Smooth Case -/

namespace Homogenization

open scoped ENNReal

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
private noncomputable def smoothPoincareLpBase
    (hU : IsOpenBoundedConvexDomain U) : ℝ :=
  ((MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) *
    ((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain))

noncomputable def smoothPoincareLpConst
    (hU : IsOpenBoundedConvexDomain U) : ℝ :=
  1 + |smoothPoincareLpBase (d := d) (U := U) hU|

theorem smoothPoincareLpConst_nonneg
    (hU : IsOpenBoundedConvexDomain U) :
    0 ≤ smoothPoincareLpConst (d := d) (U := U) hU := by
  dsimp [smoothPoincareLpConst]
  positivity

private theorem smoothPoincareLpBase_le_const
    (hU : IsOpenBoundedConvexDomain U) :
    smoothPoincareLpBase (d := d) (U := U) hU ≤
      smoothPoincareLpConst (d := d) (U := U) hU := by
  dsimp [smoothPoincareLpConst]
  linarith [le_abs_self (smoothPoincareLpBase (d := d) (U := U) hU)]

theorem subAverageLpSeminorm_le_smoothPoincareLpConst_mul_gradientCoordLpSeminormSum_ofContDiff
    [NeZero d] [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {q : ℝ} (hq : 1 < q)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    let u : W1pFunction U (ENNReal.ofReal q) :=
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU (hf.of_le (by simp))
    u.subAverageLpSeminorm ≤
      smoothPoincareLpConst (d := d) (U := U) hU * u.gradientCoordLpSeminormSum := by
  let pE : ENNReal := ENNReal.ofReal q
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let u : W1pFunction U pE := W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU hf1
  let B : ℝ :=
    (MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))
  let M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  let K : ℝ := smoothPoincareLpBase (d := d) (U := U) hU
  let C : ℝ := smoothPoincareLpConst (d := d) (U := U) hU
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hpE_one : 1 ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (NeZero.pos d)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hK_eq : K = B * M := by
    rfl
  have hK_nonneg : 0 ≤ K := by
    rw [hK_eq]
    exact mul_nonneg hB_nonneg hM_nonneg
  have huInt : MeasureTheory.IntegrableOn f U := by
    have hu_int : MeasureTheory.Integrable u.toFun μ :=
      u.memLp.integrable hpE_one
    simpa [u, pE, hf1, μ, volumeMeasureOn,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain,
      MeasureTheory.IntegrableOn] using hu_int
  have hf_mem : MeasureTheory.MemLp f pE μ := by
    simpa [u, pE, hf1, μ,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using u.memLp
  have hsub_mem :
      MeasureTheory.MemLp (fun x => f x - integralAverage U f) pE μ := by
    have hconst : MeasureTheory.MemLp (fun _ : Vec d => integralAverage U f) pE μ :=
      MeasureTheory.memLp_const (integralAverage U f)
    simpa [Pi.sub_apply] using! hf_mem.sub hconst
  have hfderiv_mem : MeasureTheory.MemLp (fderiv ℝ f) pE μ := by
    simpa [pE, μ] using
      (memLp_fderiv_of_contDiffOnIsOpenBoundedConvexDomain
        (U := U) (p := pE) hU hf1)
  have hleft_norm :
      u.subAverageLpSeminorm =
        (∫ x in U, ‖f x - integralAverage U f‖ ^ q ∂MeasureTheory.volume) ^
          (1 / q : ℝ) := by
    calc
      u.subAverageLpSeminorm =
          ENNReal.toReal
            (MeasureTheory.eLpNorm (fun x => f x - integralAverage U f) pE μ) := by
              simp [W1pFunction.subAverageLpSeminorm, u, pE, μ,
                W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
                W1pFunction.ofContDiffOnIsSobolevRegularDomain]
      _ = (∫ x in U, ‖f x - integralAverage U f‖ ^ q ∂MeasureTheory.volume) ^
          (1 / q : ℝ) := by
            simpa [pE, μ, volumeMeasureOn] using
              (toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
                (μ := μ) (f := fun x => f x - integralAverage U f)
                hq_pos hsub_mem)
  have hderiv_norm :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) pE μ) =
        (∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume) ^ (1 / q : ℝ) := by
    simpa [pE, μ, volumeMeasureOn] using
      (toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        (μ := μ) (f := fderiv ℝ f) hq_pos hfderiv_mem)
  have hpoinc :
      ∫ x in U, ‖f x - integralAverage U f‖ ^ q ∂MeasureTheory.volume ≤
        B ^ q * (M ^ q *
          ∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume) := by
    simpa [B, M] using
      (integral_rpow_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
        (d := d) (U := U) hU huInt hf (p := q) hq hvol)
  have hleft_int_nonneg :
      0 ≤ ∫ x in U, ‖f x - integralAverage U f‖ ^ q ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hderiv_int_nonneg :
      0 ≤ ∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
  have hroot :
      u.subAverageLpSeminorm ≤
        K * ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) pE μ) := by
    rw [hleft_norm, hderiv_norm]
    calc
      (∫ x in U, ‖f x - integralAverage U f‖ ^ q ∂MeasureTheory.volume) ^
          (1 / q : ℝ)
          ≤ (B ^ q * (M ^ q *
              ∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume)) ^
              (1 / q : ℝ) := by
            exact Real.rpow_le_rpow hleft_int_nonneg hpoinc (by positivity)
      _ = K *
          (∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume) ^
            (1 / q : ℝ) := by
            have hBM_nonneg : 0 ≤ B * M := mul_nonneg hB_nonneg hM_nonneg
            have hpow_arg :
                B ^ q * (M ^ q *
                    ∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume) =
                  (B * M) ^ q *
                    ∫ y in U, ‖fderiv ℝ f y‖ ^ q ∂MeasureTheory.volume := by
              rw [Real.mul_rpow hB_nonneg hM_nonneg]
              ring
            rw [hpow_arg]
            rw [Real.mul_rpow (Real.rpow_nonneg hBM_nonneg _) hderiv_int_nonneg]
            rw [← Real.rpow_mul hBM_nonneg]
            have hq_ne : q ≠ 0 := ne_of_gt hq_pos
            rw [show q * (1 / q : ℝ) = 1 by field_simp [hq_ne]]
            simp [hK_eq]
  have hderiv_le_grad :
      ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) pE μ) ≤
        u.gradientCoordLpSeminormSum := by
    simpa [u, pE, hf1, μ] using
      (fderivLpNorm_le_gradientCoordLpSeminormSum_ofContDiffOnIsOpenBoundedConvexDomain
        (U := U) (p := pE) hU hpE_one hf)
  have hK_le_C : K ≤ C := by
    simpa [K, C] using smoothPoincareLpBase_le_const (d := d) (U := U) hU
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using smoothPoincareLpConst_nonneg (d := d) (U := U) hU
  change u.subAverageLpSeminorm ≤ C * u.gradientCoordLpSeminormSum
  calc
    u.subAverageLpSeminorm
        ≤ K * ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) pE μ) := hroot
    _ ≤ C * ENNReal.toReal (MeasureTheory.eLpNorm (fderiv ℝ f) pE μ) := by
          exact mul_le_mul_of_nonneg_right hK_le_C ENNReal.toReal_nonneg
    _ ≤ C * u.gradientCoordLpSeminormSum := by
          exact mul_le_mul_of_nonneg_left hderiv_le_grad hC_nonneg


end W1pFunction

end Homogenization
