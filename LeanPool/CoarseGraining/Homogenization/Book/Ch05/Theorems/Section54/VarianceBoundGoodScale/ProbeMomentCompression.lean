/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScaleCompression
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.QuadraticProbeBounds

/-! # Probe Moment Compression -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory

noncomputable section

/-!
# Compressed origin moments for variance probes

The first Rosenthal bridge used the coarse bound `C * (Λ + λ⁻¹)`.  For the
final variance lemma we also need the sharper matched form
`CUpper * Λ + CLower * λ⁻¹`, so that good-scale scalar comparisons compress the
normalization constants to `\widetilde\Theta_0`.
-/

/-- Centered origin moment bound from a matched upper/lower unit-scale
ellipticity domination. -/
theorem section54_centeredOrigin_momentRoot_le_weighted_factor_sum_of_abs_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {CUpper CLower : ℝ} (hCUpper_nonneg : 0 ≤ CUpper)
    (hCLower_nonneg : 0 ≤ CLower) {X : RegCoeffField d → ℝ}
    (hX_meas : AEMeasurable X P)
    (hX_abs_le :
      (fun a => |X a|) ≤ᵐ[P]
        fun a =>
          CUpper *
              Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
            CLower *
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹) :
    Integrable (fun a => |X a - ∫ b, X b ∂P| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a => |X a - ∫ b, X b ∂P|) ≤
        2 *
          (CUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            CLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let L : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a
  let I : RegCoeffField d → ℝ :=
    fun a =>
      (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹
  let YUpper : RegCoeffField d → ℝ := fun a => CUpper * L a
  let YLower : RegCoeffField d → ℝ := fun a => CLower * I a
  let Y : RegCoeffField d → ℝ := fun a => YUpper a + YLower a
  have hξ_one : 1 ≤ hP4.xi :=
    le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hL_nonneg : ∀ a, 0 ≤ L a := fun a =>
    Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hP4.sUpper_pos
      (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : ∀ a, 0 ≤ I a := fun a =>
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hP4.sLower_pos
        (by norm_num : (1 : ℝ) ≤ 1))
  have hYUpper_nonneg : ∀ a, 0 ≤ YUpper a := fun a =>
    mul_nonneg hCUpper_nonneg (hL_nonneg a)
  have hYLower_nonneg : ∀ a, 0 ≤ YLower a := fun a =>
    mul_nonneg hCLower_nonneg (hI_nonneg a)
  have hY_nonneg : ∀ a, 0 ≤ Y a := fun a =>
    add_nonneg (hYUpper_nonneg a) (hYLower_nonneg a)
  have hL_meas : AEMeasurable L P := by
    simpa [L] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hP4.sUpper_pos
  have hI_meas : AEMeasurable I P := by
    simpa [I] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hP4.sLower_pos
  have hYUpper_meas : AEMeasurable YUpper P := by
    exact hL_meas.const_mul CUpper
  have hYLower_meas : AEMeasurable YLower P := by
    exact hI_meas.const_mul CLower
  have hL_int : Integrable (fun a => L a ^ hP4.xi) P := by
    simpa [L] using
      Section52.upperFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hI_int : Integrable (fun a => I a ^ hP4.xi) P := by
    simpa [I] using
      Section52.lowerFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hYUpper_int : Integrable (fun a => YUpper a ^ hP4.xi) P := by
    have hscaled := hL_int.const_mul (CUpper ^ hP4.xi)
    refine hscaled.congr ?_
    filter_upwards with a
    simp [YUpper, mul_pow]
  have hYLower_int : Integrable (fun a => YLower a ^ hP4.xi) P := by
    have hscaled := hI_int.const_mul (CLower ^ hP4.xi)
    refine hscaled.congr ?_
    filter_upwards with a
    simp [YLower, mul_pow]
  have hξ_ne : hP4.xi ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hP4.two_le_xi)
  have hYUpper_mem : MemLp YUpper (hP4.xi : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hYUpper_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    have hYUpper_abs_int : Integrable (fun a => |YUpper a| ^ hP4.xi) P := by
      refine hYUpper_int.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hYUpper_nonneg a)]
    simpa [Real.norm_eq_abs] using hYUpper_abs_int
  have hYLower_mem : MemLp YLower (hP4.xi : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hYLower_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    have hYLower_abs_int : Integrable (fun a => |YLower a| ^ hP4.xi) P := by
      refine hYLower_int.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hYLower_nonneg a)]
    simpa [Real.norm_eq_abs] using hYLower_abs_int
  have hY_mem : MemLp Y (hP4.xi : ENNReal) P :=
    hYUpper_mem.add hYLower_mem
  have hY_int : Integrable (fun a => Y a ^ hP4.xi) P := by
    have hint := hY_mem.integrable_norm_pow hξ_ne
    refine hint.congr ?_
    filter_upwards with a
    simp [Y, Real.norm_eq_abs, abs_of_nonneg (hY_nonneg a)]
  have hX_abs_pow_int :
      Integrable (fun a => |X a| ^ hP4.xi) P :=
    section54_integrable_abs_pow_of_ae_abs_le_nonneg
      hX_meas (Filter.Eventually.of_forall hY_nonneg)
      (by simpa [Y, YUpper, YLower, L, I] using hX_abs_le) hY_int
  have hcenter_mem :
      MemLp (fun a => X a - ∫ b, X b ∂P) (hP4.xi : ENNReal) P := by
    have hmem_p : MemLp X (hP4.xi : ENNReal) P := by
      rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
        (by exact_mod_cast hξ_ne) (by simp)]
      simpa [Real.norm_eq_abs] using hX_abs_pow_int
    exact hmem_p.sub (memLp_const (∫ b, X b ∂P))
  have hcenter_int :
      Integrable (fun a => |X a - ∫ b, X b ∂P| ^ hP4.xi) P := by
    have hint := hcenter_mem.integrable_norm_pow hξ_ne
    simpa [Real.norm_eq_abs] using hint
  refine ⟨hcenter_int, ?_⟩
  have hcenter_root :=
    section54_annealedMomentRoot_abs_sub_integral_le_two_mul
      (P := P) (ξ := hP4.xi) (X := X) hξ_one hX_meas hX_abs_pow_int
  have hraw_to_Y :
      Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|) ≤
        Ch04.annealedMomentRoot P hP4.xi Y :=
    section54_annealedMomentRoot_abs_le_of_ae_abs_le_nonneg
      (P := P) (ξ := hP4.xi) (X := X) (Y := Y)
      hξ_one hY_nonneg (by simpa [Y, YUpper, YLower, L, I] using hX_abs_le)
      hX_abs_pow_int hY_int
  have hY_root :
      Ch04.annealedMomentRoot P hP4.xi Y ≤
        CUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          CLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
    have hY_add :
        Ch04.annealedMomentRoot P hP4.xi Y ≤
          Ch04.annealedMomentRoot P hP4.xi YUpper +
            Ch04.annealedMomentRoot P hP4.xi YLower := by
      simpa [Y] using
        section54_annealedMomentRoot_add_le
          (P := P) (ξ := hP4.xi) (X := YUpper) (Y := YLower)
          hξ_one hYUpper_nonneg hYLower_nonneg hYUpper_meas hYLower_meas
          hYUpper_int hYLower_int
    have hUpper_eq :
        Ch04.annealedMomentRoot P hP4.xi YUpper =
          CUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
      simpa [YUpper, L, Ch04.LambdaMomentAtScale] using
        Section52.section52_annealedMomentRoot_const_mul_of_nonneg
          (P := P) (ξ := hP4.xi) (c := CUpper) (X := L)
          hξ_one hCUpper_nonneg hL_nonneg
    have hLower_eq :
        Ch04.annealedMomentRoot P hP4.xi YLower =
          CLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
      simpa [YLower, I, Ch04.lambdaInvMomentAtScale] using
        Section52.section52_annealedMomentRoot_const_mul_of_nonneg
          (P := P) (ξ := hP4.xi) (c := CLower) (X := I)
          hξ_one hCLower_nonneg hI_nonneg
    simpa [hUpper_eq, hLower_eq] using hY_add
  calc
    Ch04.annealedMomentRoot P hP4.xi (fun a => |X a - ∫ b, X b ∂P|)
        ≤ 2 * Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|) := hcenter_root
    _ ≤ 2 * Ch04.annealedMomentRoot P hP4.xi Y := by
      exact mul_le_mul_of_nonneg_left hraw_to_Y (by norm_num)
    _ ≤
        2 *
          (CUpper * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            CLower * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
      exact mul_le_mul_of_nonneg_left hY_root (by norm_num)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
