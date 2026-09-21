/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.FiniteNet
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Partition Average -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory

noncomputable section

/-!
# Local-representative bridge for partition averages

This file builds the Section 5.4-local bridge needed to feed the normalized
full-block fluctuation observable into the Chapter 4 partition-average
theorems.  The bridge is internal to the variance-bound slice: it proves the
locality/measurability facts from existing Ch4 entrywise local representatives,
without adding proof objects to the public Section 5.4 theorem.
-/

private theorem isLocalRandomVariable_fullBlockMat_of_entries
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {X : RegCoeffField d → FullBlockMat d}
    (hX :
      ∀ α β : BlockCoord d,
        Ch04.IsRestrictionLocalRandomVariable U hU (fun a => X a α β)) :
    Ch04.IsRestrictionLocalRandomVariable U hU X := by
  change @Measurable (RegCoeffField d) (FullBlockMat d) (Ch04.restrictionSigma U hU) _ X
  refine (@measurable_pi_iff (RegCoeffField d) (BlockCoord d)
    (fun _ => BlockCoord d → ℝ) (Ch04.restrictionSigma U hU) (fun _ => inferInstance) X).2 ?_
  intro α
  refine (@measurable_pi_iff (RegCoeffField d) (BlockCoord d)
    (fun _ => ℝ) (Ch04.restrictionSigma U hU) (fun _ => inferInstance) (fun a => X a α)).2 ?_
  intro β
  exact hX α β

private def normalizedFullBlockCLMLinearMap {d : ℕ} [NeZero d]
    (D : FullBlockMat d) :
    FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) :=
  let left : FullBlockMat d →ₗ[ℝ] FullBlockMat d :=
    mulLeftLinearMap (BlockCoord d) ℝ D
  let right : FullBlockMat d →ₗ[ℝ] FullBlockMat d :=
    mulRightLinearMap (BlockCoord d) ℝ D
  let sandwich : FullBlockMat d →ₗ[ℝ] FullBlockMat d := right.comp left
  let toCLM :
      FullBlockMat d →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) :=
    LinearEquiv.toLinearMap
      (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
        |>.toAlgEquiv |>.toLinearEquiv)
  toCLM.comp sandwich

private theorem normalizedFullBlockCLMLinearMap_apply {d : ℕ} [NeZero d]
    (D M : FullBlockMat d) :
    normalizedFullBlockCLMLinearMap D M =
      Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (D * M * D) := by
  rfl

private theorem measurable_normalizedFullBlockFluctuationMap {d : ℕ} [NeZero d]
    (D Abar : FullBlockMat d) :
    Measurable
      (fun M : FullBlockMat d =>
        ‖normalizedFullBlockCLMLinearMap D (M - Abar)‖ ^ 2) := by
  have hcont :
      Continuous
        (fun M : FullBlockMat d =>
          normalizedFullBlockCLMLinearMap D (M - Abar)) :=
    (normalizedFullBlockCLMLinearMap D).continuous_of_finiteDimensional.comp
      (continuous_id.sub continuous_const)
  exact ((continuous_norm.comp hcont).pow 2).measurable

private def normalizedFullBlockMatLinearMap {d : ℕ}
    (D : FullBlockMat d) : FullBlockMat d →ₗ[ℝ] FullBlockMat d :=
  let left : FullBlockMat d →ₗ[ℝ] FullBlockMat d :=
    mulLeftLinearMap (BlockCoord d) ℝ D
  let right : FullBlockMat d →ₗ[ℝ] FullBlockMat d :=
    mulRightLinearMap (BlockCoord d) ℝ D
  right.comp left

private theorem normalizedFullBlockMatLinearMap_apply {d : ℕ}
    (D M : FullBlockMat d) :
    normalizedFullBlockMatLinearMap D M = D * M * D := by
  rfl

private theorem measurable_normalizedFullBlockQuadraticMap {d : ℕ}
    [NeZero d] (D : FullBlockMat d) (q : FullBlockVec d) :
    Measurable
      (fun M : FullBlockMat d => fullBlockQuadratic (D * M * D) q) := by
  have hcont :
      Continuous
        (fun M : FullBlockMat d =>
          fullBlockQuadratic (normalizedFullBlockMatLinearMap D M) q) := by
    unfold fullBlockQuadratic
    fun_prop
  simpa [normalizedFullBlockMatLinearMap_apply] using hcont.measurable

theorem section54_annealedMomentRoot_abs_le_of_ae_abs_le_nonneg
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (_hY_nonneg : ∀ a, 0 ≤ Y a)
    (hXY : (fun a => |X a|) ≤ᵐ[P] Y)
    (hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P)
    (hY_pow_int : Integrable (fun a => Y a ^ ξ) P) :
    Ch04.annealedMomentRoot P ξ (fun a => |X a|) ≤
      Ch04.annealedMomentRoot P ξ Y := by
  have hpow :
      (fun a => |X a| ^ ξ) ≤ᵐ[P] fun a => Y a ^ ξ := by
    filter_upwards [hXY] with a hle
    exact pow_le_pow_left₀ (abs_nonneg (X a)) hle ξ
  have hint_le :
      ∫ a, |X a| ^ ξ ∂P ≤ ∫ a, Y a ^ ξ ∂P :=
    integral_mono_ae hX_abs_pow_int hY_pow_int hpow
  have hleft_nonneg : 0 ≤ ∫ a, |X a| ^ ξ ∂P :=
    integral_nonneg fun a => pow_nonneg (abs_nonneg (X a)) ξ
  have hexp_nonneg : 0 ≤ 1 / (ξ : ℝ) := by positivity
  simpa [Ch04.annealedMomentRoot] using
    Real.rpow_le_rpow hleft_nonneg hint_le hexp_nonneg

theorem section54_integrable_abs_pow_of_ae_abs_le_nonneg
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hX_meas : AEMeasurable X P)
    (hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a)
    (hXY : (fun a => |X a|) ≤ᵐ[P] Y)
    (hY_pow_int : Integrable (fun a => Y a ^ ξ) P) :
    Integrable (fun a => |X a| ^ ξ) P := by
  have hY_abs_pow_int : Integrable (fun a => |Y a| ^ ξ) P := by
    refine hY_pow_int.congr ?_
    filter_upwards [hY_nonneg] with a ha
    simp [abs_of_nonneg ha]
  refine Integrable.mono' hY_abs_pow_int ?_ ?_
  · exact ((hX_meas.norm.pow_const ξ)).aestronglyMeasurable
  · filter_upwards [hY_nonneg, hXY] with a hY_nonneg_a hXY_a
    have hpow : |X a| ^ ξ ≤ |Y a| ^ ξ := by
      simpa [abs_of_nonneg hY_nonneg_a] using
        pow_le_pow_left₀ (abs_nonneg (X a)) hXY_a ξ
    have hleft_nonneg : 0 ≤ |X a| ^ ξ :=
      pow_nonneg (abs_nonneg (X a)) ξ
    have hright_nonneg : 0 ≤ |Y a| ^ ξ :=
      pow_nonneg (abs_nonneg (Y a)) ξ
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
      abs_of_nonneg hright_nonneg] using hpow

theorem section54_annealedMomentRoot_abs_sub_integral_le_two_mul
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hX_meas : AEMeasurable X P)
    (hX_abs_pow_int : Integrable (fun a => |X a| ^ ξ) P) :
    Ch04.annealedMomentRoot P ξ
        (fun a => |X a - ∫ b, X b ∂P|) ≤
      2 * Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hmem_p : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hX_abs_pow_int
  have hmem_one : MemLp X (1 : ENNReal) P :=
    hmem_p.mono_exponent (by exact_mod_cast hξ)
  have hX_int : Integrable X P := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at hmem_one
  let c : ℝ := ∫ b, X b ∂P
  have hconst_mem : MemLp (fun _ : RegCoeffField d => c) (ξ : ENNReal) P :=
    memLp_const c
  have hcenter_mem : MemLp (fun a => X a - c) (ξ : ENNReal) P :=
    hmem_p.sub hconst_mem
  have hcenter_toReal :
      ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P) =
        Ch04.annealedMomentRoot P ξ (fun a => |X a - c|) := by
    calc
      ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P)
          = (∫ a, ‖X a - c‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := fun a => X a - c) (p := ξ) hξ hcenter_mem
      _ = Ch04.annealedMomentRoot P ξ (fun a => |X a - c|) := by
            simp [Ch04.annealedMomentRoot, Real.norm_eq_abs]
  have hX_toReal :
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) =
        Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
    calc
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P)
          = (∫ a, ‖X a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := X) (p := ξ) hξ hmem_p
      _ = Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
            simp [Ch04.annealedMomentRoot, Real.norm_eq_abs]
  have hroot_abs_nonneg :
      0 ≤ Ch04.annealedMomentRoot P ξ (fun a => |X a|) :=
    Ch04.annealedMomentRoot_nonneg_of_nonneg P ξ fun a => abs_nonneg (X a)
  have hmean_le :
      |c| ≤ Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
    have hAbs_meas : AEMeasurable (fun a => |X a|) P := by
      simpa [Real.norm_eq_abs] using hX_meas.norm
    have hAbs_int : Integrable (fun a => |X a|) P := by
      have hAbs_mem_one : MemLp (fun a => |X a|) (1 : ENNReal) P := by
        have hAbs_mem_p : MemLp (fun a => |X a|) (ξ : ENNReal) P := by
          rw [← MeasureTheory.integrable_norm_rpow_iff hAbs_meas.aestronglyMeasurable
            (by exact_mod_cast hξ_ne) (by simp)]
          simpa [Real.norm_eq_abs, abs_abs] using hX_abs_pow_int
        exact hAbs_mem_p.mono_exponent (by exact_mod_cast hξ)
      rwa [MeasureTheory.memLp_one_iff_integrable] at hAbs_mem_one
    have hInt_le_root :
        ∫ a, |X a| ∂P ≤
          Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
      exact Ch04.integral_le_annealedMomentRoot_of_ae_nonneg hξ hAbs_meas
        (Filter.Eventually.of_forall fun a => abs_nonneg (X a))
        (by simpa using hX_abs_pow_int)
    exact (abs_integral_le_integral_abs (f := X) (μ := P)).trans hInt_le_root
  have hconst_toReal :
      ENNReal.toReal (eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P) = |c| := by
    have hμ_ne_zero : (P : Measure (RegCoeffField d)) ≠ 0 :=
      IsProbabilityMeasure.ne_zero P
    have hξ_enn_ne_zero : (ξ : ENNReal) ≠ 0 := by exact_mod_cast hξ_ne
    rw [MeasureTheory.eLpNorm_const (μ := P) (c := c) (p := (ξ : ENNReal))
      hξ_enn_ne_zero hμ_ne_zero]
    simp [IsProbabilityMeasure.measure_univ, Real.norm_eq_abs]
  have hconst_ne_top :
      eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P ≠ ⊤ :=
    hconst_mem.2.ne
  have hsum_ne_top :
      eLpNorm X (ξ : ENNReal) P +
          eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hmem_p.2.ne, hconst_ne_top⟩
  have hsub_le :
      eLpNorm (fun a => X a - c) (ξ : ENNReal) P ≤
        eLpNorm X (ξ : ENNReal) P +
          eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P := by
    simpa only [c, Pi.sub_def, Pi.sub_apply] using
      eLpNorm_sub_le hX_meas.aestronglyMeasurable
        (aestronglyMeasurable_const (μ := P) (b := c))
        (by exact_mod_cast hξ)
  calc
    Ch04.annealedMomentRoot P ξ (fun a => |X a - ∫ b, X b ∂P|)
        = ENNReal.toReal (eLpNorm (fun a => X a - c) (ξ : ENNReal) P) := by
          simp [hcenter_toReal, c]
    _ ≤ ENNReal.toReal
          (eLpNorm X (ξ : ENNReal) P +
            eLpNorm (fun _ : RegCoeffField d => c) (ξ : ENNReal) P) :=
          ENNReal.toReal_mono hsum_ne_top hsub_le
    _ = Ch04.annealedMomentRoot P ξ (fun a => |X a|) + |c| := by
          rw [ENNReal.toReal_add hmem_p.2.ne hconst_ne_top,
            hX_toReal, hconst_toReal]
    _ ≤ Ch04.annealedMomentRoot P ξ (fun a => |X a|) +
          Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by
          gcongr
    _ = 2 * Ch04.annealedMomentRoot P ξ (fun a => |X a|) := by ring

theorem section54_annealedMomentRoot_add_le
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hX_nonneg : ∀ a, 0 ≤ X a) (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hX_meas : AEMeasurable X P) (hY_meas : AEMeasurable Y P)
    (hX_int : Integrable (fun a => X a ^ ξ) P)
    (hY_int : Integrable (fun a => Y a ^ ξ) P) :
    Ch04.annealedMomentRoot P ξ (fun a => X a + Y a) ≤
      Ch04.annealedMomentRoot P ξ X + Ch04.annealedMomentRoot P ξ Y := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hX_abs_int : Integrable (fun a => |X a| ^ ξ) P := by
    refine hX_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hX_nonneg a)]
  have hY_abs_int : Integrable (fun a => |Y a| ^ ξ) P := by
    refine hY_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hY_nonneg a)]
  have hX_mem : MemLp X (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hX_abs_int
  have hY_mem : MemLp Y (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hY_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hY_abs_int
  have hsum_mem : MemLp (fun a => X a + Y a) (ξ : ENNReal) P :=
    hX_mem.add hY_mem
  have hsum_toReal :
      ENNReal.toReal (eLpNorm (fun a => X a + Y a) (ξ : ENNReal) P) =
        Ch04.annealedMomentRoot P ξ (fun a => X a + Y a) := by
    calc
      ENNReal.toReal (eLpNorm (fun a => X a + Y a) (ξ : ENNReal) P)
          = (∫ a, ‖X a + Y a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := fun a => X a + Y a) (p := ξ) hξ hsum_mem
      _ = Ch04.annealedMomentRoot P ξ (fun a => X a + Y a) := by
            rw [Ch04.annealedMomentRoot]
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
              simp [Real.norm_eq_abs, abs_of_nonneg
                (add_nonneg (hX_nonneg a) (hY_nonneg a))])
  have hX_toReal :
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) =
        Ch04.annealedMomentRoot P ξ X := by
    calc
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P)
          = (∫ a, ‖X a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := X) (p := ξ) hξ hX_mem
      _ = Ch04.annealedMomentRoot P ξ X := by
            rw [Ch04.annealedMomentRoot]
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
              simp [Real.norm_eq_abs, abs_of_nonneg (hX_nonneg a)])
  have hY_toReal :
      ENNReal.toReal (eLpNorm Y (ξ : ENNReal) P) =
        Ch04.annealedMomentRoot P ξ Y := by
    calc
      ENNReal.toReal (eLpNorm Y (ξ : ENNReal) P)
          = (∫ a, ‖Y a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := Y) (p := ξ) hξ hY_mem
      _ = Ch04.annealedMomentRoot P ξ Y := by
            rw [Ch04.annealedMomentRoot]
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
              simp [Real.norm_eq_abs, abs_of_nonneg (hY_nonneg a)])
  have hsum_ne_top :
      eLpNorm X (ξ : ENNReal) P + eLpNorm Y (ξ : ENNReal) P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hX_mem.2.ne, hY_mem.2.ne⟩
  have hadd :
      eLpNorm (fun a => X a + Y a) (ξ : ENNReal) P ≤
        eLpNorm X (ξ : ENNReal) P + eLpNorm Y (ξ : ENNReal) P := by
    simpa only [Pi.add_def, Pi.add_apply] using
      (MeasureTheory.eLpNorm_add_le
        hX_meas.aestronglyMeasurable hY_meas.aestronglyMeasurable
        (by exact_mod_cast hξ))
  calc
    Ch04.annealedMomentRoot P ξ (fun a => X a + Y a)
        = ENNReal.toReal (eLpNorm (fun a => X a + Y a) (ξ : ENNReal) P) :=
          hsum_toReal.symm
    _ ≤ ENNReal.toReal (eLpNorm X (ξ : ENNReal) P + eLpNorm Y (ξ : ENNReal) P) :=
          ENNReal.toReal_mono hsum_ne_top hadd
    _ = Ch04.annealedMomentRoot P ξ X + Ch04.annealedMomentRoot P ξ Y := by
          rw [ENNReal.toReal_add hX_mem.2.ne hY_mem.2.ne, hX_toReal, hY_toReal]

theorem section54_centeredOrigin_momentRoot_le_factor_sum_of_abs_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C : ℝ} (hC_nonneg : 0 ≤ C) {X : RegCoeffField d → ℝ}
    (hX_meas : AEMeasurable X P)
    (hX_abs_le :
      (fun a => |X a|) ≤ᵐ[P]
        fun a =>
          C *
            (Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
              (Ch04.lambdaSqCoeffField
                (originCube d 0) hP4.sLower (.finite 1) a)⁻¹)) :
    Integrable (fun a => |X a - ∫ b, X b ∂P| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a => |X a - ∫ b, X b ∂P|) ≤
        2 * C *
          (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let L : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a
  let I : RegCoeffField d → ℝ :=
    fun a =>
      (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹
  let Y : RegCoeffField d → ℝ := fun a => C * (L a + I a)
  have hξ_one : 1 ≤ hP4.xi :=
    le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hL_nonneg : ∀ a, 0 ≤ L a := fun a =>
    Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hP4.sUpper_pos
      (by norm_num : (1 : ℝ) ≤ 1)
  have hI_nonneg : ∀ a, 0 ≤ I a := fun a =>
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hP4.sLower_pos
        (by norm_num : (1 : ℝ) ≤ 1))
  have hY_nonneg : ∀ a, 0 ≤ Y a := fun a =>
    mul_nonneg hC_nonneg (add_nonneg (hL_nonneg a) (hI_nonneg a))
  have hL_meas : AEMeasurable L P := by
    simpa [L] using
      hP.aemeasurable_LambdaSqCoeffField_finite_one
        (originCube d 0) hP4.sUpper_pos
  have hI_meas : AEMeasurable I P := by
    simpa [I] using
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
        (originCube d 0) hP4.sLower_pos
  have hL_int : Integrable (fun a => L a ^ hP4.xi) P := by
    simpa [L] using
      Section52.upperFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hI_int : Integrable (fun a => I a ^ hP4.xi) P := by
    simpa [I] using
      Section52.lowerFactorPowerIntegrableAtScale_from_P4
        hP hStruct hP4 0
  have hξ_ne : hP4.xi ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hP4.two_le_xi)
  have hL_mem : MemLp L (hP4.xi : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hL_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    have hL_abs_int : Integrable (fun a => |L a| ^ hP4.xi) P := by
      refine hL_int.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hL_nonneg a)]
    simpa [Real.norm_eq_abs] using hL_abs_int
  have hI_mem : MemLp I (hP4.xi : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hI_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    have hI_abs_int : Integrable (fun a => |I a| ^ hP4.xi) P := by
      refine hI_int.congr ?_
      filter_upwards with a
      simp [abs_of_nonneg (hI_nonneg a)]
    simpa [Real.norm_eq_abs] using hI_abs_int
  have hsum_mem : MemLp (fun a => L a + I a) (hP4.xi : ENNReal) P :=
    hL_mem.add hI_mem
  have hsum_int : Integrable (fun a => (L a + I a) ^ hP4.xi) P := by
    have hint := hsum_mem.integrable_norm_pow (by exact hξ_ne)
    refine hint.congr ?_
    filter_upwards with a
    simp [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (hL_nonneg a) (hI_nonneg a))]
  have hY_int : Integrable (fun a => Y a ^ hP4.xi) P := by
    have hscaled := hsum_int.const_mul (C ^ hP4.xi)
    refine hscaled.congr ?_
    filter_upwards with a
    simp [Y, mul_pow]
  have hX_abs_pow_int :
      Integrable (fun a => |X a| ^ hP4.xi) P :=
    section54_integrable_abs_pow_of_ae_abs_le_nonneg
      hX_meas (Filter.Eventually.of_forall hY_nonneg)
      (by simpa [Y] using hX_abs_le) hY_int
  have hcenter_mem : MemLp (fun a => X a - ∫ b, X b ∂P) (hP4.xi : ENNReal) P := by
    have hmem_p : MemLp X (hP4.xi : ENNReal) P := by
      rw [← MeasureTheory.integrable_norm_rpow_iff hX_meas.aestronglyMeasurable
        (by exact_mod_cast hξ_ne) (by simp)]
      simpa [Real.norm_eq_abs] using hX_abs_pow_int
    exact hmem_p.sub (memLp_const (∫ b, X b ∂P))
  have hcenter_int :
      Integrable (fun a => |X a - ∫ b, X b ∂P| ^ hP4.xi) P := by
    have hint := hcenter_mem.integrable_norm_pow (by exact hξ_ne)
    simpa [Real.norm_eq_abs] using hint
  refine ⟨hcenter_int, ?_⟩
  have hcenter_root :=
    section54_annealedMomentRoot_abs_sub_integral_le_two_mul
      (P := P) (ξ := hP4.xi) (X := X) hξ_one hX_meas hX_abs_pow_int
  have hraw_root :
      Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|) ≤
        C *
          (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
    have hraw_to_Y :
        Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|) ≤
          Ch04.annealedMomentRoot P hP4.xi Y :=
      section54_annealedMomentRoot_abs_le_of_ae_abs_le_nonneg
        (P := P) (ξ := hP4.xi) (X := X) (Y := Y)
        hξ_one hY_nonneg (by simpa [Y] using hX_abs_le)
        hX_abs_pow_int hY_int
    have hY_eq :
        Ch04.annealedMomentRoot P hP4.xi Y =
          C * Ch04.annealedMomentRoot P hP4.xi (fun a => L a + I a) := by
      simpa [Y] using
        Section52.section52_annealedMomentRoot_const_mul_of_nonneg
          (P := P) (ξ := hP4.xi) (c := C) (X := fun a => L a + I a)
          hξ_one hC_nonneg
          (fun a => add_nonneg (hL_nonneg a) (hI_nonneg a))
    have hsum_root :
        Ch04.annealedMomentRoot P hP4.xi (fun a => L a + I a) ≤
          Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
      simpa [L, I, Ch04.LambdaMomentAtScale, Ch04.lambdaInvMomentAtScale] using
        section54_annealedMomentRoot_add_le
          (P := P) (ξ := hP4.xi) (X := L) (Y := I)
          hξ_one hL_nonneg hI_nonneg hL_meas hI_meas hL_int hI_int
    calc
      Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|)
          ≤ Ch04.annealedMomentRoot P hP4.xi Y := hraw_to_Y
      _ = C * Ch04.annealedMomentRoot P hP4.xi (fun a => L a + I a) := hY_eq
      _ ≤ C *
          (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) :=
          mul_le_mul_of_nonneg_left hsum_root hC_nonneg
  calc
    Ch04.annealedMomentRoot P hP4.xi (fun a => |X a - ∫ b, X b ∂P|)
        ≤ 2 * Ch04.annealedMomentRoot P hP4.xi (fun a => |X a|) := hcenter_root
    _ ≤ 2 * (C *
          (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) := by
          exact mul_le_mul_of_nonneg_left hraw_root (by norm_num)
    _ = 2 * C *
          (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
            Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by ring

private theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : RegCoeffField d → ℝ,
      Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j)
          =ᵐ[P] Y := by
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q ((Pi.single i 1, 0) + (0, Pi.single j 1)) with
    ⟨Ysum, hYsum_local, hYsum_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (Pi.single i 1, 0) with ⟨Yi, hYi_local, hYi_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (0, Pi.single j 1) with ⟨Yj, hYj_local, hYj_eq⟩
  refine ⟨fun a => Ysum a - Yi a - Yj a,
    (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
  filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
  calc
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j =
        Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) a -
          Mu (cubeSet Q) (Pi.single i 1, 0) a -
          Mu (cubeSet Q) (0, Pi.single j 1) a := by
          simp [coarseBlockMatrix_upperRight_apply]
    _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

private theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : RegCoeffField d → ℝ,
      Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j)
          =ᵐ[P] Y := by
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q ((0, Pi.single i 1) + (Pi.single j 1, 0)) with
    ⟨Ysum, hYsum_local, hYsum_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (0, Pi.single i 1) with ⟨Yi, hYi_local, hYi_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (Pi.single j 1, 0) with ⟨Yj, hYj_local, hYj_eq⟩
  refine ⟨fun a => Ysum a - Yi a - Yj a,
    (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
  filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
  calc
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j =
        Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) a -
          Mu (cubeSet Q) (0, Pi.single i 1) a -
          Mu (cubeSet Q) (Pi.single j 1, 0) a := by
          simp [coarseBlockMatrix_lowerLeft_apply]
    _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

private theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∃ Y : RegCoeffField d → FullBlockMat d,
      Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
          =ᵐ[P] Y := by
  classical
  let entry_exists : ∀ α β : BlockCoord d,
      ∃ Y : RegCoeffField d → ℝ,
        Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
          (fun a : RegCoeffField d =>
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β) =ᵐ[P] Y := by
    intro α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat] using
              hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
        | inr j =>
            simpa [toFullBlockMat] using
              exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperRight_apply_cubeSet
                hP Q i j
    | inr i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat] using
              exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerLeft_apply_cubeSet
                hP Q i j
        | inr j =>
            simpa [toFullBlockMat] using
              hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
  let Yentry : BlockCoord d → BlockCoord d → RegCoeffField d → ℝ :=
    fun α β => Classical.choose (entry_exists α β)
  let Y : RegCoeffField d → FullBlockMat d := fun a α β => Yentry α β a
  refine ⟨Y, ?_, ?_⟩
  · refine isLocalRandomVariable_fullBlockMat_of_entries (measurableSet_cubeSet Q) ?_
    intro α β
    exact (Classical.choose_spec (entry_exists α β)).1
  · have hentry :
        ∀ α β : BlockCoord d,
          (fun a : RegCoeffField d =>
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β) =ᵐ[P]
              fun a => Y a α β := by
      intro α β
      exact (Classical.choose_spec (entry_exists α β)).2
    have hall :
        ∀ᵐ a ∂P,
          ∀ α β : BlockCoord d,
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β = Y a α β := by
      rw [Filter.eventually_all]
      intro α
      rw [Filter.eventually_all]
      intro β
      exact hentry α β
    filter_upwards [hall] with a ha
    ext α β
    exact ha α β

private theorem aemeasurable_fullBlockNormalizedFluctuationOperatorNormSq_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        Ch04.fullBlockNormalizedFluctuationOperatorNormSq
          hP hStruct center (cubeSet Q) a.toFun) P := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let Abar : BlockMat d := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let g : FullBlockMat d → ℝ :=
    fun M => ‖normalizedFullBlockCLMLinearMap D (M - toFullBlockMat Abar)‖ ^ 2
  have hg : Measurable g :=
    measurable_normalizedFullBlockFluctuationMap D (toFullBlockMat Abar)
  have hM :
      AEMeasurable
        (fun a : RegCoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  simpa only [Ch04.fullBlockNormalizedFluctuationOperatorNormSq, b, c, D, Abar, g,
    normalizedFullBlockCLMLinearMap_apply, Function.comp_def] using
    hg.comp_aemeasurable hM

theorem exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedFluctuationOperatorNormSq_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) :
    ∃ Y : RegCoeffField d → ℝ,
      Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d =>
          Ch04.fullBlockNormalizedFluctuationOperatorNormSq
            hP hStruct center (cubeSet Q) a.toFun) =ᵐ[P] Y := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let Abar : BlockMat d := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let g : FullBlockMat d → ℝ :=
    fun M => ‖normalizedFullBlockCLMLinearMap D (M - toFullBlockMat Abar)‖ ^ 2
  have hg : Measurable g :=
    measurable_normalizedFullBlockFluctuationMap D (toFullBlockMat Abar)
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet
      hP Q with ⟨Ymat, hYmat_local, hYmat_eq⟩
  refine ⟨fun a => g (Ymat a), hYmat_local.comp_measurable hg, ?_⟩
  filter_upwards [hYmat_eq] with a ha
  simp [Ch04.fullBlockNormalizedFluctuationOperatorNormSq, b, c, D, Abar, g,
    normalizedFullBlockCLMLinearMap_apply, ha]

private theorem aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable
          hP hStruct center q (cubeSet Q) a.toFun) P := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let g : FullBlockMat d → ℝ :=
    fun M => fullBlockQuadratic (D * M * D) q
  have hg : Measurable g :=
    measurable_normalizedFullBlockQuadraticMap D q
  have hM :
      AEMeasurable
        (fun a : RegCoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  simpa only [fullBlockNormalizedQuadraticObservable, b, c, D, g,
    Function.comp_def] using
    hg.comp_aemeasurable hM

theorem exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) :
    ∃ Y : RegCoeffField d → ℝ,
      Ch04.IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d =>
          fullBlockNormalizedQuadraticObservable
            hP hStruct center q (cubeSet Q) a.toFun) =ᵐ[P] Y := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let g : FullBlockMat d → ℝ :=
    fun M => fullBlockQuadratic (D * M * D) q
  have hg : Measurable g :=
    measurable_normalizedFullBlockQuadraticMap D q
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet
      hP Q with ⟨Ymat, hYmat_local, hYmat_eq⟩
  refine ⟨fun a => g (Ymat a), hYmat_local.comp_measurable hg, ?_⟩
  filter_upwards [hYmat_eq] with a ha
  simp [fullBlockNormalizedQuadraticObservable, b, c, D, g, ha]

/-- Descendant-family local representatives for the normalized full-block
fluctuation observable.  This is the local-representative hypothesis needed by
the a.e.-local Ch4 partition-average theorem. -/
theorem fullBlockNormalizedFluctuationOperatorNormSq_descendants_localRep
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      ∃ Y : RegCoeffField d → ℝ,
        Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧
          (fun a : RegCoeffField d =>
            Ch04.fullBlockNormalizedFluctuationOperatorNormSq
              hP hStruct center (cubeSet R) a.toFun) =ᵐ[P] Y := by
  intro R _hR
  exact
    exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedFluctuationOperatorNormSq_cubeSet
      hP hStruct center R

/-- Descendant-family a.e.-measurability for the normalized full-block
fluctuation observable. -/
private theorem aemeasurable_fullBlockNormalizedFluctuationOperatorNormSq_descendants
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch04.fullBlockNormalizedFluctuationOperatorNormSq
            hP hStruct center (cubeSet R) a.toFun) P := by
  intro R _hR
  exact
    aemeasurable_fullBlockNormalizedFluctuationOperatorNormSq_cubeSet
      hP hStruct center R

/-- Descendant-family local representatives for normalized quadratic probes. -/
theorem fullBlockNormalizedQuadraticObservable_descendants_localRep
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      ∃ Y : RegCoeffField d → ℝ,
        Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧
          (fun a : RegCoeffField d =>
            fullBlockNormalizedQuadraticObservable
              hP hStruct center q (cubeSet R) a.toFun) =ᵐ[P] Y := by
  intro R _hR
  exact
    exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
      hP hStruct center q R

/-- Descendant-family a.e.-measurability for normalized quadratic probes. -/
private theorem aemeasurable_fullBlockNormalizedQuadraticObservable_descendants
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      AEMeasurable
        (fun a : RegCoeffField d =>
          fullBlockNormalizedQuadraticObservable
            hP hStruct center q (cubeSet R) a.toFun) P := by
  intro R _hR
  exact
    aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet
      hP hStruct center q R

/-- Origin-cube partition-average moment estimate with a.e.-local descendant
representatives.  This is the Section 5.4-local bridge from the exact-local
Ch4 Rosenthal theorem to the totalized coarse-block observables used in Ch5. -/
theorem integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
    {d : ℕ} {n m : ℤ} {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hP : Ch04.RestrictionLawCarrier P)
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : Ch04.RestrictionStationaryLaw P) (hPdep : Ch04.RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_localRep :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        ∃ Y : RegCoeffField d → ℝ,
          Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet R) =ᵐ[P] Y)
    (hX_cov : Ch04.IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (hX0Lp_int :
      Integrable (fun a => |Ch04.restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |Ch04.restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K) :
    (∫ a, |Ch04.restrictionCenteredDescendantAverage P n m X a| ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d n p *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^
              (1 / (p : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d n p *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
  simpa [Ch04.restrictionCenteredDescendantAverage, Ch04.restrictionCenteredDescendantAverageOnCube]
    using
      Ch04.integral_abs_restrictionCenteredDescendantAverageOnCube_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
        (d := d) (Q := originCube d m) (n := n) (P := P) (p := p) (K := K)
        hP hn (by simpa [originCube] using hnm) hPstat hPdep X
        hX_localRep hX_cov hX0_aemeas hX_desc_aemeas hp hK_nonneg
        hX0Lp_int hX0Lp

/-- Rosenthal/partition-average estimate for the normalized full-block
fluctuation observable, assuming only the origin-scale moment root that the
good-scale scalar estimates will provide. -/
theorem fullBlockNormalizedFluctuationOperatorNormSq_restrictionCenteredDescendantAverage_pow_rpow_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center n m : ℤ} {K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m) (hK_nonneg : 0 ≤ K)
    (hOriginMoment_int :
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P n
            (fun U a =>
              Ch04.fullBlockNormalizedFluctuationOperatorNormSq
                hP hStruct center U a.toFun) a| ^ hP4.xi) P)
    (hOriginMoment :
      (∫ a,
          |Ch04.restrictionCenteredOriginObservable P n
            (fun U a =>
              Ch04.fullBlockNormalizedFluctuationOperatorNormSq
                hP hStruct center U a.toFun) a| ^ hP4.xi ∂P) ^
          (1 / (hP4.xi : ℝ)) ≤ K) :
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P n m
          (fun U a =>
            Ch04.fullBlockNormalizedFluctuationOperatorNormSq
              hP hStruct center U a.toFun) a| ^ hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d n hP4.xi *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d n hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a =>
      Ch04.fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center U a.toFun
  have hlocal :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        ∃ Y : RegCoeffField d → ℝ,
          Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet R) =ᵐ[P] Y := by
    simpa only [X] using
      fullBlockNormalizedFluctuationOperatorNormSq_descendants_localRep
        hP hStruct center (originCube d m) n
  have hdesc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        AEMeasurable (X (cubeSet R)) P := by
    simpa only [X] using
      aemeasurable_fullBlockNormalizedFluctuationOperatorNormSq_descendants
        hP hStruct center (originCube d m) n
  have h0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P := by
    simpa only [X] using
      aemeasurable_fullBlockNormalizedFluctuationOperatorNormSq_cubeSet
        hP hStruct center (originCube d n)
  simpa [X] using
    integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
      (d := d) (n := n) (m := m) (P := P) (p := hP4.xi) (K := K)
      hP hn hnm hStruct.stationary hStruct.unit_range X hlocal
      (Ch04.isRestrictionTranslationCovariant_comp_toFun
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
          hP hStruct center))
      h0_aemeas hdesc_aemeas hP4.two_le_xi hK_nonneg
      (by simpa [X] using hOriginMoment_int)
      (by simpa [X] using hOriginMoment)

/-- Rosenthal/partition-average estimate for a normalized quadratic probe,
assuming the origin-scale moment root supplied by the good-scale scalar
estimate. -/
theorem fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center n m : ℤ} {K : ℝ} (q : FullBlockVec d)
    (hn : 0 ≤ n) (hnm : n ≤ m) (hK_nonneg : 0 ≤ K)
    (hOriginMoment_int :
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P n
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              hP4.xi) P)
    (hOriginMoment :
      (∫ a,
          |Ch04.restrictionCenteredOriginObservable P n
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              hP4.xi ∂P) ^
          (1 / (hP4.xi : ℝ)) ≤ K) :
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P n m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d n hP4.xi *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d n hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  have hlocal :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        ∃ Y : RegCoeffField d → ℝ,
          Ch04.IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet R) =ᵐ[P] Y := by
    simpa only [X, fullBlockNormalizedQuadraticObservableR] using!
      fullBlockNormalizedQuadraticObservable_descendants_localRep
        hP hStruct center q (originCube d m) n
  have hdesc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        AEMeasurable (X (cubeSet R)) P := by
    simpa only [X, fullBlockNormalizedQuadraticObservableR] using!
      aemeasurable_fullBlockNormalizedQuadraticObservable_descendants
        hP hStruct center q (originCube d m) n
  have h0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P := by
    simpa only [X, fullBlockNormalizedQuadraticObservableR] using!
      aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet
        hP hStruct center q (originCube d n)
  simpa [X] using
    integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
      (d := d) (n := n) (m := m) (P := P) (p := hP4.xi) (K := K)
      hP hn hnm hStruct.stationary hStruct.unit_range X hlocal
      (Ch04.isRestrictionTranslationCovariant_comp_toFun
        (fullBlockNormalizedQuadraticObservable_translation_covariant
          hP hStruct center q))
      h0_aemeas hdesc_aemeas hP4.two_le_xi hK_nonneg
      (by simpa [X] using hOriginMoment_int)
      (by simpa [X] using hOriginMoment)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
