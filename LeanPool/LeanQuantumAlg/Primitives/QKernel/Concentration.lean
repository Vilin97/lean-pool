/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Util.Concentration
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic.Common
/-!
# Exponential concentration of the tensor-product RY quantum kernel

The global-measurement example of Thanasilp et al. (2022): the fidelity kernel of the
embedding `U(x) = ⊗ₖ R_Y(xₖ)` is `κ(x,x') = ∏ₖ cos²((xₖ-x'ₖ)/2)`. By translation
invariance each coordinate reduces to a uniform variable on `[-π,π]`, so we study
`ryKernel n θ = ∏ₖ cos²(θₖ)`. Its moments are elementary (`𝔼[κ]=(1/2)ⁿ`,
`Var[κ]=(3/8)ⁿ-(1/4)ⁿ`), giving genuine exponential concentration with NO Haar assumption.
-/

@[expose] public section

namespace QuantumAlg

open MeasureTheory ProbabilityTheory Real intervalIntegral

/-- Uniform probability measure on `[-π, π]`. -/
noncomputable def unifAngle : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Icc (-Real.pi) Real.pi)

/-- The reduced tensor-product RY fidelity kernel `∏ₖ cos²(θₖ)`. -/
noncomputable def ryKernel (n : ℕ) (θ : Fin n → ℝ) : ℝ := ∏ k, Real.cos (θ k) ^ 2

/-- The data distribution: `n` independent uniform angles. -/
noncomputable def ryMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => unifAngle)

instance : IsProbabilityMeasure unifAngle := by
  refine ⟨?_⟩
  rw [unifAngle, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Icc,
    show Real.pi - -Real.pi = 2 * Real.pi from by ring,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top]

theorem ryKernel_nonneg (n : ℕ) (θ : Fin n → ℝ) : 0 ≤ ryKernel n θ :=
  Finset.prod_nonneg (fun _ _ => sq_nonneg _)

theorem ryKernel_le_one (n : ℕ) (θ : Fin n → ℝ) : ryKernel n θ ≤ 1 :=
  Finset.prod_le_one (fun k _ => sq_nonneg _)
    (fun k _ => by nlinarith [Real.neg_one_le_cos (θ k), Real.cos_le_one (θ k)])

theorem continuous_ryKernel (n : ℕ) : Continuous (ryKernel n) := by
  unfold ryKernel
  exact continuous_finsetProd _
    (fun k _ => (Real.continuous_cos.comp (continuous_apply k)).pow 2)

/-- `∫ cos²θ` over the uniform measure on `[-π,π]` equals `1/2`. -/
theorem integral_cos_sq_unifAngle : ∫ x, Real.cos x ^ 2 ∂unifAngle = 1 / 2 := by
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [unifAngle, MeasureTheory.integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi, integral_cos_sq,
    Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp
  ring

/-- `∫ cos⁴θ` over the uniform measure on `[-π,π]` equals `3/8`. -/
theorem integral_cos_pow4_unifAngle : ∫ x, Real.cos x ^ 4 ∂unifAngle = 3 / 8 := by
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hI : ∫ x in (-Real.pi)..Real.pi, Real.cos x ^ 4 = 3 * Real.pi / 4 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow, integral_cos_sq,
      Real.cos_pi, Real.sin_pi, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
    push_cast
    ring
  rw [unifAngle, MeasureTheory.integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi, hI,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp
  ring

instance instIsProbabilityMeasureRyMeasure (n : ℕ) : IsProbabilityMeasure (ryMeasure n) := by
  unfold ryMeasure; infer_instance

theorem ryKernel_memLp (n : ℕ) : MemLp (ryKernel n) 2 (ryMeasure n) := by
  refine MemLp.of_bound (continuous_ryKernel n).aestronglyMeasurable 1 ?_
  refine ae_of_all _ (fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ryKernel_nonneg n θ)]
  exact ryKernel_le_one n θ

/-- First moment: `𝔼[κ_n] = (1/2)ⁿ`. -/
theorem mean_ryKernel (n : ℕ) : ∫ θ, ryKernel n θ ∂(ryMeasure n) = (1 / 2) ^ n := by
  unfold ryKernel ryMeasure
  rw [integral_fintype_prod_eq_pow (fun t => Real.cos t ^ 2), integral_cos_sq_unifAngle,
    Fintype.card_fin]

/-- Second moment: `𝔼[κ_n²] = (3/8)ⁿ`. -/
theorem mean_ryKernel_sq (n : ℕ) :
    ∫ θ, (ryKernel n θ) ^ 2 ∂(ryMeasure n) = (3 / 8) ^ n := by
  have hrw : (fun θ : Fin n → ℝ => (ryKernel n θ) ^ 2)
      = (fun θ => ∏ k, Real.cos (θ k) ^ 4) := by
    funext θ
    simp only [ryKernel, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun k _ => by ring)
  calc ∫ θ, (ryKernel n θ) ^ 2 ∂(ryMeasure n)
      = ∫ θ, ∏ k, Real.cos (θ k) ^ 4 ∂(ryMeasure n) := by rw [hrw]
    _ = (∫ x, Real.cos x ^ 4 ∂unifAngle) ^ (Fintype.card (Fin n)) := by
        unfold ryMeasure; rw [integral_fintype_prod_eq_pow (fun t => Real.cos t ^ 4)]
    _ = (3 / 8) ^ n := by rw [integral_cos_pow4_unifAngle, Fintype.card_fin]

/-- Exact variance: `Var[κ_n] = (3/8)ⁿ - (1/4)ⁿ`. -/
theorem variance_ryKernel (n : ℕ) :
    variance (ryKernel n) (ryMeasure n) = (3 / 8) ^ n - (1 / 4) ^ n := by
  rw [variance_eq_sub (ryKernel_memLp n)]
  simp only [Pi.pow_apply]
  rw [mean_ryKernel_sq, mean_ryKernel,
    show ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4) ^ n by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]

theorem variance_ryKernel_le (n : ℕ) :
    variance (ryKernel n) (ryMeasure n) ≤ (3 / 8) ^ n := by
  rw [variance_ryKernel]
  have : (0 : ℝ) ≤ (1 / 4) ^ n := by positivity
  linarith

/-- **The tensor-product RY quantum kernel concentrates exponentially** (Thanasilp 2022),
with NO Haar assumption. -/
theorem ryKernel_concentrates :
    ExpConcentratedProb (fun n => ryMeasure n) (fun n => ryKernel n) := by
  refine expConcentratedProb_of_variance_le (fun n => ryMeasure n) (fun n => ryKernel n)
    (fun n => ryKernel_memLp n) (b := 8 / 3) (by norm_num) (C := 1) (by norm_num)
    (fun n => ?_)
  have hb : (3 / 8 : ℝ) ^ n = 1 / (8 / 3) ^ n := by
    rw [one_div, ← inv_pow]; congr 1; norm_num
  calc variance (ryKernel n) (ryMeasure n) ≤ (3 / 8) ^ n := variance_ryKernel_le n
    _ = 1 / (8 / 3) ^ n := hb

/-- The RY-kernel deviation probability vanishes as the qubit count grows: the kernel
landscape becomes exponentially flat, so a polynomial shot budget cannot resolve it. -/
theorem ryKernel_tendsto_zero {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n => (ryMeasure n) {θ | δ ≤ |ryKernel n θ - ∫ x, ryKernel n x ∂(ryMeasure n)|})
      Filter.atTop (nhds 0) :=
  ryKernel_concentrates.tendsto_zero hδ

end QuantumAlg
