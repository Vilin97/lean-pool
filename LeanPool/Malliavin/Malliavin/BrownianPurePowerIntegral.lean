/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.IteratedKernelPurePower
import LeanPool.Malliavin.Malliavin.BrownianPolynomialHermite

/-!
# Canonical Brownian multiple integrals of pure-power kernels

This file evaluates the Hilbert-space laws of the genuine Brownian multiple-integral operator on
deterministic pure powers.  Symmetry removes the explicit symmetrization, and the deterministic
pure-power inner-product formula gives the usual factorial isometry.  At order one the resulting
operator is identified with the concrete Brownian Wick power of a finite step kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- The genuine order-`n` Brownian multiple integral of the pure power `f^{⊗n}`. -/
noncomputable def brownianPurePowerIntegral (hB : IsPreBrownianReal B P)
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) : RandomL2 P :=
  brownianMultipleIntegralCLM hB n (iteratedKernelPurePower n f)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Symmetry of a pure-power kernel removes symmetrization from its multiple integral. -/
theorem brownianPurePowerIntegral_eq_integralCLM
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB n f =
      (n.factorial : ℝ) • integralCLM hB n (iteratedKernelPurePower n f) := by
  rw [brownianPurePowerIntegral, brownianMultipleIntegralCLM_apply,
    symmetrizeL_iteratedKernelPurePower]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A pure-power multiple integral belongs to its canonical Brownian homogeneous chaos. -/
theorem brownianPurePowerIntegral_mem_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB n f ∈ brownianHomogeneousChaos hB n := by
  rw [brownianPurePowerIntegral_eq_integralCLM]
  exact (brownianHomogeneousChaos hB n).smul_mem (n.factorial : ℝ)
    (integralCLM_mem_brownianHomogeneousChaos hB n (iteratedKernelPurePower n f))

omit [CompleteSpace W] [BorelSpace W] in
/-- Every positive-order Brownian pure-power multiple integral is centered. -/
theorem integral_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (hn : 0 < n) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∫ w, brownianPurePowerIntegral hB n f w ∂P = 0 := by
  rw [brownianPurePowerIntegral_eq_integralCLM]
  rw [integral_congr_ae
    (Lp.coeFn_smul (n.factorial : ℝ)
      (integralCLM hB n (iteratedKernelPurePower n f)))]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul,
    integralCLM_centered hB hsm positiveOrderedBoxDense n hn, mul_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- Factorial isometry for genuine Brownian multiple integrals of pure powers. -/
theorem inner_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB n f)
        (brownianPurePowerIntegral hB n g) =
      (n.factorial : ℝ) * inner ℝ f g ^ n := by
  rw [brownianPurePowerIntegral, brownianPurePowerIntegral,
    inner_brownianMultipleIntegralCLM hB hsm,
    symmetrizeL_iteratedKernelPurePower, symmetrizeL_iteratedKernelPurePower,
    inner_iteratedKernelPurePower]

omit [CompleteSpace W] [BorelSpace W] in
/-- Pure-power multiple integrals of different orders are orthogonal. -/
theorem inner_brownianPurePowerIntegral_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB m f)
      (brownianPurePowerIntegral hB n g) = 0 := by
  exact inner_brownianMultipleIntegralCLM_of_ne hB hsm hmn
    (iteratedKernelPurePower m f) (iteratedKernelPurePower n g)

omit [CompleteSpace W] [BorelSpace W] in
/-- Squared norm of a genuine Brownian multiple integral of a pure power. -/
theorem norm_sq_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖brownianPurePowerIntegral hB n f‖ ^ 2 =
      (n.factorial : ℝ) * (‖f‖ ^ 2) ^ n := by
  simpa only [real_inner_self_eq_norm_sq] using
    inner_brownianPurePowerIntegral hB hsm n f f

omit [CompleteSpace W] [BorelSpace W] in
/-- Exact norm of a genuine Brownian multiple integral of a pure power. -/
theorem norm_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖brownianPurePowerIntegral hB n f‖ =
      Real.sqrt (n.factorial : ℝ) * ‖f‖ ^ n := by
  have hpow : (‖f‖ ^ 2) ^ n = (‖f‖ ^ n) ^ 2 := by
    calc
      (‖f‖ ^ 2) ^ n = ‖f‖ ^ (2 * n) := (pow_mul ‖f‖ 2 n).symm
      _ = ‖f‖ ^ (n * 2) := by rw [Nat.mul_comm 2 n]
      _ = (‖f‖ ^ n) ^ 2 := pow_mul ‖f‖ n 2
  have h := congrArg Real.sqrt (norm_sq_brownianPurePowerIntegral hB hsm n f)
  rw [hpow] at h
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (pow_nonneg (norm_nonneg _) n)] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Under the order-one kernel equivalence, a pure power is its original time kernel. -/
theorem kernelToLine_iteratedKernelPurePower_one
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    kernelToLine (iteratedKernelPurePower 1 f) = f := by
  unfold kernelToLine
  change Lp.compMeasurePreserving
      (MeasurableEquiv.funUnique (Fin 1) ℝ≥0).symm
      measurePreserving_funUnique_symm_nnreal (iteratedKernelPurePower 1 f) = f
  apply Lp.ext
  have hmap := Lp.coeFn_compMeasurePreserving (iteratedKernelPurePower 1 f)
    measurePreserving_funUnique_symm_nnreal
  have hpure := measurePreserving_funUnique_symm_nnreal.quasiMeasurePreserving.ae_eq_comp
    (coeFn_iteratedKernelPurePower 1 f)
  filter_upwards [hmap, hpure] with t hmap_t hpure_t
  rw [hmap_t, hpure_t]
  simp [iteratedKernelPurePowerFun, MeasurableEquiv.funUnique_symm_apply]

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The genuine zeroth multiple integral of any pure power is the constant one. -/
theorem brownianPurePowerIntegral_zero
    (hB : IsPreBrownianReal B P) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB 0 f = Lp.const 2 P (1 : ℝ) := by
  rw [brownianPurePowerIntegral_eq_integralCLM]
  simp only [Nat.factorial_zero, Nat.cast_one, one_smul]
  have hpure :
      (∫ t, iteratedKernelPurePower 0 f t ∂iteratedKernelMeasure 0) = 1 := by
    rw [integral_congr_ae (coeFn_iteratedKernelPurePower 0 f)]
    simp [iteratedKernelPurePowerFun]
  apply Lp.ext
  filter_upwards [integralCLM_zeroOrder hB (iteratedKernelPurePower 0 f),
    Lp.coeFn_const 2 P (1 : ℝ)] with w hintegral hone
  rw [hintegral, hpure, hone]
  rfl

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- At order zero the pure-power multiple integral agrees with the concrete Wick power. -/
theorem brownianPurePowerIntegral_zero_step
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianPurePowerIntegral hB 0 (stepToLp v) = brownianWickPowerLp hB v 0 := by
  rw [brownianPurePowerIntegral_zero, brownianWickPowerLp_zero]

/-- The genuine first multiple integral of a Brownian step kernel is its first Wick power. -/
theorem brownianPurePowerIntegral_one_step
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    brownianPurePowerIntegral hB 1 (stepToLp v) = brownianWickPowerLp hB v 1 := by
  rw [brownianPurePowerIntegral,
    brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel hB hsm,
    wienerIntegralKernel_apply, kernelToLine_iteratedKernelPurePower_one,
    wienerIntegral_stepToLp, brownianWickPowerLp_one]

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
