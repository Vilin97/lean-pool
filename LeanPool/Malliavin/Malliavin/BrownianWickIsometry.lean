/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.GaussianHermite
import LeanPool.Malliavin.Malliavin.BrownianPolynomialHermite

/-!
# Hilbert-space laws of Brownian Wick powers

The exact centered Gaussian law of each finite Brownian step sum transfers generalized-Hermite
orthogonality to the concrete `L²` Wick powers used in the Brownian chaos reduction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A finite Brownian step sum has the centered Gaussian law with variance equal to the squared
norm of its deterministic step kernel. -/
theorem map_stepSum_eq_gaussianReal (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    P.map (stepSum B v) = gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
  calc
    P.map (stepSum B v) = P.map (stepToRandom hB v : W → ℝ) :=
      (Measure.map_congr (coeFn_stepToRandom hB v)).symm
    _ = P.map (wienerIntegral hB (stepToLp v) : W → ℝ) := by
      rw [wienerIntegral_stepToLp]
    _ = gaussianReal 0 (‖stepToLp v‖₊ ^ 2) :=
      map_wienerIntegral_eq_gaussianReal hB (stepToLp v)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The second moment of a finite Brownian step sum is the squared norm of its deterministic
step kernel. -/
theorem integral_stepSum_sq (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, stepSum B v w ^ 2 ∂P) = ‖stepToLp v‖ ^ 2 := by
  calc
    (∫ w, stepSum B v w ^ 2 ∂P) =
        ∫ x, x ^ 2 ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, x ^ 2 ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = ‖stepToLp v‖ ^ 2 := by
      rw [integral_sq_centeredGaussian]
      simp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The fourth moment of a finite Brownian step sum is three times the squared variance. -/
theorem integral_stepSum_pow_four (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, stepSum B v w ^ 4 ∂P) = 3 * (‖stepToLp v‖ ^ 2) ^ 2 := by
  calc
    (∫ w, stepSum B v w ^ 4 ∂P) =
        ∫ x, x ^ 4 ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, x ^ 4 ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = 3 * (‖stepToLp v‖ ^ 2) ^ 2 := by
      rw [integral_pow_four_centeredGaussian]
      simp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The centered square of a finite Brownian step sum has second moment twice the squared
variance. -/
theorem integral_stepSum_sq_sub_variance_sq
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, (stepSum B v w ^ 2 - ‖stepToLp v‖ ^ 2) ^ 2 ∂P) =
      2 * (‖stepToLp v‖ ^ 2) ^ 2 := by
  calc
    (∫ w, (stepSum B v w ^ 2 - ‖stepToLp v‖ ^ 2) ^ 2 ∂P) =
        ∫ x, (x ^ 2 - ‖stepToLp v‖ ^ 2) ^ 2
          ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, (x ^ 2 - ‖stepToLp v‖ ^ 2) ^ 2
          ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = 2 * (‖stepToLp v‖ ^ 2) ^ 2 := by
      have h :=
        integral_sq_sub_variance_sq_centeredGaussian (‖stepToLp v‖₊ ^ 2)
      simpa using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Wick powers of one finite Brownian step sum are orthogonal, with the usual factorial norm. -/
theorem inner_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (m n : ℕ) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) =
      if m = n then m.factorial * (‖stepToLp v‖ ^ 2) ^ m else 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ w, inner ℝ (brownianWickPowerLp hB v m w)
        (brownianWickPowerLp hB v n w) ∂P) =
        ∫ w, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval (stepSum B v w) *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_brownianWickPowerLp hB v m,
        coeFn_brownianWickPowerLp hB v n] with w hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval x *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval x *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x
          ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = if m = n then m.factorial * (‖stepToLp v‖ ^ 2) ^ m else 0 := by
      have hvariance : ((↑(‖stepToLp v‖₊ ^ 2) : ℝ)) = ‖stepToLp v‖ ^ 2 := by
        simp
      have horth :=
        integral_varianceHermite_mul_centeredGaussian (‖stepToLp v‖₊ ^ 2) m n
      rw [hvariance] at horth
      exact horth

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Wick powers of different orders of the same step sum are orthogonal. -/
theorem inner_brownianWickPowerLp_of_ne (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) = 0 := by
  rw [inner_brownianWickPowerLp, ite_eq_right hmn]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Squared norm of a Brownian Wick power. -/
theorem norm_sq_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    ‖brownianWickPowerLp hB v n‖ ^ 2 =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
  rw [← real_inner_self_eq_norm_sq, inner_brownianWickPowerLp, ite_eq_left rfl]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Every positive-order Brownian Wick power is centered. -/
theorem integral_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ w, brownianWickPowerLp hB v n w ∂P = 0 := by
  calc
    (∫ w, brownianWickPowerLp hB v n w ∂P) =
        ∫ w, (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) ∂P := by
      apply integral_congr_ae
      exact coeFn_brownianWickPowerLp hB v n
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x
          ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x
          ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = 0 := by
      have hvariance : ((↑(‖stepToLp v‖₊ ^ 2) : ℝ)) = ‖stepToLp v‖ ^ 2 := by
        simp
      have hcenter :=
        integral_varianceHermite_centeredGaussian (‖stepToLp v‖₊ ^ 2) n
      rw [hvariance] at hcenter
      rw [hcenter, ite_eq_right (Nat.ne_of_gt hn)]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Exact norm of a Brownian Wick power. -/
theorem norm_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    ‖brownianWickPowerLp hB v n‖ =
      Real.sqrt (n.factorial : ℝ) * ‖stepToLp v‖ ^ n := by
  have hpow : (‖stepToLp v‖ ^ 2) ^ n = (‖stepToLp v‖ ^ n) ^ 2 := by
    calc
      (‖stepToLp v‖ ^ 2) ^ n = ‖stepToLp v‖ ^ (2 * n) :=
        (pow_mul ‖stepToLp v‖ 2 n).symm
      _ = ‖stepToLp v‖ ^ (n * 2) := by rw [Nat.mul_comm 2 n]
      _ = (‖stepToLp v‖ ^ n) ^ 2 := pow_mul ‖stepToLp v‖ n 2
  have h := congrArg Real.sqrt (norm_sq_brownianWickPowerLp hB v n)
  rw [hpow] at h
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (pow_nonneg (norm_nonneg _) n)] using h

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
