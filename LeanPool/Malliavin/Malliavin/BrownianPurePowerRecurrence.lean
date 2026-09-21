/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianHermiteMultipleIntegral

/-!
# The pure-power recurrence endpoint

The generalized Hermite values satisfy a two-step recurrence whose leading term is pointwise
multiplication by the underlying Brownian step sum.  This file packages that leading term in
`RandomL2`, proves the Wick recurrence, and shows that the higher Hermite/multiple-integral
identity is equivalent to the matching recurrence for canonical pure-power multiple integrals.
Thus the remaining all-order stochastic input can be stated as the usual Itô product recurrence.
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

/-- The `L²` polynomial value representing a Brownian step sum multiplied by its order-`n`
Wick power. -/
noncomputable def brownianStepTimesWickPowerLp
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  polynomialFamilyLinearMap (brownianStepPowerLp hB v)
    (Polynomial.X * varianceHermite (‖stepToLp v‖ ^ 2) n)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The recurrence's leading term has the intended pointwise product representative. -/
theorem coeFn_brownianStepTimesWickPowerLp
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianStepTimesWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ stepSum B v w *
        (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by
  have h := coeFn_polynomialFamilyLinearMap
    (brownianStepPowerLp hB v) (stepSum B v)
    (fun k ↦ MemLp.coeFn_toLp (memLp_two_stepSum_pow hB v k))
    (Polynomial.X * varianceHermite (‖stepToLp v‖ ^ 2) n)
  filter_upwards [h] with w hw
  rw [brownianStepTimesWickPowerLp, hw, Polynomial.eval_mul,
    Polynomial.eval_X]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Generalized Brownian Wick powers satisfy the Hermite two-step recurrence in `RandomL2`. -/
theorem brownianWickPowerLp_add_two
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v (n + 2) =
      brownianStepTimesWickPowerLp hB v (n + 1) -
        (‖stepToLp v‖ ^ 2 * ((n + 1 : ℕ) : ℝ)) •
          brownianWickPowerLp hB v n := by
  unfold brownianWickPowerLp brownianStepTimesWickPowerLp
  rw [show n + 2 = (n + 1) + 1 by omega,
    varianceHermite_succ, map_sub, ← Polynomial.smul_eq_C_mul, map_smul,
    Nat.add_sub_cancel]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- At the first recurrence step, multiplication by the step sum gives its raw square. -/
theorem brownianStepTimesWickPowerLp_one
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianStepTimesWickPowerLp hB v 1 = brownianStepPowerLp hB v 2 := by
  simpa only [brownianStepTimesWickPowerLp, varianceHermite, pow_two] using
    (polynomialFamilyLinearMap_X_pow (brownianStepPowerLp hB v) 2)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The second Wick power is the raw square minus its variance. -/
theorem brownianWickPowerLp_two
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 2 =
      brownianStepPowerLp hB v 2 -
        ‖stepToLp v‖ ^ 2 • Lp.const 2 P (1 : ℝ) := by
  simpa only [Nat.zero_add, Nat.cast_one, mul_one,
    brownianStepTimesWickPowerLp_one, brownianWickPowerLp_zero] using
    (brownianWickPowerLp_add_two hB v 0)

/-- The remaining Itô product input, stated as the matching two-step recurrence for canonical
pure-power multiple integrals. -/
def BrownianPurePowerHermiteRecurrence (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n,
    brownianPurePowerIntegral hB (n + 2) (stepToLp v) =
      brownianStepTimesWickPowerLp hB v (n + 1) -
        (‖stepToLp v‖ ^ 2 * ((n + 1 : ℕ) : ℝ)) •
          brownianPurePowerIntegral hB n (stepToLp v)

omit [CompleteSpace W] [BorelSpace W] in
/-- The pure-power recurrence and the automatic base orders identify every canonical pure-power
integral with its Wick power. -/
theorem brownianPurePowerIntegral_eq_wickPower_of_recurrence
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hrec : BrownianPurePowerHermiteRecurrence hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianPurePowerIntegral hB n (stepToLp v) =
      brownianWickPowerLp hB v n := by
  induction n using Nat.twoStepInduction with
  | zero => exact brownianPurePowerIntegral_zero_step hB v
  | one => exact brownianPurePowerIntegral_one_step hB hsm v
  | more n hn _hn1 =>
      rw [hrec v n, brownianWickPowerLp_add_two, hn]

omit [CompleteSpace W] [BorelSpace W] in
/-- The matching pure-power recurrence implies the full higher Hermite/multiple-integral
identity. -/
theorem higherHermiteMultipleIntegralIdentity_of_purePowerRecurrence
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hrec : BrownianPurePowerHermiteRecurrence hB) :
    BrownianHigherHermiteMultipleIntegralIdentity hB := by
  intro v n _hn
  exact (brownianPurePowerIntegral_eq_wickPower_of_recurrence
    hB hsm hrec v n).symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Conversely, the higher Hermite/multiple-integral identity forces the matching pure-power
recurrence. -/
theorem purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianPurePowerHermiteRecurrence hB := by
  intro v n
  rw [← brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
      hB hsm hid v (n + 2),
    ← brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
      hB hsm hid v n,
    brownianWickPowerLp_add_two]

omit [CompleteSpace W] [BorelSpace W] in
/-- The all-order identity is exactly the pure-power Itô product recurrence. -/
theorem purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianHigherHermiteMultipleIntegralIdentity hB := by
  exact ⟨higherHermiteMultipleIntegralIdentity_of_purePowerRecurrence hB hsm,
    purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity hB hsm⟩

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
