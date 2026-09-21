/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianWickIsometry
import LeanPool.Malliavin.Malliavin.BrownianPurePowerRecurrence

/-!
# Mixed-inner characterization of the Hermite/multiple-integral identity

Concrete Brownian Wick powers and canonical pure-power multiple integrals already have identical
squared norms.  Consequently, their vector equality is equivalent to a single mixed-inner-product
formula.  This file packages that scalar endpoint and relates it to both the higher Hermite
identity and the pure-power Itô recurrence.
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

omit [CompleteSpace W] [BorelSpace W] in
/-- Equality of a Wick power and its canonical pure-power multiple integral is equivalent to
their mixed inner product attaining their common squared norm. -/
theorem brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
        brownianPurePowerIntegral hB n (stepToLp v) ↔
      inner ℝ (brownianWickPowerLp hB v n)
          (brownianPurePowerIntegral hB n (stepToLp v)) =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
  constructor
  · intro heq
    rw [heq, real_inner_self_eq_norm_sq,
      norm_sq_brownianPurePowerIntegral hB hsm n (stepToLp v)]
  · intro hinner
    let X := brownianWickPowerLp hB v n
    let Y := brownianPurePowerIntegral hB n (stepToLp v)
    change X = Y
    change inner ℝ X Y =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n at hinner
    have hX : ‖X‖ ^ 2 =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
      exact norm_sq_brownianWickPowerLp hB v n
    have hY : ‖Y‖ ^ 2 =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
      exact norm_sq_brownianPurePowerIntegral hB hsm n (stepToLp v)
    have hdiffInner : inner ℝ (X - Y) (X - Y) = 0 := by
      rw [real_inner_sub_sub_self, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, hX, hinner, hY]
      ring
    have hdiffNorm : ‖X - Y‖ ^ 2 = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hdiffInner
    have hnormZero : ‖X - Y‖ = 0 := by
      nlinarith [norm_nonneg (X - Y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)

omit [CompleteSpace W] [BorelSpace W] in
/-- The mixed-inner formula is automatic at order zero. -/
theorem brownianWickPurePowerMixedInner_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 0)
      (brownianPurePowerIntegral hB 0 (stepToLp v)) =
      (Nat.factorial 0 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 0 := by
  exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    hB hsm v 0).1 (brownianPurePowerIntegral_zero_step hB v).symm

omit [CompleteSpace W] [BorelSpace W] in
/-- The mixed-inner formula is automatic at order one. -/
theorem brownianWickPurePowerMixedInner_one
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 1)
      (brownianPurePowerIntegral hB 1 (stepToLp v)) =
      (Nat.factorial 1 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 1 := by
  exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    hB hsm v 1).1 (brownianPurePowerIntegral_one_step hB hsm v).symm

/-- The scalar mixed-inner-product statement at every order. -/
def BrownianWickPurePowerMixedInnerIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n,
    inner ℝ (brownianWickPowerLp hB v n)
        (brownianPurePowerIntegral hB n (stepToLp v)) =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n

/-- The scalar mixed-inner-product statement at every genuinely higher order. -/
def BrownianHigherWickPurePowerMixedInnerIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n →
    inner ℝ (brownianWickPowerLp hB v n)
        (brownianPurePowerIntegral hB n (stepToLp v)) =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n

omit [CompleteSpace W] [BorelSpace W] in
/-- Since the mixed-inner formula is automatic in orders zero and one, its all-orders and
genuinely higher-order forms are equivalent. -/
theorem wickPurePowerMixedInnerIdentity_iff_higher
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianWickPurePowerMixedInnerIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  constructor
  · intro hinner v n _
    exact hinner v n
  · intro hinner v n
    cases n with
    | zero => exact brownianWickPurePowerMixedInner_zero hB hsm v
    | succ n =>
        cases n with
        | zero => exact brownianWickPurePowerMixedInner_one hB hsm v
        | succ n => exact hinner v (Nat.succ (Nat.succ n)) (by omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- The higher Hermite/multiple-integral identity is exactly its mixed-inner scalar formula. -/
theorem higherHermiteMultipleIntegralIdentity_iff_mixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  constructor
  · intro hid v n hn
    exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
      hB hsm v n).1 (hid v n hn)
  · intro hinner v n hn
    exact (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
      hB hsm v n).2 (hinner v n hn)

omit [CompleteSpace W] [BorelSpace W] in
/-- Including the automatic base orders, the Hermite/multiple-integral identity is exactly the
full mixed-inner scalar formula. -/
theorem higherHermiteMultipleIntegralIdentity_iff_fullMixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianWickPurePowerMixedInnerIdentity hB := by
  calc
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
        BrownianHigherWickPurePowerMixedInnerIdentity hB :=
      higherHermiteMultipleIntegralIdentity_iff_mixedInner hB hsm
    _ ↔ BrownianWickPurePowerMixedInnerIdentity hB :=
      (wickPurePowerMixedInnerIdentity_iff_higher hB hsm).symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Equivalently, the pure-power Itô recurrence is exactly the higher mixed-inner formula. -/
theorem purePowerRecurrence_iff_mixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by
  rw [purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity hB hsm,
    higherHermiteMultipleIntegralIdentity_iff_mixedInner hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Equivalently, the pure-power Itô recurrence is exactly the full mixed-inner scalar
formula, whose base orders hold automatically. -/
theorem purePowerRecurrence_iff_fullMixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianWickPurePowerMixedInnerIdentity hB := by
  calc
    BrownianPurePowerHermiteRecurrence hB ↔
        BrownianHigherWickPurePowerMixedInnerIdentity hB :=
      purePowerRecurrence_iff_mixedInner hB hsm
    _ ↔ BrownianWickPurePowerMixedInnerIdentity hB :=
      (wickPurePowerMixedInnerIdentity_iff_higher hB hsm).symm

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
