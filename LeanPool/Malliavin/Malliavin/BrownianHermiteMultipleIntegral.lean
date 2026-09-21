/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianPurePowerIntegral

/-!
# Brownian Hermite powers as multiple integrals

This file isolates the exact remaining stochastic identity needed to pass from generalized
Hermite powers of finite Brownian step sums to the canonical multiple-integral construction.
Orders zero and one have already been identified unconditionally, so the endpoint hypothesis
only concerns orders at least two.  Under that hypothesis, homogeneous-chaos membership gives
ordered-chain compatibility and hence natural martingale representation.
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

/-- The genuinely higher-order Hermite/multiple-integral identity for finite Brownian step
kernels. -/
def BrownianHigherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n →
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v)

/-- The higher-order identity, together with the automatic base orders, identifies every Wick
power with its canonical pure-power multiple integral. -/
theorem brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v) := by
  cases n with
  | zero => exact (brownianPurePowerIntegral_zero_step hB v).symm
  | succ n =>
      cases n with
      | zero => exact (brownianPurePowerIntegral_one_step hB hsm v).symm
      | succ n => exact hid v (Nat.succ (Nat.succ n)) (by omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- The Hermite/multiple-integral identity puts every higher Wick power in the ordered-chain
closure. -/
theorem brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianHigherWickChainCompatible hB := by
  intro v n hn
  rw [hid v n hn]
  exact brownianHomogeneousChaos_le_orderedChainSpan_closure hB hsm n
    (brownianPurePowerIntegral_mem_brownianHomogeneousChaos
      hB n (stepToLp v))

omit [CompleteSpace W] [BorelSpace W] in
/-- The Hermite/multiple-integral identity supplies Wick-chain compatibility at every order. -/
theorem brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianWickChainCompatible hB := by
  exact (brownianWickChainCompatible_iff_higher hB).2
    (brownianHigherWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)

omit [CompleteSpace W] [BorelSpace W] in
/-- The Hermite/multiple-integral identity makes the ordered Brownian chain span dense. -/
theorem dense_orderedChainSpan_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hgen : IsWienerGenerated B)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  exact dense_orderedChainSpan_of_wickChainCompatible hB hgen
    (brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)

omit [CompleteSpace W] [BorelSpace W] in
/-- The Hermite/multiple-integral identity yields natural martingale representation. -/
theorem naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (hgen : IsWienerGenerated B)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  exact naturalMartingaleRepresentation_of_wickChainCompatible
    hB hsm hnat hgen
    (brownianWickChainCompatible_of_hermiteMultipleIntegralIdentity
      hB hsm hid)

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
