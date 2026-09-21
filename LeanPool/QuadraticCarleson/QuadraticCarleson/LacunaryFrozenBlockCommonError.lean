/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseCommonErrorWeak
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryFrozenInputL0
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleKalton

/-!
# Passing a common-error finite maximum to the actual frozen block

This adapter retains the exact frozen input and its mass.  It uses a
logarithm-squared weak estimate for a finite family and a pointwise comparison
with one common maximal-function error.  The hypotheses are exposed until
the concrete high-scale family is supplied.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson.LacunaryFrozenBlockCommonError

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLowFullEstimate
open LacunaryMiddleRange LacunaryMiddleOperator LacunaryMiddleKalton
open LacunaryFrozenInputL0 KaltonPaperApplication ExtendedWeakL1Combinators
open FiniteSparseCommonErrorWeak


/-- The exact frozen-block weak hypothesis follows from the finite-family
estimate and a single `48 M` comparison error.  No positivity of the block
size is required: `paperLog 1 B ≥ 1` holds also for the empty block. -/
theorem hasLogSquaredFrozenBlockWeakBounds_of_common_error
    (f : L0Infinity) (B : ℕ → ℕ) (c : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (T : (k : ℕ) → (τ : ℤ) → Fin (Q (B k) τ).card → TestOperator)
    (hweak : ∀ (k : ℕ) (τ : ℤ),
      HasWeakOneOneBound (D * paperLog 1 (B k : ℝ) ^ 2) (finiteMax (T k τ)))
    (hpoint : ∀ (k : ℕ) (τ : ℤ) (x : ℝ),
      frozenBlockMaxEnorm lacunaryAmplitude f k (B k) c τ x ≤
        ENNReal.ofReal (finiteMax (T k τ) (frozenBlockInputL0 f k (B k) c τ) x) +
          48 * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖frozenBlockInputL0 f k (B k) c τ y‖ₑ) x) :
    HasLogSquaredFrozenBlockWeakBounds (f : ℝ → ℂ) B c (2 * D + 384) := by
  refine ⟨by positivity, ?_⟩
  intro k τ a ha
  let g := frozenBlockInputL0 f k (B k) c τ
  let mass := frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ
  let L := paperLog 1 (B k : ℝ)
  have hmass : mass ≠ ∞ := g.integrable.hasFiniteIntegral.ne
  have hL : 1 ≤ L := PositiveEndpointOptimization.one_le_paperLog_one
    (by positivity : 0 ≤ (B k : ℝ))
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hcoefficient : 2 * (D * L ^ 2) + 384 ≤ (2 * D + 384) * L ^ 2 := by
    nlinarith
  have hsmall := hasExtendedWeakL1Bound_of_finiteMax_add_fortyEight_maximal
    (T k τ) (mul_nonneg hD (sq_nonneg L)) (hweak k τ) g (hpoint k τ)
  have hglobal : HasExtendedWeakL1Bound volume
      (((2 * D + 384) * L ^ 2) * mass.toReal)
      (frozenBlockMaxEnorm lacunaryAmplitude f k (B k) c τ) :=
    ExtendedWeakL1Combinators.HasExtendedWeakL1Bound.mono_constant hsmall
      (mul_le_mul_of_nonneg_right hcoefficient ENNReal.toReal_nonneg)
  have hrestricted := ExtendedWeakL1Combinators.HasExtendedWeakL1Bound.restrict hglobal
    (fivefoldExceptionalSet (stoppingCenter (f := (f : ℝ → ℂ))) stoppingLength)ᶜ
  apply (hrestricted.2 a ha).trans_eq
  change ENNReal.ofReal (((2 * D + 384) * L ^ 2) * mass.toReal) =
    ENNReal.ofReal ((2 * D + 384) * L ^ 2) * mass
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * D + 384) * L ^ 2),
    ENNReal.ofReal_toReal hmass]


end QuadraticCarleson.LacunaryFrozenBlockCommonError
