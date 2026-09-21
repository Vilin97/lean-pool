/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.ExtendedWeakL1Combinators
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleKalton

/-!
# Reduction of a frozen middle block to a finite quadratic-Hilbert block

This file applies the smooth-kernel comparison to the genuine frozen inputs.
It isolates the remaining finite-modulation estimate at precisely the sharp
quadratic Hilbert maximal truncation occurring in the paper.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryMiddleBlockWeak

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLowFullEstimate
open KaltonPaperApplication ExtendedWeakL1Combinators
open LacunaryMiddleOperator LacunaryMiddleKalton


/-- A weak bound for the finite quadratic-Hilbert modulation block transfers
to the genuine smooth low-kernel block. The extra constant is exactly the
Hardy--Littlewood boundary contribution. -/
theorem hasExtendedWeakL1Bound_frozenBlockMaxEnorm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ) {AH : ℝ}
    (hH : HasExtendedWeakL1Bound
      (volume.restrict (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ)
      AH (frozenBlockHilbertMaxEnorm A f k B c τ)) :
    HasExtendedWeakL1Bound
      (volume.restrict (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ)
      (4 * AH + 128 * (frozenBlockInputL1Mass A f k B c τ).toReal)
      (frozenBlockMaxEnorm A f k B c τ) := by
  have hfm := measurable_frozenBlockInput (A := A) hf k B c τ
  have hfi' := integrable_frozenBlockInput (A := A) hf hfi hAk B c τ
  have hM := ExtendedWeakL1Combinators.HasExtendedWeakL1Bound.restrict
    (hasExtendedWeakL1Bound_centeredHardyLittlewoodMaximal_enorm hfi')
    (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ
  have h := hasExtendedWeakL1Bound_of_le_two_mul_add_sixteen_mul
    (frozenBlockMaxEnorm_le_hilbertMax_add_maximal hf hfi hAk B c τ) hH hM
  convert h using 1; simp only [frozenBlockInputL1Mass]; ring

/-- The exact remaining Hilbert-block input: a single finite block has the
paper's logarithm-squared weak constant. -/
def HasLogSquaredFrozenHilbertBlockWeakBounds
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (k : ℕ) (τ : ℤ), HasExtendedWeakL1Bound
    (volume.restrict (fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength)ᶜ)
    ((C * paperLog 1 (B k : ℝ) ^ 2) *
      (frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ).toReal)
    (frozenBlockHilbertMaxEnorm lacunaryAmplitude f k (B k) c τ)

/-- A logarithm-squared finite quadratic-Hilbert estimate implies the exact
frozen low-kernel hypothesis needed by the Kalton assembly. -/
theorem logSquaredFrozenBlockWeakBounds_of_hilbert
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {C : ℝ}
    (hH : HasLogSquaredFrozenHilbertBlockWeakBounds f B c C) :
    HasLogSquaredFrozenBlockWeakBounds f B c (4 * C + 128) := by
  refine ⟨by linarith [hH.1], ?_⟩
  intro k τ a ha
  let mass := frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ
  let L := paperLog 1 (B k : ℝ)
  have hfi' := integrable_frozenBlockInput (A := lacunaryAmplitude) hf hfi
    (lacunaryAmplitude_pos k).le (B k) c τ
  have hmass_ne : mass ≠ ∞ := hfi'.hasFiniteIntegral.ne
  have hmass0 : 0 ≤ mass.toReal := ENNReal.toReal_nonneg
  have hL : 1 ≤ L := by
    change 1 ≤ paperLog 1 (B k : ℝ)
    exact PositiveEndpointOptimization.one_le_paperLog_one
      (t := (B k : ℝ)) (by positivity)
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hC' : 0 ≤ 4 * C + 128 := by linarith [hH.1]
  have hconstant :
      4 * ((C * L ^ 2) * mass.toReal) + 128 * mass.toReal ≤
        ((4 * C + 128) * L ^ 2) * mass.toReal := by
    nlinarith [hH.1]
  have hlow := hasExtendedWeakL1Bound_frozenBlockMaxEnorm hf hfi
    (lacunaryAmplitude_pos k).le (B k) c τ (hH.2 k τ)
  have hlow' := ExtendedWeakL1Combinators.HasExtendedWeakL1Bound.mono_constant
    hlow hconstant
  apply (hlow'.2 a ha).trans_eq
  change ENNReal.ofReal (((4 * C + 128) * L ^ 2) * mass.toReal) =
    ENNReal.ofReal ((4 * C + 128) * L ^ 2) * mass
  rw [ENNReal.ofReal_mul (mul_nonneg hC' (sq_nonneg L)),
    ENNReal.ofReal_toReal hmass_ne]


end LacunaryMiddleBlockWeak
end QuadraticCarleson
