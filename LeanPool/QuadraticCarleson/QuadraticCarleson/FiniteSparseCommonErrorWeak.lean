/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.ExtendedWeakL1Combinators
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison

/-!
# A finite sparse maximum with one common maximal-function error

The exact frozen block comparison leaves one Hardy--Littlewood error outside
the finite modulation maximum. Its weak bound therefore costs one absolute
constant, independently of the number of modulations.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson.FiniteSparseCommonErrorWeak

open KaltonPaperApplication


/-- A pointwise error of `48 M f` adds only `384 ‖f‖₁` to the weak constant.
The proof uses the level split at `a / 2` and `a / 96`, retaining the exact
input mass and requiring no additional measurability of the dominated output. -/
theorem hasExtendedWeakL1Bound_of_finiteMax_add_fortyEight_maximal
    {N : ℕ} (T : Fin N → TestOperator) {C : ℝ} (hC : 0 ≤ C)
    (hweak : HasWeakOneOneBound C (finiteMax T))
    (f : L0Infinity) {F : ℝ → ℝ≥0∞}
    (hpoint : ∀ x, F x ≤ ENNReal.ofReal (finiteMax T f x) +
      48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :
    HasExtendedWeakL1Bound volume
      ((2 * C + 384) * (∫⁻ x, ‖f x‖ₑ).toReal) F := by
  let mass : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ
  have hmass : mass ≠ ∞ := f.integrable.hasFiniteIntegral.ne
  refine ⟨mul_nonneg (by positivity) ENNReal.toReal_nonneg, ?_⟩
  intro a ha
  let EH : Set ℝ := {x | a / 2 < finiteMax T f x}
  let EM : Set ℝ := {x | ENNReal.ofReal (a / 96) <
    centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x}
  have ha2 : 0 < a / 2 := by positivity
  have ha96 : 0 < a / 96 := by positivity
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h96 : (96 : ℝ≥0∞) * ENNReal.ofReal (a / 96) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 96)]
    congr 1
    ring
  have h48 : (48 : ℝ≥0∞) * ENNReal.ofReal (a / 96) =
      ENNReal.ofReal (a / 2) := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 48)]
    congr 1
    ring
  have hhalf : ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) =
      ENNReal.ofReal a := by
    rw [← two_mul, htwo]
  have hsub : {x | ENNReal.ofReal a < F x} ⊆ EH ∪ EM := by
    intro x hx
    by_contra hxunion
    have hxH : finiteMax T f x ≤ a / 2 :=
      le_of_not_gt fun hlt ↦ hxunion (Or.inl hlt)
    have hxM : centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x ≤
        ENNReal.ofReal (a / 96) :=
      le_of_not_gt fun hlt ↦ hxunion (Or.inr hlt)
    have hupper : F x ≤ ENNReal.ofReal a := by
      calc
        F x ≤ ENNReal.ofReal (finiteMax T f x) +
            48 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := hpoint x
        _ ≤ ENNReal.ofReal (a / 2) + 48 * ENNReal.ofReal (a / 96) :=
          add_le_add (ENNReal.ofReal_le_ofReal hxH) (mul_le_mul' le_rfl hxM)
        _ = ENNReal.ofReal a := by rw [h48, hhalf]
    exact (not_lt_of_ge hupper) hx
  have hH : ENNReal.ofReal (a / 2) * volume EH ≤ ENNReal.ofReal C * mass :=
    hweak f (a / 2) ha2
  have hM : ENNReal.ofReal (a / 96) * volume EM ≤ 4 * mass :=
    centeredHardyLittlewoodMaximal_weak_bound
      (fun y ↦ ‖f y‖ₑ) (ENNReal.ofReal (a / 96))
  calc
    ENNReal.ofReal a * volume {x | ENNReal.ofReal a < F x} ≤
        ENNReal.ofReal a * (volume EH + volume EM) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans (measure_union_le EH EM))
    _ = 2 * (ENNReal.ofReal (a / 2) * volume EH) +
        96 * (ENNReal.ofReal (a / 96) * volume EM) := by
      rw [mul_add]
      exact congrArg₂ (· + ·)
        (by rw [← htwo, mul_assoc]) (by rw [← h96, mul_assoc])
    _ ≤ 2 * (ENNReal.ofReal C * mass) + 96 * (4 * mass) :=
      add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl hM)
    _ = ENNReal.ofReal ((2 * C + 384) * mass.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * C + 384),
        ENNReal.ofReal_toReal hmass,
        ENNReal.ofReal_add (by positivity : 0 ≤ 2 * C) (by norm_num),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
      ring


end QuadraticCarleson.FiniteSparseCommonErrorWeak
