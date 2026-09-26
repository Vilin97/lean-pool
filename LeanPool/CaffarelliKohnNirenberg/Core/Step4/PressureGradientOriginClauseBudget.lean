/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.OneSidedMorreyMonotone

/-!
# Pressure Gradient Origin Clause Budget

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-!
# Budget comparison for the one-sided pressure-gradient constant

The quantitative constant `oneSidedPressureGradientKP` is the one-sided
Morrey constant of a selected pressure gradient, evaluated with the two
numerical budgets fed to it by the local estimates.  This module records the
elementary comparison facts for that constant: monotonicity of the one-sided
Morrey bound in its two integral budgets, and the resulting bound of the
specialized constant by the general one with the budget factors made
explicit.  Both results are pure order arithmetic on `ℝ≥0∞`; no analytic
hypothesis enters.
-/

/-- The one-sided Morrey bound taken with the raw budget data is dominated by
the specialized constant `oneSidedPressureGradientKP`, whose budgets carry the
explicit factor `|C_CZ| + 1`. -/
theorem oneSidedMorreyBound_le_pressureGradientKP
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hA : A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hB : B ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁ A B ≤
      oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD := by
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (|C_CZ| + 1) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith only [abs_nonneg C_CZ])
  have hAle :
      A ≤ ENNReal.ofReal (|C_CZ| + 1) *
        (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) := by
    calc A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε) := hA
      _ = 1 * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) :=
        (one_mul _).symm
      _ ≤ ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) :=
        mul_le_mul' hc le_rfl
  have hBle :
      B ≤ ENNReal.ofReal (|C_CZ| + 1) *
        ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := by
    calc B ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := hB
      _ = 1 * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (|C_CZ| + 1) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) :=
        mul_le_mul' hc le_rfl
  dsimp [oneSidedPressureGradientKP]
  exact oneSidedMorreyBound_mono (by norm_num) hAle hBle

end CKN.Core.Step4
