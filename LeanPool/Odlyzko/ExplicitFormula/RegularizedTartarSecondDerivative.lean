/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.TartarSecondDerivativeBounds
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Regularized Tartar Second Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real

namespace NumberField.Odlyzko

/-- A regularized scaled tartar second derivative used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartarSecondDerivative
    (y δ x : ℝ) : ℝ :=
  (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
      2 * δ * scaledTartarTestFunction y x -
      4 * δ * x * (y * deriv Tartar.testFunction (y * x)) +
      4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x) *
    Real.exp (-δ * x ^ 2)

private theorem hasDerivAt_scaledTartarTestFunctionDerivative (y x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ y * deriv Tartar.testFunction (y * z))
      (y ^ 2 * tartarTestFunctionSecondDerivative (y * x)) x := by
  have h := (hasDerivAt_deriv_tartarTestFunction (y * x)).comp x
    ((hasDerivAt_id x).const_mul y)
  exact h.const_mul y |>.congr_deriv (by ring)

theorem hasDerivAt_regularizedScaledTartarDerivative (y δ x : ℝ) :
    HasDerivAt (regularizedScaledTartarDerivative y δ)
      (regularizedScaledTartarSecondDerivative y δ x) x := by
  let f : ℝ → ℝ := scaledTartarTestFunction y
  let f' : ℝ → ℝ := fun z ↦ y * deriv Tartar.testFunction (y * z)
  let g : ℝ → ℝ := fun z ↦ Real.exp (-δ * z ^ 2)
  have hf : HasDerivAt f (f' x) x := by
    exact hasDerivAt_scaledTartarTestFunction y x
  have hf' : HasDerivAt f'
      (y ^ 2 * tartarTestFunctionSecondDerivative (y * x)) x := by
    exact hasDerivAt_scaledTartarTestFunctionDerivative y x
  have hg : HasDerivAt g (-2 * δ * x * g x) x := by
    dsimp [g]
    have h := (((hasDerivAt_id x).pow 2).const_mul (-δ)).exp
    convert h using 1 <;> simp only [Pi.pow_apply, id_eq]
    ring
  have hinside :
      HasDerivAt (fun z ↦ f' z - 2 * δ * z * f z)
        (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
          2 * δ * f x - 2 * δ * x * f' x) x := by
    have h := hf'.sub ((((hasDerivAt_id x).const_mul (2 * δ)).mul hf))
    have he :
        HasDerivAt (fun z ↦ f' z - 2 * δ * z * f z)
          (y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
            (2 * δ * 1 * f x + 2 * δ * x * f' x)) x :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z ↦ rfl)
    grind
  have hprod := hinside.mul hg
  unfold regularizedScaledTartarDerivative
    regularizedScaledTartarSecondDerivative
  dsimp [f, f', g] at hprod
  exact hprod.congr_deriv (by ring)

theorem abs_regularizedScaledTartarSecondDerivative_le
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    |regularizedScaledTartarSecondDerivative y δ x| ≤
      (y ^ 2 * tartarTestFunctionSecondDerivativeBound +
        2 * δ +
        8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
        4 * δ ^ 2 * x ^ 2) *
      Real.exp (-δ * x ^ 2) := by
  unfold regularizedScaledTartarSecondDerivative
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  calc
    |y ^ 2 * tartarTestFunctionSecondDerivative (y * x) -
        2 * δ * scaledTartarTestFunction y x -
        4 * δ * x * (y * deriv Tartar.testFunction (y * x)) +
        4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x| ≤
      |y ^ 2 * tartarTestFunctionSecondDerivative (y * x)| +
        |2 * δ * scaledTartarTestFunction y x| +
        |4 * δ * x * (y * deriv Tartar.testFunction (y * x))| +
        |4 * δ ^ 2 * x ^ 2 * scaledTartarTestFunction y x| := by grind
    _ ≤ y ^ 2 * tartarTestFunctionSecondDerivativeBound +
        2 * δ +
        8 * δ * |y| * tartarAmplitudeDerivativeBound * |x| +
        4 * δ ^ 2 * x ^ 2 := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hδ,
        abs_of_nonneg (scaledTartarTestFunction_nonneg y x),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · rw [sq_abs]
            exact mul_le_mul_of_nonneg_left
              (abs_tartarTestFunctionSecondDerivative_le (y * x))
              (sq_nonneg y)
          · simpa only [scaledTartarTestFunction, mul_one] using
              mul_le_mul_of_nonneg_left
                (tartarTestFunction_le_one (y * x))
                (show 0 ≤ 2 * δ from mul_nonneg (by norm_num) hδ)
        · have hd :=
            abs_deriv_tartarTestFunction_le (y * x)
          have hcoef :
              0 ≤ 4 * δ * |x| * |y| := by positivity
          nlinarith
      · have hf := tartarTestFunction_le_one (y * x)
        change
          4 * δ ^ 2 * |x| ^ 2 * Tartar.testFunction (y * x) ≤
            4 * δ ^ 2 * x ^ 2
        rw [sq_abs]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hf
            (show 0 ≤ 4 * δ ^ 2 * x ^ 2 by positivity)

end NumberField.Odlyzko
