/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeMap

/-! The L² derivative-field construction is a contraction between the actual Banach spaces. -/

@[expose] public section


noncomputable section


namespace EulerLpDerivative

open MeasureTheory

variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X)

/-- Bundling linear, bundling `toFun`, `map_add`, `map_smul`. -/
def bundlingLinear : Lp (P →L[ℝ] V) 2 μ →ₗ[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toFun := derivativeMap μ
  map_add' D E := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_add D E
  map_smul' c D := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_smul c D

/-- Derivative bundling, bundling `toLinearMap`, `cont`. -/
def derivativeBundling : Lp (P →L[ℝ] V) 2 μ →L[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toLinearMap := bundlingLinear μ
  cont := AddMonoidHomClass.continuous_of_bound (bundlingLinear (P := P) (V := V) μ) 1
    (fun D => by
      change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
      simpa only [one_mul] using derivativeMap_norm_le μ D)

@[simp] theorem derivativeBundling_apply (D : Lp (P →L[ℝ] V) 2 μ) :
    derivativeBundling μ D = derivativeMap μ D := rfl

theorem derivativeBundling_norm_le_one : ‖derivativeBundling (P := P) (V := V) μ‖ ≤ 1 :=
  (derivativeBundling (P := P) (V := V) μ).opNorm_le_bound zero_le_one (fun D => by
    change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
    simpa only [one_mul] using derivativeMap_norm_le μ D)

end EulerLpDerivative
