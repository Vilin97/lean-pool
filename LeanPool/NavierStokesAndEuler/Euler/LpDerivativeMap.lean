/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Currying an actual L² field of derivatives into a bounded derivative operator. -/

@[expose] public section


noncomputable section

namespace EulerLpDerivative

open MeasureTheory

variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X)

/-- Apply derivative, given by `(ContinuousLinearMap.apply ℝ V a).compLpL 2 μ D`. -/
def applyDerivative (D : Lp (P →L[ℝ] V) 2 μ) (a : P) : Lp V 2 μ :=
  (ContinuousLinearMap.apply ℝ V a).compLpL 2 μ D

theorem applyDerivative_ae (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    applyDerivative μ D a =ᵐ[μ] fun x => D x a :=
  (ContinuousLinearMap.apply ℝ V a).coeFn_compLp D

theorem applyDerivative_norm_le (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    ‖applyDerivative μ D a‖ ≤ ‖D‖ * ‖a‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyDerivative_ae μ D a] with x hx
  rw [hx, mul_comm]
  exact (D x).le_opNorm a

/-- Derivative linear, bundling `toFun`, `map_add`, `map_smul`. -/
def derivativeLinear (D : Lp (P →L[ℝ] V) 2 μ) : P →ₗ[ℝ] Lp V 2 μ where
  toFun := applyDerivative μ D
  map_add' a b := by
    apply Lp.ext
    filter_upwards [applyDerivative_ae μ D (a+b), applyDerivative_ae μ D a,
      applyDerivative_ae μ D b, Lp.coeFn_add (applyDerivative μ D a) (applyDerivative μ D b)]
      with x hab ha hb hs
    rw [hab, hs]
    simp only [Pi.add_apply]
    rw [ha, hb, map_add]
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [applyDerivative_ae μ D (c • a), applyDerivative_ae μ D a,
      Lp.coeFn_smul c (applyDerivative μ D a)] with x hca ha hs
    change (applyDerivative μ D (c • a)) x = (c • applyDerivative μ D a) x
    rw [hca, hs]
    simp only [Pi.smul_apply]
    rw [ha, map_smul]

/-- This is a concrete bounded derivative with values in the actual L² function space. -/
def derivativeMap (D : Lp (P →L[ℝ] V) 2 μ) : P →L[ℝ] Lp V 2 μ :=
  (derivativeLinear μ D).mkContinuous ‖D‖ (applyDerivative_norm_le μ D)

theorem derivativeMap_ae (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    derivativeMap μ D a =ᵐ[μ] fun x => D x a := applyDerivative_ae μ D a

theorem derivativeMap_norm_le (D : Lp (P →L[ℝ] V) 2 μ) : ‖derivativeMap μ D‖ ≤ ‖D‖ :=
  (derivativeMap μ D).opNorm_le_bound (norm_nonneg D) (applyDerivative_norm_le μ D)

end EulerLpDerivative
