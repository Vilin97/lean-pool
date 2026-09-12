/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Pointwise multilinear L² fields define genuine bounded multilinear maps into L². -/

@[expose] public section


noncomputable section


namespace EulerLpDerivative

open MeasureTheory Filter

variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X) (n : ℕ)

/-- Multilinear bundling as an element of `Lp (P [×n]→L[ℝ] V) 2 μ →L[ℝ] (P [×n]→L[ℝ] Lp V 2 μ)`. -/
def multilinearBundling : Lp (P [×n]→L[ℝ] V) 2 μ →L[ℝ] (P [×n]→L[ℝ] Lp V 2 μ) := by
  let ev : P [×n]→L[ℝ] ((P [×n]→L[ℝ] V) →L[ℝ] V) :=
    (ContinuousLinearMap.id ℝ (P [×n]→L[ℝ] V)).flipMultilinear
  let lift : ((P [×n]→L[ℝ] V) →L[ℝ] V) →L[ℝ]
      (Lp (P [×n]→L[ℝ] V) 2 μ →L[ℝ] Lp V 2 μ) :=
    ContinuousLinearMap.compLpL₂ (𝕜 := ℝ) (E := P [×n]→L[ℝ] V) (F := V)
      (G := (P [×n]→L[ℝ] V) →L[ℝ] V) 2 μ
      (ContinuousLinearMap.id ℝ ((P [×n]→L[ℝ] V) →L[ℝ] V))
  exact (lift.compContinuousMultilinearMap ev).flipLinear

theorem multilinearBundling_ae (D : Lp (P [×n]→L[ℝ] V) 2 μ) (v : Fin n → P) :
    multilinearBundling (P := P) (V := V) μ n D v =ᵐ[μ] fun x => D x v := by
  let L : (P [×n]→L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (P [×n]→L[ℝ] V)).flipMultilinear v
  exact ContinuousLinearMap.coeFn_compLp (𝕜 := ℝ) (𝕜' := ℝ)
    (E := P [×n]→L[ℝ] V) (F := V) (σ := RingHom.id ℝ) L D

theorem multilinearBundling_apply_norm_le (D : Lp (P [×n]→L[ℝ] V) 2 μ) :
    ‖multilinearBundling (P := P) (V := V) μ n D‖ ≤ ‖D‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg D)
  intro v
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multilinearBundling_ae μ n D v] with x hx
  rw [hx, mul_comm]
  exact (D x).le_opNorm v

theorem multilinearBundling_norm_le_one :
    ‖multilinearBundling (P := P) (V := V) μ n‖ ≤ 1 := by
  apply (multilinearBundling (P := P) (V := V) μ n).opNorm_le_bound zero_le_one
  intro D
  simpa only [one_mul] using multilinearBundling_apply_norm_le μ n D

end EulerLpDerivative
