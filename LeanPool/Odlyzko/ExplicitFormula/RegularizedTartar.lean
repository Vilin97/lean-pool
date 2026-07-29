/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform

/-!
# Regularized Tartar

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter Real
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized scaled tartar used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartar
    (y δ x : ℝ) : ℝ :=
  scaledTartarTestFunction y x * Real.exp (-δ * x ^ 2)

@[simp]
theorem regularizedScaledTartar_zero (y δ : ℝ) :
    regularizedScaledTartar y δ 0 = 1 := by
  simp [regularizedScaledTartar, scaledTartarTestFunction,
    tartarTestFunction_zero]

theorem regularizedScaledTartar_even (y δ x : ℝ) :
    regularizedScaledTartar y δ (-x) =
      regularizedScaledTartar y δ x := by
  unfold regularizedScaledTartar
  rw [scaledTartarTestFunction_even]
  simp

theorem regularizedScaledTartar_nonneg (y δ x : ℝ) :
    0 ≤ regularizedScaledTartar y δ x :=
  mul_nonneg (scaledTartarTestFunction_nonneg y x)
    (Real.exp_pos _).le

theorem regularizedScaledTartar_le_scaledTartar
    {y δ x : ℝ} (hδ : 0 ≤ δ) :
    regularizedScaledTartar y δ x ≤
      scaledTartarTestFunction y x := by
  unfold regularizedScaledTartar
  have hexp : Real.exp (-δ * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hδ (sq_nonneg x))
  exact mul_le_of_le_one_right
    (scaledTartarTestFunction_nonneg y x) hexp

theorem regularizedScaledTartar_le_one
    {y δ x : ℝ} (hδ : 0 ≤ δ) :
    regularizedScaledTartar y δ x ≤ 1 :=
  (regularizedScaledTartar_le_scaledTartar hδ).trans
    (tartarTestFunction_le_one _)

theorem tendsto_regularizedScaledTartar_nhds_zero
    (y x : ℝ) :
    Tendsto
      (fun δ : ℝ ↦ regularizedScaledTartar y δ x)
      (𝓝 0)
      (𝓝 (scaledTartarTestFunction y x)) := by
  unfold regularizedScaledTartar
  have harg :
      Tendsto (fun δ : ℝ ↦ -δ * x ^ 2)
        (𝓝 0) (𝓝 0) := by
    have hneg :
        Tendsto (fun δ : ℝ ↦ -δ) (𝓝 0) (𝓝 0) :=
      by
        have hid :
            Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) :=
          tendsto_id
        simpa only [id_eq, neg_zero] using hid.neg
    simpa using hneg.mul_const (x ^ 2)
  simpa using
    tendsto_const_nhds.mul
      (Real.continuous_exp.continuousAt.tendsto.comp harg)

end NumberField.Odlyzko
