/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The bounded primitive operator on unit-interval paths -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Extend a path by keeping both endpoint values constant. -/
def unitPathExtend (u : C(Icc (0 : ℝ) 1, E)) : ℝ → E :=
  fun t => u (projIcc 0 1 zero_le_one t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_unitPathExtend (u : C(Icc (0 : ℝ) 1, E)) : Continuous (unitPathExtend u) :=
  u.continuous.comp continuous_projIcc

/-- Integrate a continuous path from the left endpoint. -/
def unitPathPrimitive (u : C(Icc (0 : ℝ) 1, E)) : C(Icc (0 : ℝ) 1, E) where
  toFun t := ∫ s in 0..(t : ℝ), unitPathExtend u s
  continuous_toFun := (intervalIntegral.continuous_primitive
    (fun a b => (continuous_unitPathExtend u).intervalIntegrable a b) 0).comp continuous_subtype_val

theorem norm_unitPathPrimitive_le (u : C(Icc (0 : ℝ) 1, E)) : ‖unitPathPrimitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (t : ℝ)) (fun s _ => u.norm_coe_le_norm (projIcc 0 1 zero_le_one s))
  change ‖∫ s in 0..(t : ℝ), unitPathExtend u s‖ ≤ ‖u‖
  apply hb.trans
  rw [sub_zero, abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

/-- The primitive operator has norm at most one. -/
def unitPathPrimitiveCLM : C(Icc (0 : ℝ) 1, E) →L[ℝ] C(Icc (0 : ℝ) 1, E) := by
  let L : C(Icc (0 : ℝ) 1, E) →ₗ[ℝ] C(Icc (0 : ℝ) 1, E) :=
    { toFun := unitPathPrimitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in 0..(t : ℝ), unitPathExtend (u + v) s) =
          (∫ s in 0..(t : ℝ), unitPathExtend u s) + (∫ s in 0..(t : ℝ), unitPathExtend v s)
        simp only [unitPathExtend, ContinuousMap.add_apply]
        exact intervalIntegral.integral_add
          ((continuous_unitPathExtend u).intervalIntegrable _ _)
          ((continuous_unitPathExtend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        simp [unitPathPrimitive, unitPathExtend, intervalIntegral.integral_smul] }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(Icc (0 : ℝ) 1, E)) (F := C(Icc (0 : ℝ) 1, E)) L 1 ?_
  intro u
  change ‖unitPathPrimitive u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_unitPathPrimitive_le u

@[simp] theorem unitPathPrimitiveCLM_apply (u : C(Icc (0 : ℝ) 1, E)) :
    unitPathPrimitiveCLM u = unitPathPrimitive u := rfl

theorem norm_unitPathPrimitiveCLM_le : ‖unitPathPrimitiveCLM (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [unitPathPrimitiveCLM_apply, one_mul] using norm_unitPathPrimitive_le u

end LichnerowiczObata
