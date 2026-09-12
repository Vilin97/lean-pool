/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientTimeRestriction

/-!
# Actual source data on the history and forward time intervals

These constructions restrict the given deformation and its inverse. The
time derivative follows by restriction or by the affine change t = τ+s;
spatial derivatives are retained literally by continuous precomposition.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseSourceCoefficientPath EulerTimeIntervalRestriction EulerVolterraConvolution
  EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketIntervalData1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketIntervalData2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketIntervalData3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketIntervalData4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

namespace Data

variable (D : Data U)

/-- The prescribed source fields on [0,τ]. -/
def initial (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) : Data U where
  T := τ
  T_pos := hτ
  support := D.support
  support_compact := D.support_compact
  m₀ := D.m₀
  m₀_unit := D.m₀_unit
  R := D.R
  F := D.F.comp (initialInclusion D.T τ hτT)
  F₁ := D.F₁.comp (initialInclusion D.T τ hτT)
  FInv := D.FInv.comp (initialInclusion D.T τ hτT)
  M := D.M.comp (initialInclusion D.T τ hτT)
  inverse_left t x v := D.inverse_left (initialInclusion D.T τ hτT t) x v
  inverse_right t x v := D.inverse_right (initialInclusion D.T τ hτT t) x v
  frame_time t ht x :=
    initialPath_hasDerivWithinAt D.T τ D.T_pos.le hτ.le hτT
      (pathEvaluation x D.F.field) (pathEvaluation x D.F₁.field)
      (fun s hs => D.frame_time s hs x) t ht
  strain_equation t x v := D.strain_equation (initialInclusion D.T τ hτT t) x v

/-- The prescribed source fields on [τ,T], with elapsed time starting at zero. -/
def tail (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ < D.T) : Data U where
  T := D.T-τ
  T_pos := sub_pos.mpr hτT
  support := D.support
  support_compact := D.support_compact
  m₀ := D.m₀
  m₀_unit := D.m₀_unit
  R := D.R
  F := D.F.comp (tailInclusion D.T τ hτ)
  F₁ := D.F₁.comp (tailInclusion D.T τ hτ)
  FInv := D.FInv.comp (tailInclusion D.T τ hτ)
  M := D.M.comp (tailInclusion D.T τ hτ)
  inverse_left t x v := D.inverse_left (tailInclusion D.T τ hτ t) x v
  inverse_right t x v := D.inverse_right (tailInclusion D.T τ hτ t) x v
  frame_time t ht x :=
    tailPath_hasDerivWithinAt D.T τ D.T_pos.le hτ hτT.le
      (pathEvaluation x D.F.field) (pathEvaluation x D.F₁.field)
      (fun s hs => D.frame_time s hs x) t ht
  strain_equation t x v := D.strain_equation (tailInclusion D.T τ hτ t) x v

@[simp] theorem initial_frame_apply (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T)
    (t : Icc (0 : ℝ) τ) (x : Space) (v : U) :
    (D.initial τ hτ hτT).frame.field t x v =
      D.frame.field (initialInclusion D.T τ hτT t) x v := rfl

@[simp] theorem tail_frame_apply (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ < D.T)
    (t : Icc (0 : ℝ) (D.T - τ)) (x : Space) (v : U) :
    (D.tail τ hτ hτT).frame.field t x v =
      D.frame.field (tailInclusion D.T τ hτ t) x v := rfl

theorem initial_inverseBound_le (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) :
    (D.initial τ hτ hτT).inverseBound ≤ D.inverseBound := by
  change 1+‖(D.FInv.comp (initialInclusion D.T τ hτT)).field‖ ≤ 1+‖D.FInv.field‖
  linarith [D.FInv.comp_norm_le (initialInclusion D.T τ hτT)]

theorem tail_inverseBound_le (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ < D.T) :
    (D.tail τ hτ hτT).inverseBound ≤ D.inverseBound := by
  change 1+‖(D.FInv.comp (tailInclusion D.T τ hτ)).field‖ ≤ 1+‖D.FInv.field‖
  linarith [D.FInv.comp_norm_le (tailInclusion D.T τ hτ)]

end Data

namespace HistoryData

variable {D : Data U} (B : HistoryData D)

/-- The source Jacobi law and positivity remain valid on the actual history interval. -/
def initial (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) : HistoryData (D.initial τ hτ hτT) where
  H := B.H.comp (initialInclusion D.T τ hτT)
  jacobi t ht x :=
    initialPath_hasDerivWithinAt D.T τ D.T_pos.le hτ.le hτT
      (pathEvaluation x D.F₁.field)
      (pathEvaluation x (-pathCompositionMap B.H.field D.F.field))
      (fun s hs => B.jacobi s hs x) t ht
  potential := B.potential
  potential_nonneg := B.potential_nonneg
  potential_bound t x v := B.potential_bound (initialInclusion D.T τ hτT t) x v
  small := by
    have hs : τ^2 ≤ D.T^2 := (sq_le_sq₀ hτ.le D.T_pos.le).mpr hτT
    have hm := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2))
      B.potential_nonneg
    exact hm.trans B.small

end HistoryData
end EulerTransversePacketProvider
