/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticSource

@[expose] public section

/-! Continuous coefficient data for the correction source, with proved uniform ball bounds. -/

noncomputable section

namespace EulerQuadraticSource

open Set
open scoped Topology

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T]

/-- Actual continuous data for the pressure-projected quadratic source. -/
structure Coefficients (T : Type*) [TopologicalSpace T] (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  projection : C(T, Y →L[ℝ] Y)
  forcing : C(T, Y)
  linear : C(T, X →L[ℝ] Y)
  quadratic : C(T, X →L[ℝ] X →L[ℝ] Y)

/-- Evaluate the genuine projected source. -/
def Coefficients.apply (C : Coefficients T X Y) (t : T) (u : X) : Y :=
  source (C.projection t) (C.forcing t) (C.linear t) (C.quadratic t) u

/-- The source is jointly continuous in time and the Sobolev unknown. -/
theorem Coefficients.continuous (C : Coefficients T X Y) :
    Continuous (fun p : T × X => C.apply p.1 p.2) :=
  source_continuous _ _ _ _ C.projection.continuous C.forcing.continuous C.linear.continuous
    C.quadratic.continuous

/-- Restrict coefficient data along any continuous parameter map. -/
def Coefficients.comp {U : Type*} [TopologicalSpace U] (C : Coefficients T X Y) (f : C(U,T)) :
  Coefficients U X Y where
  projection := C.projection.comp f
  forcing := C.forcing.comp f
  linear := C.linear.comp f
  quadratic := C.quadratic.comp f

@[simp] theorem Coefficients.comp_apply {U : Type*} [TopologicalSpace U]
    (C : Coefficients T X Y) (f : C(U,T)) (t : U) (u : X) : (C.comp f).apply t u = C.apply (f t) u
      := rfl

local instance nestedGroup : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance

variable [CompactSpace T]

/-- A uniform norm bound for the actual source on a ball. -/
def Coefficients.ballBound (C : Coefficients T X Y) (R : ℝ) : ℝ :=
  ‖C.projection‖ * (‖C.forcing‖ + ‖C.linear‖*R + ‖C.quadratic‖*R^2)

/-- A uniform Lipschitz constant for the actual source on a ball. -/
def Coefficients.ballLipschitz (C : Coefficients T X Y) (R : ℝ) : ℝ :=
  ‖C.projection‖ * (‖C.linear‖ + 2*‖C.quadratic‖*R)

theorem Coefficients.ballBound_nonneg (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ C.ballBound R := by unfold Coefficients.ballBound; positivity

theorem Coefficients.ballLipschitz_nonneg (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ C.ballLipschitz R := by unfold Coefficients.ballLipschitz; positivity

/-- The uniform source bound follows from actual operator norms, with no assumed nonlinear estimate. -/
theorem Coefficients.apply_bound (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R)
    (t : T) (u : X) (hu : ‖u‖ ≤ R) : ‖C.apply t u‖ ≤ C.ballBound R :=
  source_uniform_bound _ _ _ _ _ _ _ _ R
    (C.projection.norm_coe_le_norm t) (C.forcing.norm_coe_le_norm t)
    (C.linear.norm_coe_le_norm t) (C.quadratic.norm_coe_le_norm t) hR u hu

/-- The uniform local Lipschitz estimate follows from the proved quadratic difference identity. -/
theorem Coefficients.apply_sub_bound (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R)
    (t : T) (u v : X) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖C.apply t u-C.apply t v‖ ≤ C.ballLipschitz R * ‖u-v‖ :=
  source_uniform_sub_bound _ _ _ _ _ _ _ R
    (C.projection.norm_coe_le_norm t) (C.linear.norm_coe_le_norm t)
    (C.quadratic.norm_coe_le_norm t) hR u v hu hv

end EulerQuadraticSource
