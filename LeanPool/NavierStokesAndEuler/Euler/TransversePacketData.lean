/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseBoundedGeometry

/-!
# Source deformation data for the concrete transverse packet provider

Only the prescribed deformation, its inverse, and their actual time identity
are inputs. The transverse frame, normal, both coercivity constants, and all
geometry needed by the forward solve are derived below.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseBoundedFrame EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

/-- Data, collecting `T`, `T_pos`, `support`, `support_compact`, `m₀`, `m₀_unit` and their
compatibility conditions. -/
structure Data (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] where
  /-- Time horizon of `Data`, of type `ℝ`. -/
  T : ℝ
  T_pos : 0 < T
  /-- Support set of `Data`, of type `Set Space`. -/
  support : Set Space
  support_compact : IsCompact support
  /-- M₀ of `Data`, of type `Space`. -/
  m₀ : Space
  m₀_unit : ‖m₀‖ = 1
  /-- Radius parameter of `Data`, of type `U ≃ₗᵢ[ℝ] referencePlane m₀`. -/
  R : U ≃ₗᵢ[ℝ] referencePlane m₀
  /-- F of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- F₁ of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- F inv of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  FInv : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- M of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  inverse_left : ∀ t x v, FInv.field t x (F.field t x v) = v
  inverse_right : ∀ t x v, F.field t x (FInv.field t x v) = v
  frame_time : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T T_pos.le F.field s x)
      (extendPath T T_pos.le F₁.field t x) (Icc (0 : ℝ) T) t
  strain_equation : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v)

namespace Data

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem support_measurable : MeasurableSet D.support :=
  D.support_compact.isClosed.measurableSet

/-- Frame: an abbreviation for `coefficient D.m₀ D.R D.F`. -/
abbrev frame := coefficient D.m₀ D.R D.F
/-- Frame derivative: an abbreviation for `coefficient D.m₀ D.R D.F₁`. -/
abbrev frameDerivative := coefficient D.m₀ D.R D.F₁
/-- Normal: an abbreviation for `normalCoefficient D.m₀ D.FInv`. -/
abbrev normal := normalCoefficient D.m₀ D.FInv

/-- Inverse bound, given by `1+‖D.FInv.field‖`. -/
def inverseBound : ℝ := 1+‖D.FInv.field‖
/-- Frame bound, given by `1+‖D.F.field‖`. -/
def frameBound : ℝ := 1+‖D.F.field‖
/-- Frame lower, given by `D.inverseBound⁻¹^2`. -/
def frameLower : ℝ := D.inverseBound⁻¹^2
/-- Normal lower, given by `D.frameBound⁻¹^2`. -/
def normalLower : ℝ := D.frameBound⁻¹^2

theorem inverseBound_pos : 0 < D.inverseBound := by
  unfold inverseBound
  positivity

theorem frameBound_pos : 0 < D.frameBound := by
  unfold frameBound
  positivity

theorem frameLower_pos : 0 < D.frameLower :=
  pow_pos (inv_pos.mpr D.inverseBound_pos) 2

theorem normalLower_pos : 0 < D.normalLower :=
  pow_pos (inv_pos.mpr D.frameBound_pos) 2

theorem inverse_norm (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖D.FInv.field t x‖ ≤ D.inverseBound := by
  exact ((D.FInv.field t).norm_coe_le_norm x).trans
    ((D.FInv.field.norm_coe_le_norm t).trans (by unfold inverseBound; linarith))

theorem frame_norm (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖D.F.field t x‖ ≤ D.frameBound := by
  exact ((D.F.field t).norm_coe_le_norm x).trans
    ((D.F.field.norm_coe_le_norm t).trans (by unfold frameBound; linarith))

/-- Uniform coercivity follows from the actual inverse deformation. -/
theorem frame_lower (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    D.frameLower*‖v‖^2 ≤ ‖D.frame.field t x v‖^2 :=
  coefficient_lower D.m₀ D.R D.F (fun t x => D.FInv.field t x)
    D.inverseBound D.inverseBound_pos D.inverse_left D.inverse_norm t x v

/-- The scalar pressure inverse is nondegenerate by the same source identity. -/
theorem normal_lower (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.normalLower ≤ ‖D.normal.field t x‖^2 :=
  normalCoefficient_lower D.m₀ D.F D.FInv D.m₀_unit D.inverse_left
    D.frameBound D.frameBound_pos D.frame_norm t x

theorem frame_tangent (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    ⟪D.normal.field t x,D.frame.field t x v⟫_ℝ = 0 :=
  coefficient_tangent D.m₀ D.R D.F D.FInv D.inverse_left t x v

theorem frame_range (t : Icc (0 : ℝ) D.T) (x η : Space)
    (hη : ⟪D.normal.field t x, η⟫_ℝ = 0) : ∃ v, D.frame.field t x v = η :=
  coefficient_range D.m₀ D.R D.F D.FInv D.inverse_right t x η hη

theorem frame_strain (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.frameDerivative.field t x = (D.M.field t x).comp (D.frame.field t x) :=
  coefficient_strain D.m₀ D.R D.F D.F₁ D.M D.strain_equation t x

theorem frame_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.frame.field s x)
      (extendPath D.T D.T_pos.le D.frameDerivative.field t x) (Icc (0 : ℝ) D.T) t :=
  coefficient_hasDerivWithinAt D.m₀ D.R D.T D.T_pos.le D.F D.F₁ D.frame_time t ht x

end Data

end EulerTransversePacketProvider
