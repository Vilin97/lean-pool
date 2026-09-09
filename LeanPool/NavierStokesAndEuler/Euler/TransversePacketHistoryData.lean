/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus

/-!
# Source Hessian data construct the transverse history inverse

The additional inputs are the manuscript's literal Jacobi identity
F_tt = -H F and upper Hessian bound. The full-cylinder Dirichlet inverse,
its true time derivatives, and all endpoint conditions are constructed by
the previously proved coercive solve. No solution is an input.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerTransverseSourceCoefficientPath EulerTransverseFrameCoordinates
  EulerBoundedFieldCalculus EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The original Hessian law and upper bound, before the actual solve. -/
structure HistoryData (D : Data U) where
  /-- H of `HistoryData`, of type `SmoothCoefficientPath (Icc (0 : ℝ) D.T) (Space →L[ℝ] Space)`. -/
  H : SmoothCoefficientPath (Icc (0 : ℝ) D.T) (Space →L[ℝ] Space)
  jacobi : ∀ t ∈ Icc (0 : ℝ) D.T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.F₁.field s x)
      (-((extendPath D.T D.T_pos.le H.field t x).comp
        (extendPath D.T D.T_pos.le D.F.field t x))) (Icc (0 : ℝ) D.T) t
  /-- Potential of `HistoryData`, of type `ℝ`. -/
  potential : ℝ
  potential_nonneg : 0 ≤ potential
  potential_bound : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ potential*‖v‖^2
  small : potential*(D.T^2/2) ≤ 1/2

namespace HistoryData

variable {D : Data U} (B : HistoryData D)

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketHistoryData1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketHistoryData2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketHistoryData3 : NormedAddCommGroup (U →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketHistoryData4 : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketHistoryData5 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketHistoryData6 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ U →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketHistoryData7 : NormedAddCommGroup (Space →ᵇ U →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ U →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketHistoryData8 : NormedSpace ℝ (Space →ᵇ U →L[ℝ] Space) :=
    inferInstance

/-- The second frame derivative is the prescribed Hessian product. -/
def frameSecond : C(Icc (0 : ℝ) D.T,Space →ᵇ U →L[ℝ] Space) :=
  -pathCompositionMap B.H.field D.frame.field

@[simp] theorem frameSecond_apply (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    B.frameSecond t x v = -(B.H.field t x (D.frame.field t x v)) := rfl

theorem frameSecond_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.frameDerivative.field s x)
      (extendPath D.T D.T_pos.le B.frameSecond t x) (Icc (0 : ℝ) D.T) t := by
  have hd := (referenceRestriction D.m₀ D.R).hasFDerivAt.comp_hasDerivWithinAt t (B.jacobi t ht x)
  exact hd.congr_deriv (by
    apply ContinuousLinearMap.ext
    intro v
    rfl)

/-- The genuine spatial-angular L² inverse data, with uniform coercivity
derived from the actual inverse deformation. -/
def coefficients : EulerCylinderDirichlet.Coefficients D.T U Space where
  time_pos := D.T_pos
  Q := D.frame.field
  Q₁ := D.frameDerivative.field
  Q₂ := B.frameSecond
  H := B.H.field
  lower := D.frameLower
  lower_pos := D.frameLower_pos
  lower_bound := D.frame_lower
  derivative := D.frame_derivative
  second_derivative := B.frameSecond_derivative
  jacobi := B.frameSecond_apply
  potential := B.potential
  potential_nonneg := B.potential_nonneg
  potential_bound := B.potential_bound
  small := B.small

theorem coefficient_frame (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    B.coefficients.Q t x v = D.F.field t x (D.R v : Space) := rfl

theorem coefficient_hessian (t : Icc (0 : ℝ) D.T) (x : Space) :
    B.coefficients.H t x = B.H.field t x := rfl

end HistoryData

end EulerTransversePacketProvider
