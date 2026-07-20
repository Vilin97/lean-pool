/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Topology.Path

/-!
# Bridge coercions from PiecewiseC1Curve to mathlib Path / ContinuousMap

We provide `PiecewiseC1Curve.toPath` and `PiecewiseC1Curve.toContinuousMap` that
rescale the domain `[a,b]` to the unit interval `[0,1]` via `iccHomeoI`.
-/

open Complex Set Topology unitInterval

noncomputable section

namespace PiecewiseC1Curve

/-- The rescaling homeomorphism from `I = [0,1]` to `[a,b]`, as a subtype-valued map. -/
private def rescale (γ : PiecewiseC1Curve) : I → Icc γ.a γ.b :=
  (iccHomeoI γ.a γ.b γ.hab).symm

private theorem rescale_continuous (γ : PiecewiseC1Curve) :
    Continuous (Subtype.val ∘ γ.rescale) :=
  continuous_subtype_val.comp (iccHomeoI γ.a γ.b γ.hab).symm.continuous

private theorem rescale_mem_Icc (γ : PiecewiseC1Curve) (t : I) :
    (γ.rescale t : ℝ) ∈ Icc γ.a γ.b := (γ.rescale t).2

private theorem rescale_zero (γ : PiecewiseC1Curve) :
    (γ.rescale ⟨0, left_mem_Icc.mpr zero_le_one⟩ : ℝ) = γ.a := by
  simp [rescale, iccHomeoI_symm_apply_coe]

private theorem rescale_one (γ : PiecewiseC1Curve) :
    (γ.rescale ⟨1, right_mem_Icc.mpr zero_le_one⟩ : ℝ) = γ.b := by
  simp [rescale, iccHomeoI_symm_apply_coe]

/-- Convert a `PiecewiseC1Curve` to a mathlib `Path` by rescaling `[a,b]` to `[0,1]`.
The path goes from `γ(a)` to `γ(b)`. -/
def toPath (γ : PiecewiseC1Curve) : Path (γ.toFun γ.a) (γ.toFun γ.b) where
  toFun t := γ.toFun (γ.rescale t)
  continuous_toFun :=
    γ.continuous_toFun.comp_continuous γ.rescale_continuous (fun t => γ.rescale_mem_Icc t)
  source' := congrArg γ.toFun γ.rescale_zero
  target' := congrArg γ.toFun γ.rescale_one

/-- Convert a `PiecewiseC1Curve` to a `ContinuousMap` from the unit interval to `ℂ`. -/
def toContinuousMap (γ : PiecewiseC1Curve) : C(I, ℂ) :=
  γ.toPath.toContinuousMap

/-- `toPath` agrees with the original curve under rescaling. -/
theorem toPath_apply (γ : PiecewiseC1Curve) (t : I) :
    γ.toPath t = γ.toFun ((iccHomeoI γ.a γ.b γ.hab).symm t) := rfl

/-- `toContinuousMap` agrees with the original curve under rescaling. -/
theorem toContinuousMap_apply (γ : PiecewiseC1Curve) (t : I) :
    γ.toContinuousMap t = γ.toFun ((iccHomeoI γ.a γ.b γ.hab).symm t) := rfl

/-- A closed `PiecewiseC1Curve` gives a loop, i.e., a `Path` from `γ(a)` to itself. -/
def toLoop (γ : PiecewiseC1Curve) (hc : γ.IsClosed) :
    Path (γ.toFun γ.a) (γ.toFun γ.a) :=
  γ.toPath.cast rfl hc

end PiecewiseC1Curve

end
