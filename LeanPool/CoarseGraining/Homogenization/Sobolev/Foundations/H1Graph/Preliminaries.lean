/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! # Preliminaries -/

namespace Homogenization

open scoped RealInnerProductSpace

/-- Smooth compactly supported test functions used to encode the weak-gradient
constraints inside the `L²(U) × L²(U; ℝᵈ)` ambient product. -/
structure H1WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

namespace H1WeakTestFunction

variable {d : ℕ} {U : Set (Vec d)}

instance : CoeFun (H1WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun

/-- The `i`th classical derivative of a test function. -/
noncomputable def deriv (φ : H1WeakTestFunction U) (i : Fin d) : Vec d → ℝ :=
  fun x => (fderiv ℝ φ x) (basisVec i)

private theorem continuous (φ : H1WeakTestFunction U) : Continuous φ :=
  (φ.smooth.differentiable (by simp)).continuous

private theorem memScalarL2 (φ : H1WeakTestFunction U) : MemScalarL2 U φ := by
  simpa [MemScalarL2, volumeMeasureOn] using
    (φ.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict U

private theorem deriv_continuous (φ : H1WeakTestFunction U) (i : Fin d) :
    Continuous (φ.deriv i) := by
  simpa [H1WeakTestFunction.deriv] using!
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem deriv_compactSupport (φ : H1WeakTestFunction U) (i : Fin d) :
    HasCompactSupport (φ.deriv i) := by
  simpa [H1WeakTestFunction.deriv] using!
    φ.compactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)

private theorem deriv_memScalarL2 (φ : H1WeakTestFunction U) (i : Fin d) :
    MemScalarL2 U (φ.deriv i) := by
  simpa [MemScalarL2, volumeMeasureOn] using
    ((φ.deriv_continuous i).memLp_of_hasCompactSupport (φ.deriv_compactSupport i)).restrict U

/-- The scalar `L²(U)` class of a test function. -/
noncomputable def toScalarL2 (φ : H1WeakTestFunction U) : ScalarL2 U :=
  Homogenization.toScalarL2 φ.memScalarL2

/-- The scalar `L²(U)` class of the `i`th derivative of a test function. -/
noncomputable def derivToScalarL2 (φ : H1WeakTestFunction U) (i : Fin d) : ScalarL2 U :=
  Homogenization.toScalarL2 (φ.deriv_memScalarL2 i)

@[simp] theorem coeFn_toScalarL2 (φ : H1WeakTestFunction U) :
    φ.toScalarL2 =ᵐ[volumeMeasureOn U] φ :=
  Homogenization.coeFn_toScalarL2 φ.memScalarL2

@[simp] theorem coeFn_derivToScalarL2 (φ : H1WeakTestFunction U) (i : Fin d) :
    φ.derivToScalarL2 i =ᵐ[volumeMeasureOn U] φ.deriv i :=
  Homogenization.coeFn_toScalarL2 (φ.deriv_memScalarL2 i)

end H1WeakTestFunction

section HilbertCoords

variable {d : ℕ} {U : Set (Vec d)}

/-- Extract the `i`th scalar coordinate of a Hilbert-vector `L²` field. -/
noncomputable def hilbertVectorCoordToScalarL2 (i : Fin d) :
    HilbertVectorL2 U →L[ℝ] ScalarL2 U :=
  let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  (π.compLpL 2 (volumeMeasureOn U)).comp (hilbertVectorL2ToVectorL2 (U := U))

@[simp] theorem coeFn_hilbertVectorCoordToScalarL2 (i : Fin d) (g : HilbertVectorL2 U) :
    hilbertVectorCoordToScalarL2 (U := U) i g =ᵐ[volumeMeasureOn U] fun x => g x i := by
  let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL
        (p := 2)
        (μ := volumeMeasureOn U)
        (L := π)
        (f := hilbertVectorL2ToVectorL2 (U := U) g),
       coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := g)]
    with x hcoord hback
  rw [show hilbertVectorCoordToScalarL2 (U := U) i g x = π (hilbertVectorL2ToVectorL2 (U := U) g x)
        by simpa [hilbertVectorCoordToScalarL2, π] using hcoord]
  rw [hback]
  rfl

theorem scalarInner_eq_integral (f g : ScalarL2 U) :
    inner ℝ f g = ∫ x in U, f x * g x ∂MeasureTheory.volume := by
  rw [MeasureTheory.L2.inner_def]
  simp [mul_comm]

theorem coordInner_eq_integral
    (i : Fin d) (g : HilbertVectorL2 U) (φ : H1WeakTestFunction U) :
    inner ℝ (hilbertVectorCoordToScalarL2 (U := U) i g) φ.toScalarL2 =
      ∫ x in U, g x i * φ x ∂MeasureTheory.volume := by
  rw [scalarInner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [coeFn_hilbertVectorCoordToScalarL2 (U := U) i g, φ.coeFn_toScalarL2]
    with x hg hφ
  rw [hg, hφ]

end HilbertCoords

end Homogenization
