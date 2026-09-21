/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Affine covariance of the closed numerical range

The raw numerical-range covariance extends to the standard affine form
`A ↦ aA + bI`.  When `a` is nonzero this affine map is a homeomorphism, so it
also commutes exactly with closure.
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import LeanPool.OperatorTheory.Operator.NumericalRange.Affine

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range commutes with the usual affine action
`A ↦ aA + bI`. -/
theorem numericalRange_smul_add_smul_one
    (A : E →L[ℂ] E) (a b : ℂ) :
    numericalRange (a • A + b • 1) =
      (fun z => a * z + b) '' numericalRange A := by
  rw [numericalRange_add_smul_one, numericalRange_smul, Set.image_image]

/-- A nondegenerate affine change of an operator transports the closure of
its numerical range by the same affine map. -/
theorem closure_numericalRange_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    closure (numericalRange (a • A + b • 1)) =
      (fun z => a * z + b) '' closure (numericalRange A) := by
  rw [numericalRange_smul_add_smul_one]
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  have h := (e.image_closure (numericalRange A)).symm
  have he : (e : ℂ → ℂ) = fun z => a * z + b := by
    funext z
    rfl
  rw [he] at h
  exact h

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
