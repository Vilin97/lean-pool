/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Shared definitions for external theorem compatibility

These mirror definitions from the source project so external theorems can be
stated and proved using the same types.
-/

open Filter Topology Metric InnerProductSpace

noncomputable section

namespace PLAcceleratedNesterovLean

/-! ## Ambient space -/

/-- The ambient Euclidean space ℝ^d (matching PLAcceleratedNesterovLean). -/
abbrev Ed (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ## Tubular neighborhoods -/

/-- A tubular neighborhood of S is an open set U ⊇ S such that every
    point in U has a unique nearest point in S. -/
structure IsTubularNeighborhood {E : Type*} [PseudoMetricSpace E]
    (S U : Set E) : Prop where
  isOpen : IsOpen U
  subset : S ⊆ U
  uniqueProj : ∀ x ∈ U, ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S

/-! ## Optimization definitions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of global minimizers of f. -/
def Ext.argminSet (f : E → ℝ) : Set E := {x | ∀ y, f x ≤ f y}

/-- The infimal value f⋆ = inf_x f(x). -/
def Ext.fStar (f : E → ℝ) : ℝ := ⨅ x, f x

/-- μ-PŁ condition using ‖fderiv‖ (PLMB compatibility layer). -/
def Ext.PolyakLojasiewicz (f : E → ℝ) (μ : ℝ) (U : Set E) : Prop :=
  0 < μ ∧ ∀ x ∈ U, ‖fderiv ℝ f x‖ ^ 2 ≥ 2 * μ * (f x - Ext.fStar f)

/-- The gradient of f at x (Riesz representative of fderiv ℝ f x). -/
def Ext.gradient (f : E → ℝ) (x : E) : E :=
  (toDual ℝ E).symm (fderiv ℝ f x)

/-- The Hessian quadratic form ξᵀ D²f(x) ξ = ⟨D(∇f)(x)·ξ, ξ⟩. -/
def Ext.hessianQuadForm (f : E → ℝ) (x ξ : E) : ℝ :=
  @inner ℝ E _ (fderiv ℝ (Ext.gradient f) x ξ) ξ

end PLAcceleratedNesterovLean
