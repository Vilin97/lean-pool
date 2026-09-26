/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Basic sphere and odd-map interface

This file fixes a working model of the sphere and defines odd maps.
The definitions here should eventually be aligned with whichever sphere API is
most convenient for the full formalization, possibly `TopCat.sphere n`.
-/

@[expose] public section

noncomputable section

open Metric

namespace SphereOddDegree

/-- A concrete model of `S^n` as the unit sphere in `R^(n+1)`. -/
abbrev Sphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) (1 : ℝ))

/-- An odd map between spheres is equivariant for the antipodal map. -/
def IsOddMap {n : ℕ} (f : C(Sphere n, Sphere n)) : Prop :=
  ∀ x : Sphere n, f (-x) = - f x

/-- `IsOddMap f` unfolds to the pointwise oddness condition `f (-x) = - f x`.
This restatement is convenient for `rw`/`simp` even though it holds by `rfl`. -/
theorem isOddMap_iff {n : ℕ} {f : C(Sphere n, Sphere n)} :
    IsOddMap f ↔ ∀ x : Sphere n, f (-x) = - f x := by
  rfl

end SphereOddDegree
