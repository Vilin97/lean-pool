/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Definitions from the quadratic Carleson endpoint paper

This file records foundational objects from Sections 2 and 3 of the paper.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace QuadraticCarleson

/-- The paper's notation `e(s) = exp(2 π i s)`. -/
noncomputable def phase (s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)

@[simp]
theorem phase_zero : phase 0 = 1 := by
  simp [phase]

/-- The iterated logarithms from the paper, with `paperLog 1 t = log (10 + t)`. -/
noncomputable def paperLog : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => fun t => Real.log (10 + paperLog n t)

@[simp]
theorem paperLog_zero (t : ℝ) : paperLog 0 t = t := rfl

@[simp]
theorem paperLog_succ (n : ℕ) (t : ℝ) :
    paperLog (n + 1) t = Real.log (10 + paperLog n t) := rfl

/-- A Young function in the precise sense used in Section 2.5 of the paper.

Only values on `[0, ∞)` are relevant. The final field includes the paper's
exceptional Young function `Φ(t) = t` alongside the usual superlinear case. -/
structure YoungFunction where
  /-- The real-valued function whose restriction to the nonnegative half-line satisfies the
  Young-function axioms. -/
  toFun : ℝ → ℝ
  continuousOn_nonneg : ContinuousOn toFun (Ici 0)
  convexOn_nonneg : ConvexOn ℝ (Ici 0) toFun
  strictMonoOn_nonneg : StrictMonoOn toFun (Ici 0)
  map_zero : toFun 0 = 0
  identity_or_superlinear :
    (∀ t ∈ Ici (0 : ℝ), toFun t = t) ∨
      Tendsto (fun t : ℝ => toFun t / t) atTop atTop

instance : CoeFun YoungFunction (fun _ => ℝ → ℝ) := ⟨YoungFunction.toFun⟩

/-- The hypothesis `Φ(t) = o(t log₂ t)` in Theorem 1. -/
def GrowsSlowerThanEndpoint (Φ : YoungFunction) : Prop :=
  (fun t : ℝ => Φ t) =o[atTop] (fun t : ℝ => t * paperLog 2 t)

/-- The paper's space `L₀∞(ℝ)`: bounded, compactly supported measurable
complex-valued functions. -/
structure L0Infinity where
  /-- The bounded, compactly supported measurable complex-valued test function. -/
  toFun : ℝ → ℂ
  measurable_toFun : Measurable toFun
  bounded_toFun : ∃ C : ℝ, ∀ x, ‖toFun x‖ ≤ C
  hasCompactSupport_toFun : HasCompactSupport toFun

instance : CoeFun L0Infinity (fun _ => ℝ → ℂ) := ⟨L0Infinity.toFun⟩

/-- The quadratic Hilbert-transform integral truncated at distance `ε` from
the singularity. -/
noncomputable def quadraticHilbertTrunc
    (modulation ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in {t : ℝ | ε < |t|}, f (x - t) * phase (modulation * t ^ 2) / (t : ℂ)

/-- `z` is the principal value when the symmetric truncations converge to `z`
as `ε → 0+`. -/
def HasQuadraticPrincipalValue (modulation : ℝ) (f : ℝ → ℂ) (x : ℝ) (z : ℂ) : Prop :=
  Tendsto (fun ε : ℝ => quadraticHilbertTrunc modulation ε f x)
    (nhdsWithin 0 (Ioi 0)) (nhds z)

/-- Distance to the nearest integer, the paper's `‖x‖_ᵀ`. -/
noncomputable def torusNorm (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The localized Bohr set `B(k, ρ)` from Definition 3.2. -/
def bohrSet (k : ℕ) (ρ : ℝ) : Set ℝ :=
  {x | x ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ) ∧ torusNorm ((k : ℝ) * x) ≤ ρ}

end QuadraticCarleson
