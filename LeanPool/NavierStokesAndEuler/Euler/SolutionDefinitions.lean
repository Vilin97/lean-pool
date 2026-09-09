/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

/-
Copyright 2026 The Formal Conjectures Authors.

This file has been modified from its original form in the Formal Conjectures
project.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.CompletePartialOrder

/-!
# Solution-side definitions for the Euler Comparator challenge

Adapted from `FormalConjectures/Millenium/NavierStokes.lean` at
https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/Millenium/NavierStokes.lean

This is the whole-space breakdown alternative specialized to zero viscosity
and zero external force. It retains the source's initial-data decay, joint
smoothness, square integrability, and uniform energy conditions. Velocity and
pressure take position before time. The time derivative at zero is taken
within `[0,∞)`.

These definitions reproduce the independent reference exactly. This module
contains no challenge theorem or proof placeholder and does not import `Euler`.
-/

@[expose] public section



-- Inline the only needed notation from FormalConjecturesForMathlib.Geometry.3d.
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open ContDiff Set InnerProductSpace MeasureTheory

namespace Euler

/-- The divergence of a vector field, computed as the trace of its derivative. -/
noncomputable def divergence (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ v x).trace ℝ ℝ³

local notation "∇⬝" => divergence

/-- Smooth, divergence-free initial velocity. -/
structure InitialVelocityCondition (u₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Every spatial derivative of the initial velocity decays faster than any polynomial. -/
structure InitialVelocityConditionDecay (u₀ : ℝ³ → ℝ³) : Prop extends
    InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- A global smooth solution of unforced incompressible Euler on ℝ³. -/
structure EulerExistenceAndSmoothness
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  /-- `∂ₜv + (v · ∇)v = -∇p`: viscosity and external force are both zero. -/
  euler : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      -gradient (p · t) x
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

/-- The whole-space solution class, retaining the source's finite, uniformly bounded energy. -/
structure EulerExistenceAndSmoothnessR3
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends EulerExistenceAndSmoothness u₀ v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

open scoped ENNReal Topology

/-- The L² equivalence class of a square-integrable function. The fallback makes
this a total function; the solution conditions require square integrability
wherever it is used. -/
noncomputable def toL2 {V : Type*} [NormedAddCommGroup V] (f : ℝ³ → V) :
    Lp V 2 (volume : Measure ℝ³) := by
  classical
  exact if h : MemLp f 2 volume then h.toLp f else 0

/-- A spatially smooth path whose actual spatial derivative tensors belong to L²
and depend continuously on time in L², at every finite order. -/
structure SobolevSmoothOn (I : Set ℝ) (v : ℝ³ → ℝ → ℝ³) : Prop where
  spatial_smooth : ∀ t ∈ I, ContDiff ℝ ∞ (v · t)
  integrable : ∀ t ∈ I, MemLp (v · t) 2
  jets_integrable : ∀ m : ℕ, ∀ t ∈ I, MemLp (iteratedFDeriv ℝ m (v · t)) 2
  continuous : ContinuousOn (fun t => toL2 (v · t)) I
  jets_continuous : ∀ m : ℕ,
    ContinuousOn (fun t => toL2 (iteratedFDeriv ℝ m (v · t))) I

/-- Scalar-pressure Euler on a time set `I` in the original theorem's smooth
Sobolev class. The velocity and its strong time derivative have continuous L²
spatial jets of every order. The Euler equation uses this derivative witness.

As in `IsSmoothScalarEuler`, the time law and scalar-pressure equation are
required at interior times. There is no endpoint derivative condition. We use
`Ico 0 T` for a maximal lifespan and `Icc 0 T` for a closed interval. -/
structure EulerSobolevExistenceAndSmoothnessR3On (I : Set ℝ)
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  div_free : ∀ x, ∀ t ∈ I, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : SobolevSmoothOn I v
  pressure_differentiable : ∀ t ∈ interior I, Differentiable ℝ (p · t)
  euler : ∃ w : ℝ³ → ℝ → ℝ³,
    SobolevSmoothOn I w ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => toL2 (v · s)) (toL2 (w · t)) t) ∧
      (∀ x, ∀ t ∈ interior I,
        w x t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x)

/-- The ordinary curl of a velocity field, expressed through its spatial derivative.
Indices in `Fin 3` are cyclic. -/
noncomputable def vorticity (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (fderiv ℝ v x (EuclideanSpace.single (i + 1) 1)) (i + 2) -
      (fderiv ℝ v x (EuclideanSpace.single (i + 2) 1)) (i + 1))

/-- The sum of the spatial suprema of the velocity norm and derivative operator norm. -/
noncomputable def velocityC1Norm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  (⨆ x, ENNReal.ofReal ‖v x‖) + (⨆ x, ENNReal.ofReal ‖fderiv ℝ v x‖)

/-- The spatial supremum of the Euclidean norm of the actual vorticity. -/
noncomputable def vorticityNorm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖vorticity v x‖


end Euler
