/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Definitions for Nesterov Acceleration under a Local Polyak-Łojasiewicz Condition

Core definitions: ambient space, optimization concepts (argmin, PL condition, L-smoothness),
tubular neighborhoods, first-order algorithm model, convergence rate, and manifold setup.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

variable {d : ℕ}

/-- The ambient Euclidean space ℝ^d. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ## Definitions for the optimization problem -/

/-- The set of global minimizers of f. -/
def argminSet (f : E d → ℝ) : Set (E d) :=
  {x | ∀ y, f x ≤ f y}

/-- The infimal value f⋆ = inf_x f(x). -/
def fStar (f : E d → ℝ) : ℝ := iInf f

/-- A function f satisfies the μ-Polyak-Łojasiewicz (PL) condition on a set U if
    f is differentiable on U and ‖∇f(x)‖² ≥ 2μ(f(x) - f⋆) for all x ∈ U. -/
def PolyakLojasiewicz (f : E d → ℝ) (μ : ℝ) (U : Set (E d)) : Prop :=
  0 < μ ∧ DifferentiableOn ℝ f U ∧ ∀ x ∈ U, ‖gradient f x‖ ^ 2 ≥ 2 * μ * (f x - fStar f)

/-- L-smoothness: the gradient of f is L-Lipschitz. -/
def LSmooth (f : E d → ℝ) (L : ℝ≥0) : Prop :=
  Differentiable ℝ f ∧ LipschitzWith L (gradient f)

-- An open set U is a tubular neighborhood of S if it is open, contains S,
-- and every point in U has a unique nearest point in S.
-- (Uses the generic definition from PLAcceleratedNesterovLean.MorseBott.BridgeDefs.)

-- IsTubularNeighborhoodOfSubmanifold is provided by
-- PLAcceleratedNesterovLean.MorseBott.TubularProjection
-- with the additional fiber_bijectivity field. Namespace lemmas (isOpen, subset,
-- toIsTubularNeighborhood, shrink, radius) are in PLAcceleratedNesterovLean.MorseBott.Bridge.

/-- U is a general tubular neighborhood of S: U is open, S ⊆ U,
    and every point in U has a unique nearest point in S. -/
structure IsGeneralTubularNeighborhood (S U : Set (E d)) : Prop where
  isOpen : IsOpen U
  subset : S ⊆ U
  uniqueProj : ∀ x ∈ U, ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S

/-! ## First-order algorithm model -/

/-- A first-order oracle algorithm with abstract internal state.
    At each step, the algorithm receives the function value f(x) and gradient ∇f(x)
    at the current readout point x, and produces a new internal state.
    The abstract state type S allows representing momentum methods like NAG
    (e.g. with S = E d × E d for the (xₖ, yₖ) pair). -/
structure FirstOrderAlgorithm (d : ℕ) where
  /-- The internal state type. -/
  S : Type*
  /-- Initialize the state from a starting point. -/
  init : E d → S
  /-- Advance one step: (state, f(readout(state)), ∇f(readout(state))) → new state. -/
  step : S → ℝ → E d → S
  /-- Extract the current iterate from the internal state. -/
  readout : S → E d

/-- The sequence of internal states produced by a first-order algorithm. -/
def FirstOrderAlgorithm.stateAt (alg : FirstOrderAlgorithm d) (f : E d → ℝ) (x₀ : E d) :
    ℕ → alg.S
  | 0     => alg.init x₀
  | k + 1 =>
    let s := alg.stateAt f x₀ k
    let x := alg.readout s
    alg.step s (f x) (gradient f x)

/-- The sequence of iterates produced by a first-order algorithm. -/
def FirstOrderAlgorithm.iterate (alg : FirstOrderAlgorithm d) (f : E d → ℝ) (x₀ : E d)
    (k : ℕ) : E d :=
  alg.readout (alg.stateAt f x₀ k)

/-! ## Convergence rate -/

/-- Accelerated convergence rate: f(xₖ) - f⋆ ≤ C · exp(-k / √(L/μ)). -/
def HasAcceleratedRate (f : E d → ℝ) (iterates : ℕ → E d) (L μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, f (iterates k) - fStar f ≤ C * Real.exp (-(↑k / Real.sqrt (L / μ)))

/-- Accelerated convergence with explicit prefactor `2`:
    f(xₖ) - f⋆ ≤ 2 · exp(-k / √(L/μ)) · (f(x₀) - f⋆). -/
def HasAcceleratedRateWithPrefactorTwo (f : E d → ℝ) (iterates : ℕ → E d)
    (L μ : ℝ) (x₀ : E d) : Prop :=
  ∀ k : ℕ,
    f (iterates k) - fStar f ≤
      2 * Real.exp (-(↑k / Real.sqrt (L / μ))) * (f x₀ - fStar f)

/-! ## Manifold setup: M as an embedded submanifold -/

/-- The model space for the n-dimensional submanifold. -/
abbrev ManifoldModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Model with corners for the n-dimensional Euclidean model (no boundary). -/
def modelI (n : ℕ) : ModelWithCorners ℝ (ManifoldModel n) (ManifoldModel n) :=
  modelWithCornersSelf ℝ (ManifoldModel n)

end PLAcceleratedNesterovLean
