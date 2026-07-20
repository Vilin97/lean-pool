/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Definitions for Corollary 2.17: μ-PŁ ⟹ μ-MB

Formalization of definitions from:
  "Fast convergence to non-isolated minima: four equivalent conditions
   for C² functions" — Rebjock & Boumal

## Contents

- `localMinSet`         : set S of local minimizers at a given level
- `MuPL`                : μ-Polyak–Łojasiewicz condition
- `MuEB`                : μ-Error Bound condition
- `MuQG`                : μ-Quadratic Growth condition
- `IsLocalSubmanifoldAt`: C¹ embedded submanifold at a point
- `hessian`             : second Fréchet derivative (bilinear form)
- `hessianKer`          : kernel of the Hessian
- `IsMuMB`              : μ-Morse–Bott property
-/

open Filter Topology Metric Submodule

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § The set of local minimizers at a given level
-- ════════════════════════════════════════════════════════════════════════════

/-- The set of local minimizers of `f` at the same function value as `x₀`.
    This is S from equation (4) in the paper:
      S = {x ∈ M : x is a local minimum of f and f(x) = f_S} -/
def localMinSet (f : E → ℝ) (x₀ : E) : Set E :=
  {x | IsLocalMin f x ∧ f x = f x₀}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem mem_localMinSet {f : E → ℝ} {x₀ x : E} :
    x ∈ localMinSet f x₀ ↔ IsLocalMin f x ∧ f x = f x₀ :=
  Iff.rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem self_mem_localMinSet {f : E → ℝ} {x₀ : E} (hmin : IsLocalMin f x₀) :
    x₀ ∈ localMinSet f x₀ :=
  ⟨hmin, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- § μ-PŁ (Polyak–Łojasiewicz)
-- ════════════════════════════════════════════════════════════════════════════

/-- The μ-Polyak–Łojasiewicz condition (Definition 1.2 in the paper):
      ∀ x near x₀, f(x) − f(x₀) ≤ (2μ)⁻¹ ‖Df(x)‖²
    where ‖Df(x)‖ = ‖fderiv ℝ f x‖ equals the gradient norm by Riesz. -/
def MuPL (f : E → ℝ) (μ : ℝ) (x₀ : E) : Prop :=
  ∀ᶠ x in 𝓝 x₀, f x - f x₀ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2

-- ════════════════════════════════════════════════════════════════════════════
-- § μ-EB (Error Bound)
-- ════════════════════════════════════════════════════════════════════════════

/-- The μ-Error Bound condition (Definition 1.2 in the paper):
      ∀ x near x₀, μ · dist(x, S) ≤ ‖Df(x)‖ -/
def MuEB (f : E → ℝ) (μ : ℝ) (x₀ : E) (S : Set E) : Prop :=
  ∀ᶠ x in 𝓝 x₀, μ * infDist x S ≤ ‖fderiv ℝ f x‖

-- ════════════════════════════════════════════════════════════════════════════
-- § μ-QG (Quadratic Growth)
-- ════════════════════════════════════════════════════════════════════════════

/-- The μ-Quadratic Growth condition (Definition 1.2 in the paper):
      ∀ x near x₀, (μ/2) · dist(x, S)² ≤ f(x) − f(x₀) -/
def MuQG (f : E → ℝ) (μ : ℝ) (x₀ : E) (S : Set E) : Prop :=
  ∀ᶠ x in 𝓝 x₀, μ / 2 * (infDist x S) ^ 2 ≤ f x - f x₀

-- ════════════════════════════════════════════════════════════════════════════
-- § C¹ Submanifold (orthogonal-projection characterization)
-- ════════════════════════════════════════════════════════════════════════════

/-- `S` is a C¹ embedded submanifold of `E` near `x₀` with tangent space `T`.

    There exist a neighborhood `U ∋ x₀` and a C¹ function `φ : T → Tᗮ` with
    `φ(0) = 0` and `Dφ(0) = 0`, such that for every `x ∈ U`:
      x ∈ S  ↔  π_{Tᗮ}(x − x₀) = φ(π_T(x − x₀))

    Conditions:
    - `φ(0) = 0` ensures the graph passes through `x₀`, i.e., `x₀ ∈ S`.
    - `Dφ(0) = 0` ensures the tangent space to the graph at `x₀` is exactly `T`.
    - `ContDiffAt ℝ 1 φ 0` gives C¹ regularity of the chart near the origin. -/
def IsLocalSubmanifoldAt (S : Set E) (x₀ : E) (T : Submodule ℝ E) : Prop :=
  x₀ ∈ S ∧
  ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
    (φ : T → T.orthogonal),
    ContDiffAt ℝ 1 φ 0 ∧
    φ 0 = 0 ∧
    fderiv ℝ φ 0 = 0 ∧
    ∀ x ∈ U, x ∈ S ↔
      (orthogonalProjectionOnto T.orthogonal (x - x₀) : E) =
        ((φ (orthogonalProjectionOnto T (x - x₀))) : E)

-- ════════════════════════════════════════════════════════════════════════════
-- § The Hessian
-- ════════════════════════════════════════════════════════════════════════════

/-- The Hessian of `f` at `x`, as a bilinear form.
    Type: `E →L[ℝ] (E →L[ℝ] ℝ)`.
    Applied twice: `hessian f x v w : ℝ` gives D²f(x)(v,w).
    For C² functions, this is symmetric and equals ⟨v, Hf(x)w⟩ via Riesz. -/
abbrev hessian (f : E → ℝ) (x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ f) x

/-- The kernel of the Hessian at `x`, as a submodule of E. -/
def hessianKer (f : E → ℝ) (x : E) : Submodule ℝ E :=
  LinearMap.ker (hessian f x).toLinearMap

-- ════════════════════════════════════════════════════════════════════════════
-- § μ-MB (Morse–Bott)
-- ════════════════════════════════════════════════════════════════════════════

/-- The μ-Morse–Bott property at `x₀` (Definition 1.1 in the paper).

    A C² function `f : E → ℝ` satisfies μ-MB at a local minimizer `x₀` if:
      1. S = localMinSet f x₀ is a C¹ submanifold near x₀ with tangent
         space T = ker(Hess f(x₀)),
      2. The Hessian is μ-coercive on the normal space T⊥:
         D²f(x₀)(v,v) ≥ μ ‖v‖² for all v ∈ T⊥. -/
def IsMuMB (f : E → ℝ) (μ : ℝ) (x₀ : E) : Prop :=
  let H := hessian f x₀
  let T := hessianKer f x₀
  0 < μ ∧
  IsLocalMin f x₀ ∧
  IsLocalSubmanifoldAt (localMinSet f x₀) x₀ T ∧
  ∀ v : E, v ∈ T.orthogonal → H v v ≥ μ * ‖v‖ ^ 2

end PLAcceleratedNesterovLean
