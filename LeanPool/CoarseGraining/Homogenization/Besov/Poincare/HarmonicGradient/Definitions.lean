/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Bounds

/-! # Definitions -/

namespace Homogenization

open scoped BigOperators ENNReal

variable {d : ℕ}

/-!
# Vector projected dual mean-zero Poincare estimate

The note-facing Caccioppoli wrappers need a Poincare estimate that controls
the oscillation of a scalar field by the dual norm of its full gradient on
each descendant.

The pre-existing scalar/componentwise version
`CubeDescendantProjectedDualMeanZeroPoincareEstimate` is mathematically
**too strong** when applied to a single coordinate of a gradient: an affine
function `u(x) = x_j` (with `j ≠ i`) has zero `i`-th partial derivative but
nonzero oscillation, so the componentwise statement is false in general.

This file introduces the correct vector replacement: a sum-over-coordinates
form whose right-hand side controls every component of the gradient. It
mirrors the scalar `to_localEstimate` consumer pattern from
`Poincare/Descendants.lean` so the existing multiscale corridor can absorb
it after summing the per-component bounds.

The underlying inequality `‖u − ⟨u⟩_R‖_{L²(R)} ≲ ∑_i ‖∂_i u‖_{B^{-1}_{2,1}(R)}`
is a pure duality fact about `H¹` (proved by pairing against mean-zero `L²`
test, integration by parts, and constant-coefficient Dirichlet regularity).
**Harmonicity is not required.**

This file is layered under `Besov/`, so it does **not** import any
`PDE/`, `Sobolev/`, or `Deterministic/` content. The load-bearing
analytic constructor `of_h1Function`, together with the harmonic-function
corollary `of_aHarmonicFunction`, lives downstream in
`Deterministic/CoarseCaccioppoli/SingleCubeToRaw/HarmonicCanonicalGradient.lean`
(where the `H1Function` and `AHarmonicFunction` types are in scope).
-/

def CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (cubeProjection R (M - j) (fun x => G x i))

/-- The single-cube projected vector dual mean-zero Poincare estimate. This is
the local theorem that the descendant estimate applies on each subcube. -/
def CubeProjectedDualMeanZeroVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (N : ℕ) : Prop :=
  cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
    C * ∑ i : Fin d,
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (cubeProjection Q N (fun x => G x i))

/-- Infinite-depth vector dual mean-zero Poincare estimate.

This is the analytically natural target for general `H¹` functions: the
oscillation is controlled by the full negative Besov seminorm of each gradient
component, not by a fixed finite projection depth. -/
def CubeDualMeanZeroVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) : Prop :=
  cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
    C * ∑ i : Fin d,
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i)

/-- Descendant form of the infinite-depth vector dual mean-zero Poincare
estimate. -/
def CubeDescendantDualMeanZeroVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ i : Fin d,
        cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i)

/-- Constant-mode-safe infinite-depth vector Poincare estimate.

The right-hand side uses the full dual norm of each gradient component. Unlike
the mean-zero-dual-only target, this norm sees constant gradient modes and is
therefore the corrected surface for arbitrary `H¹` inputs. -/
def CubeDualFullVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) : Prop :=
  cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
    C * ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i)

/-- Descendant form of the constant-mode-safe full-dual vector Poincare
estimate. -/
def CubeDescendantDualFullVectorPoincareEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ i : Fin d,
        cubeBesovDualFullNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i)

/-- Vector analogue of `CubeLocalMultiscalePoincareEstimate`: oscillation of
the scalar `u` is controlled by `C` times the sum over coordinates of the
local `q = 1` partial circ norm at the matching multiscale depth. -/
def CubeLocalMultiscalePoincareVectorEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ i : Fin d,
        cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
          (fun x => G x i)

/-- Vector local Poincare estimate with the full local circ norm on each
descendant.  This is the honest bridge target produced by a full-dual
Poincare estimate; passing from this to the finite-partial multiscale corridor
requires a separate infinite-to-finite summation argument. -/
def CubeLocalFullCircPoincareVectorEstimate
    (Q : TriadicCube d) (C : ℝ) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ i : Fin d,
        cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i)

end Homogenization
