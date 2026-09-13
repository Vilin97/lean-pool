/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeanPool.PLAcceleratedNesterovLean.Convergence.MainTheoremInternal

/-!
# Public main theorem wrappers
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


local macro:max "R^" d:term : term => `(EuclideanSpace ℝ (Fin $d))
local macro:max "𝔐^" d:term : term => `(𝓘(ℝ, R^$d))

/-- Local Polyak-Łojasiewicz condition syntax for the public theorem statements. -/
syntax:max "PolyakLojasiewicz(" term ", " term ")[" term "]" : term
macro_rules
  | `(PolyakLojasiewicz($f, $μ)[$U]) =>
    `(0 < ($μ : ℝ) ∧ DifferentiableOn ℝ $f $U ∧
      ∀ x ∈ $U, ‖gradient $f x‖ ^ 2 ≥
        2 * ($μ : ℝ) * ($f x - fStar $f))

/-- `C²` manifold typeclass syntax for the public theorem statements. -/
syntax:max "C2Manifold(" term ", " term ")" : term
macro_rules
  | `(C2Manifold($M, $k)) => `(IsManifold (𝔐^$k) 2 $M)

/-- `C²` smooth embedding syntax for the public theorem statements. -/
syntax:max "C2Embedding(" term ", " term ", " term ")" : term
macro_rules
  | `(C2Embedding($ι, $k, $d)) => `(IsSmoothEmbedding (𝔐^$k) (𝔐^$d) 2 $ι)

/-- **Embedded-manifold main theorem.**

Assume the minimizer set of `f` is the range of a nonempty `C²` embedded
`k`-manifold, `U` is an open neighborhood of this manifold, `f` is `C²` on `U`,
satisfies the local `μ`-PL inequality on `U`, and has `L`-Lipschitz gradient on
`U`. A tubular sub-neighborhood is constructed internally. Then there exists a
momentum parameter `ρ`, depending only on `L` and `μ`, such that all sufficiently
local starts converge with the explicit accelerated prefactor-two bound. -/
theorem nesterov_pl_accelerated_rate
    {d : ℕ}
    (L : ℝ≥0)
    (μ : ℝ≥0) :
    ∃ ρ : ℝ,
    ∀ (f : (R^d) → ℝ),
    ∀ (k : ℕ),
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace (R^k) M]
      [C2Manifold(M, k)] [Nonempty M]
      (ι : M → (R^d)),
      C2Embedding(ι, k, d) →
      Set.range ι = argminSet f →
    ∀ (U : Set (R^d)),
      IsOpen U →
      Set.range ι ⊆ U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz(f, μ)[U] →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (R^d)),
      IsOpen Ū ∧ Set.range ι ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ t,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).x) - fStar f ≤
            2 * Real.exp (-(↑t / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  exact nesterov_pl_accelerated_rate_embedded L (μ : ℝ)

/-- **C³ main theorem.**

Assume `U` is an open neighborhood of the global minimizer set, `f` is `C³` on
`U`, satisfies the local `μ`-PL inequality on `U`, and has `L`-Lipschitz
gradient on `U`. The minimizer geometry and tubular sub-neighborhood are
constructed internally. -/
theorem nesterov_pl_accelerated_rate_c3
    {d : ℕ}
    (L : ℝ≥0)
    (μ : ℝ≥0) :
    ∃ ρ : ℝ,
    ∀ (f : (R^d) → ℝ),
    ∀ (U : Set (R^d)),
      IsOpen U →
      argminSet f ⊆ U →
      ContDiffOn ℝ 3 f U →
      PolyakLojasiewicz(f, μ)[U] →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (R^d)),
      IsOpen Ū ∧ argminSet f ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ t,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ t).x) - fStar f ≤
            2 * Real.exp (-(↑t / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  exact nesterov_pl_accelerated_rate_c3_internal L (μ : ℝ)

end PLAcceleratedNesterovLean
