/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanPool.SNumbers.BasicResults.John

/-!
# The Garling–Gordon projection theorem

A closed subspace of a Banach space whose codimension is at most `n` is the
kernel of a bounded projection of norm at most `√n + ε`, for every `ε > 0`. This
is a classical fact of Banach-space geometry (Garling–Gordon 1971; Pietsch,
*Eigenvalues and s-numbers* 1.7.17). It is the *dual* of Kadets–Snobar
(`BasicResults.KadetsSnobar`).

The theorem is reduced to the John's-ellipsoid development in `BasicResults.John`:
`John.exists_projection_ker` supplies, for each `ε > 0`, a projection with kernel
`M` and `‖P‖ ≤ √(codim M) + ε`, and we weaken `codim M` to `n`; the underlying
input is `John.john_decomposition`, the John decomposition of identity. The `ε`
is intrinsic to the general Banach setting
(the quotient norm is an infimum that need not be attained); the applications in
`SNumbers.Inequalities` recover the sharp constant by letting `ε → 0`.
-/

@[expose] public section

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Garling–Gordon theorem (ε-form).** For a closed subspace `M` of a normed
space `X` of codimension at most `n` and every `ε > 0`, there is a bounded
projection `P : X →L[𝕜] X` (`P ∘ P = P`) with kernel exactly `M` and operator
norm `‖P‖ ≤ √n + ε`. -/
theorem exists_projection_ker_eq_of_codim_le
    {M : Submodule 𝕜 X} (hM_closed : IsClosed (M : Set X)) {n : ℕ}
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧
      LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧ ‖P‖ ≤ Real.sqrt n + ε := by
  have : FiniteDimensional 𝕜 (X ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hM_codim Cardinal.natCast_lt_aleph0)
  have hfrn : Module.finrank 𝕜 (X ⧸ M) ≤ n := by
    rw [← Nat.cast_le (α := Cardinal), Module.finrank_eq_rank]; exact hM_codim
  have hfr : (Module.finrank 𝕜 (X ⧸ M) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfrn
  obtain ⟨P, hPP, hPker, hPnorm⟩ := John.exists_projection_ker M hε
  refine ⟨P, hPP, hPker, hPnorm.trans ?_⟩
  gcongr

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
