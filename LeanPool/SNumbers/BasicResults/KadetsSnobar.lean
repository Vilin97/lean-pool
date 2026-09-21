/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.SNumbers.BasicResults.John

/-!
# The Kadets–Snobar projection theorem

Every finite-dimensional subspace of a Banach space is the range of a bounded
projection whose norm is at most the square root of its dimension. This is a
classical fact of Banach-space geometry (Kadets–Snobar 1971; Pietsch,
*Eigenvalues and s-numbers* 1.5.5).

The theorem is reduced to the John's-ellipsoid development in `BasicResults.John`:
`John.exists_projection` supplies the projection with `‖P‖ ≤ √(dim V)`, and we
weaken `dim V` to `n`; the underlying input is `John.john_decomposition`, the
John decomposition of identity.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Kadets–Snobar theorem.** Every finite-dimensional subspace `V` of a Banach
space `Y` of dimension at most `n` is the range of a bounded projection
`P : Y →L[𝕜] Y` (`P ∘ P = P`) with operator norm `‖P‖ ≤ √n`. -/
theorem exists_projection_range_eq_of_rank_le
    {V : Submodule 𝕜 Y} {n : ℕ} (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt n := by
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hV_rank Cardinal.natCast_lt_aleph0)
  have hfr : Module.finrank 𝕜 V ≤ n := by
    rw [← Nat.cast_le (α := Cardinal), Module.finrank_eq_rank]; exact hV_rank
  obtain ⟨P, hPP, hPrange, hPnorm⟩ := John.exists_projection V
  exact ⟨P, hPP, hPrange, hPnorm.trans (Real.sqrt_le_sqrt (by exact_mod_cast hfr))⟩

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
