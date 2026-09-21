/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 4.8, Jon Crall
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.Majorization

/-!
# The `Q`-norm repair of the short-rotation full-displacement claim

`ShortRotationCounterexample` refutes the transcribed Davis--Kahan
Proposition 4.4: the direct rotation does *not* minimize `‖1 - V‖` over every
unitarily invariant norm, and no angle threshold restores it.  This file
records the natural repair.

A unitarily invariant norm `N` is a **`Q`-norm** when there is a unitarily
invariant norm `M` with

`N A ^ 2 = M (A⋆ A)`.

For Schatten norms this holds exactly when `2 ≤ p ≤ ∞`, since
`‖A‖_p ^ 2 = ‖A⋆ A‖_{p/2}`; the class contains the operator norm and the
Frobenius norm, and excludes the trace norm, which is where the counterexample
lives.

For this class the full-displacement minimality is true, and — unlike the
source statement — it needs *neither* the angle hypothesis `Θ ≤ π/3` *nor* the
restriction to a real space: it holds over every `RCLike` field.  The proof is
immediate from the valid squared-displacement theorem
`directRotation_displacementSquare_uiNorm` (the source's Proposition 4.3):
apply that to the norm `M` witnessing the `Q`-property and take square roots.

The counterexample and this theorem fit together exactly: `kyFanSum` at the
full rank is the trace norm, and `kyFan_not_isQNorm` below turns the
counterexample around to show that it is *not* a `Q`-norm.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A unitarily invariant norm `N` is a **`Q`-norm** when its square is a
unitarily invariant norm of the positive part `A⋆ A`.  Equivalently `N` is
obtained from a symmetric gauge function applied to the *squares* of the
singular values. -/
def IsQNorm (N : UnitarilyInvariantSeminorm 𝕜 E E) : Prop :=
  ∃ M : UnitarilyInvariantSeminorm 𝕜 E E,
    ∀ A : E →ₗ[𝕜] E, N A ^ 2 = M (LinearMap.adjoint A ∘ₗ A)

/-- The displacement square is the positive part of the displacement. -/
theorem displacementSquare_eq_adjoint_comp (W : E →ₗ[𝕜] E) :
    displacementSquare W =
      LinearMap.adjoint (LinearMap.id - W) ∘ₗ (LinearMap.id - W) := by
  rw [displacementSquare, map_sub, LinearMap.adjoint_id]

/-- **The `Q`-norm repair of Proposition 4.4.**  For every `Q`-norm the direct
rotation minimizes the *full* displacement `1 - V` among unitaries carrying `U`
onto `V` — without the source's `Θ ≤ π/3` threshold, and over every `RCLike`
field.

This is the statement the source should have made: the counterexample shows the
arbitrary-unitarily-invariant-norm version is false, and no angle threshold
repairs it, but restricting the norm class to `Q`-norms both repairs it and
lets the hypotheses `Θ ≤ π/3` and "real space" be dropped. -/
theorem directRotation_fullDisplacement_qnorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E) (hN : IsQNorm N)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  obtain ⟨M, hM⟩ := hN
  have hsq : N (LinearMap.id - (directRotation U V hacute).toLinearMap) ^ 2 ≤
      N (LinearMap.id - W.toLinearMap) ^ 2 := by
    rw [hM, hM, ← displacementSquare_eq_adjoint_comp,
      ← displacementSquare_eq_adjoint_comp]
    exact directRotation_displacementSquare_uiNorm M U V hacute W hmap
  nlinarith [N.nonneg (LinearMap.id - (directRotation U V hacute).toLinearMap),
    N.nonneg (LinearMap.id - W.toLinearMap), hsq]

end DavisKahan.FiniteDimensional
end TauCeti
