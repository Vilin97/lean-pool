/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Sharp projector geometry for bounded Davis--Kahan theory

The two-projection norm identity and the sharp factor-one coercive projector
theorem over arbitrary `RCLike` scalars.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/BoundedOperator/Projector.lean`
before the dependency-closed base of the sin-Θ core moved
into the staging layer.

**Renamespaced,** for the reason its sibling
`SinTheta.lean` records: the sharp projector bound is generic operator geometry
and was filed under the paper's namespace.  It now lives in `Submodule`, the
namespace of its conclusion's head symbol.

**Two declarations were deleted rather than moved.**  `norm_add_eq_max_of_block`
and `norm_starProjection_sub_eq_max` were one-line re-exports of
`ContinuousLinearMap.norm_add_eq_max_of_block` and
`Submodule.norm_starProjection_sub_eq_max`, which already exist in
`Projection/Blocks.lean` and `Projection/Gap.lean`; the second would in fact have
collided with its own target once this file moved into `Submodule`.
Consumers use the canonical declarations directly.
-/

@[expose] public section

namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The sharp (factor-one) operator-norm Davis--Kahan projector theorem.**  With
a two-sided coercive spectral gap — `A`'s form `≥ (c+g)` on `U` and `≤ c` on
`Uᗮ`, `B`'s form `≥ (c+g)` on `W` and `≤ c` on `Wᗮ` — the orthogonal
projectors onto these reducing subspaces on an arbitrary `RCLike` Hilbert space
satisfy the sharp bound

`‖P_U − P_W‖ ≤ ‖B − A‖ / g`

with constant one and no equal-rank hypothesis.  Combines the projector-difference
identity `Submodule.norm_starProjection_sub_eq_max` with the two dimension-free
directed `sin Θ` estimates `Submodule.sinTheta_directed_coercive`. -/
theorem opNorm_starProjection_sub_le_of_coercive
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUlo : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hWlo : ∀ x ∈ Wᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  rw [U.norm_starProjection_sub_eq_max W]
  refine max_le ?_ ?_
  · rw [show (1 - W.starProjection : H →L[𝕜] H) = Wᗮ.starProjection from
      (Submodule.starProjection_orthogonal' W).symm]
    exact sinTheta_directed_coercive hA hB hU
      (ContinuousLinearMap.IsSymmetric.reduces_of_invariant hB hW.2) hg hUc hWlo
  · rw [show (1 - U.starProjection : H →L[𝕜] H) = Uᗮ.starProjection from
      (Submodule.starProjection_orthogonal' U).symm]
    have h := sinTheta_directed_coercive hB hA hW
      (ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA hU.2) hg hWc hUlo
    rwa [show ‖A - B‖ = ‖B - A‖ from by rw [← neg_sub, norm_neg]] at h


/-- Sharp projector bound stated with reusable subspace form-bound predicates. -/
theorem opNorm_starProjection_sub_le_of_formBounds
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : A.LowerFormBoundOn U (c + g))
    (hUlo : A.UpperFormBoundOn Uᗮ c)
    (hWhi : B.LowerFormBoundOn W (c + g))
    (hWlo : B.UpperFormBoundOn Wᗮ c) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g :=
  opNorm_starProjection_sub_le_of_coercive hA hB hU hW hg hUhi hUlo hWhi hWlo


end Submodule
