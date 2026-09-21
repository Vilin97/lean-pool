/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation

/-!
# Frobenius sine distance between subspaces

This module gives the sine cross-projection its canonical Frobenius-norm
notation.  The definition is paper-independent: it is the Frobenius norm of
`sinThetaMap U V`, and is used by both the reusable single-angle theory and
paper-facing perturbation packages.

## Main results

* `TauCeti.sinThetaFrobenius`: the Frobenius norm of the sine cross-projection.
* `TauCeti.sinThetaFrobenius_eq`: the characteristic equation for rewriting it.
* `TauCeti.sinThetaFrobenius_nonneg`: the public nonnegativity interface.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Frobenius sine distance in canonical subspace notation. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (sinThetaMap U V)

/-- `sinThetaFrobenius` is the Frobenius norm of the sine cross-projection. -/
theorem sinThetaFrobenius_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinThetaFrobenius U V =
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (sinThetaMap U V) := by
  rw [sinThetaFrobenius]

/-- The Frobenius sine distance is nonnegative.

This is the public order-theoretic interface to the opaque
`sinThetaFrobenius` definition; downstream application packages should use
this lemma rather than relying on definitional unfolding. -/
theorem sinThetaFrobenius_nonneg (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinThetaFrobenius U V := by
  rw [sinThetaFrobenius_eq]
  exact (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)).nonneg _

end TauCeti
