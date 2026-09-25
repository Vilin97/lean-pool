/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse

/-!
# Compatibility surface for unfinished finite angle constructions

The stable finite-dimensional core moved to `DavisKahan.FiniteDimensional.Core.AngleGeometry`.
Only the still-open constructions remain declared at this historical path.

The remaining definitions use the repository's finite self-adjoint functional
calculus and Moore--Penrose inverse.  The safe tangent convention is zero on a
pole; all analytic tangent theorems carry transversality or quarter-turn
avoidance, so the pole branch is never observed there.  Two intended
dictionary theorems remain recorded in docstrings rather than stated because
the simultaneous CS-decomposition and multiset-eigenvalue bridge is still
missing:

* `tanThetaMap_eq_sin_comp_inv`: on transverse pairs, the tangent map is the
  sine block composed with the true inverse of the cosine block on its range.
* `eigenvalues_angleOperator`: the eigenvalue multiset of `angleOperator` is
  the `arcsin` image of that of `sinAngleOperator`.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Scalar tangent with the Moore--Penrose convention at poles. -/
noncomputable def safeTan (theta : ℝ) : ℝ :=
  if Real.cos theta = 0 then 0 else Real.sin theta / Real.cos theta

/-- Scalar double tangent with the Moore--Penrose convention at quarter turns. -/
noncomputable def safeTanTwo (theta : ℝ) : ℝ :=
  if Real.cos (2*theta) = 0 then 0 else
    Real.sin (2*theta) / Real.cos (2*theta)

/-- The one-sided tangent cross-map.  On the transverse part it is
`P_{Vᗮ} P_U (P_V P_U)⁻¹`.

Construction route: restrict the cosine block `P_V P_U` to the transverse
part of `U`, invert it there, compose with the sine block, and extend by zero
on the orthogonal complement (equivalently, compose the sine block with the
Moore--Penrose inverse of the cosine block once that inverse exists).  The
current total signature is provisional; bounded inversion must ultimately
require `IsTransverse U V`. -/
noncomputable def tanThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  sinThetaMap U V ∘ₗ TauCeti.moorePenroseInverse (cosThetaMap U V)

/-- The full-space canonical angle operator `Θ(U,V)` of Davis--Kahan.
Its nonzero eigenvalues are the principal angles, with the multiplicities
required by the two-projection decomposition.

Construction route: diagonalize the positive contraction `P_U P_V P_U` on
`U`, apply `arccos` to the square roots of its eigenvalues, and assign the
canonical values on the common, orthogonal, and defect summands.  Prove basis
independence through finite functional calculus (equivalently, apply
`Real.arcsin` to `sinAngleOperator U V` through that calculus). -/
noncomputable def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.selfAdjointFunctionalCalculus
    (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric
    Real.arcsin

/-- `tan Θ` on the full ambient space.  In non-acute configurations this is
understood as the Moore--Penrose/graph-operator extension on the transverse
part, with the pole recorded separately by `IsTransverse`.

Construction route: use the spectral decomposition of `angleOperator`, map
finite angles by `safeTan`, and set the quarter-turn defect summand to zero
only as a documented Moore--Penrose convention.  Theorems interpreting its
norm as a principal tangent must assume transversality or acuteness. -/
noncomputable def tanAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.selfAdjointFunctionalCalculus
    (TauCeti.selfAdjointFunctionalCalculus_isSymmetric
      (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric Real.arcsin)
    safeTan

/-- `tan (2 Θ)` on the full ambient space.

Construction route: apply `safeTanTwo` to the finite spectral decomposition
of `angleOperator`, with a theorem hypothesis excluding quarter turns whenever
the resulting operator is used analytically.  A future API may instead bundle
that pole-avoidance proof into the constructor. -/
noncomputable def tanTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.selfAdjointFunctionalCalculus
    (TauCeti.selfAdjointFunctionalCalculus_isSymmetric
      (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric Real.arcsin)
    safeTanTwo

/-- Orthogonal complements preserve the nontrivial principal angles.

Lean proof route for a weaker agent:

1. Choose the canonical two-projection decomposition into common, defect, and generic principal
  planes.
2. Show orthogonal complementation swaps the two defect blocks and leaves every generic angle
  unchanged.
3. Use `hrank` to identify the defect multiplicities; zero-padding then gives equality of the
  finitely supported principal-angle sequences.

Signature audit: The equal-rank hypothesis fixes the defect multiplicities.  With the
finitely-supported convention, additional zero angles disappear automatically, while the
nonzero and `π/2` multiplicities agree under orthogonal complementation.

Open obligation.  With the directed-sine `principalAngles`, this reduces to
`singularValues (P_{Vᗮ} P_U) = singularValues (P_V P_{Uᗮ})` at equal rank, i.e.
the two-projection statement that complementation preserves the sine spectrum.
That decomposition lemma is not yet available in the flat layer; left incomplete
pending it (or a redesign of `principalAngles` through the symmetric cosine
spectrum, cf. `principalAngles_comm`). -/
theorem principalAngles_orthogonal (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalAngles Uᗮ Vᗮ = principalAngles U V := by
  rw [principalAngles, principalAngles]
  congr 1
  change
    (complementaryProjection (Vᗮ) ∘ₗ projection (Uᗮ)).singularValues =
      (complementaryProjection V ∘ₗ projection U).singularValues
  -- `Vᗮᗮ = V`, but `projection` is indexed by an instance on the submodule, so
  -- the rewrite has to go through `simp only`
  simp only [complementaryProjection, Submodule.orthogonal_orthogonal]
  -- the complemented cross block is the adjoint of the cross block with the two
  -- subspaces exchanged, and adjoints have the same singular values
  have hadj : projection V ∘ₗ projection Uᗮ = (sinThetaMap V U).adjoint := by
    rw [sinThetaMap, complementaryProjection, LinearMap.adjoint_comp,
      projection_adjoint, projection_adjoint]
  rw [hadj, LinearMap.singularValues_adjoint]
  exact (principalSines_comm U V hrank).symm

end DavisKahan.FiniteDimensional
end TauCeti
