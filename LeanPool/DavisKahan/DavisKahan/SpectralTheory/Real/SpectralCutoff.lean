/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralCutoff

/-! # Spectral Cutoff -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The real spectral cutoff and its coherent cutoff interface

`DavisKahan/Sylvester/CutoffInterface.lean` states `SpectralCutoffInterface`
over an arbitrary `RCLike` scalar field, and
`DavisKahan/SpectralTheory/SpectralCutoff.lean` implements it over `ℂ` from the
vendored spectral calculus.  This module supplies the **real** implementation.

Four of the five laws are already available over `ℝ` from
`DavisKahan/SpectralTheory/Real/SpectralRestriction.lean`: the descended
projection `realSelfAdjointSpectralProjection` is idempotent and self-adjoint,
it preserves the operator domain, and the operator commutes with it there.

Two things genuinely had to be proved here.

* `realSpectralCutoff_range_le_domain` — the *whole range* of a bounded-band
  cutoff lies in the operator domain, not merely the image of the domain.  The
  real projection lemma `realSelfAdjointSpectralProjection_mem_domain` is only
  stated for domain vectors, so the boundedness of the band is used through the
  complex side and then read back on the real copy.

* `realSpectralCutoff_tendsto_identity` — strong convergence of the cutoffs to
  the identity, which had no real counterpart at all.  It descends from the
  complex `spectraSpectralCutoff_tendsto_identity` because `ofReal` is an
  isometry and the complex cutoff acts on the real copy by the descended real
  cutoff (`selfAdjointSpectralProjection_ofReal`).

## Why this is a sibling and not a generalization

`spectraSpectralCutoff` cannot be generalized in place to `[RCLike 𝕜]`: it is
literally `TauCeti.LinearPMap.specProjection`, and the spectral projection-valued
measure it comes from is built from the Borel functional calculus of the Cayley
transform, which exists only over `ℂ`.  The real construction is a *different*
external theorem — the conjugation-fixedness of the complexified PVM — so this
is the case the scalar-axis guidance calls a genuine two-instance split rather
than an `RCLike.I_mul_I_ax` case split.
-/

open scoped InnerProductSpace ComplexConjugate Topology
open Filter

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction

open ExactSinTheta
open ExactSinTheta.PartialMapComplexification
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real spectral cutoff `E_A([-τ, τ])`, descended from the complexified
operator's canonical spectral projection. -/
noncomputable def realSpectralCutoff
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) : E →L[ℝ] E :=
  realSelfAdjointSpectralProjection A hA (Set.Icc (-τ) τ) measurableSet_Icc

/-- The complex cutoff of the complexified operator acts on the real copy by the
real cutoff. -/
theorem spectraSpectralCutoff_ofReal
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) (x : E) :
    spectraSpectralCutoff (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) τ (ofReal x) =
      ofReal (realSpectralCutoff A hA τ x) :=
  selfAdjointSpectralProjection_ofReal A hA (Set.Icc (-τ) τ) measurableSet_Icc x

/-- Complexifying the real cutoff recovers the complex cutoff. -/
theorem complexify_realSpectralCutoff
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) :
    RealComplexification.complexify (realSpectralCutoff A hA τ) =
      spectraSpectralCutoff (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) τ :=
  complexify_realSelfAdjointSpectralProjection A hA (Set.Icc (-τ) τ) measurableSet_Icc

/-- Real spectral cutoffs are orthogonal projections. -/
theorem realSpectralCutoff_isOrthogonalProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) :
    realSpectralCutoff A hA τ ∘L realSpectralCutoff A hA τ =
        realSpectralCutoff A hA τ ∧
      (realSpectralCutoff A hA τ).IsSymmetric := by
  constructor
  · exact realSelfAdjointSpectralProjection_idem A hA (Set.Icc (-τ) τ) measurableSet_Icc
  · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (realSelfAdjointSpectralProjection_isSelfAdjoint A hA (Set.Icc (-τ) τ)
        measurableSet_Icc)

/-- **Every real cutoff vector lies in the operator domain.**  Not only the
image of the domain: the band `[-τ, τ]` is bounded, so the whole range of the
cutoff is in the domain. -/
theorem realSpectralCutoff_range_le_domain
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) :
    LinearMap.range (realSpectralCutoff A hA τ).toLinearMap ≤ A.domain := by
  rintro y ⟨x, rfl⟩
  have hC := spectraSpectralCutoff_range_le_domain
    (PartialMapComplexification.complexify A)
    (PartialMapComplexification.isSelfAdjoint_complexify hA) τ
    (show spectraSpectralCutoff (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) τ (ofReal x) ∈
      LinearMap.range (spectraSpectralCutoff (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) τ).toLinearMap from
      ⟨ofReal x, rfl⟩)
  rw [spectraSpectralCutoff_ofReal A hA τ x,
    PartialMapComplexification.mem_complexify_domain_iff] at hC
  simpa using hC.1

/-- Real spectral cutoffs preserve the operator domain and commute with the
operator there. -/
theorem realSpectralCutoff_commutes_on_domain
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (τ : ℝ) (x : A.domain) :
    ∃ hx : realSpectralCutoff A hA τ (x : E) ∈ A.domain,
      A ⟨realSpectralCutoff A hA τ (x : E), hx⟩ =
        realSpectralCutoff A hA τ (A x) :=
  ⟨realSelfAdjointSpectralProjection_mem_domain A hA measurableSet_Icc x,
    realSelfAdjoint_apply_spectralProjection A hA measurableSet_Icc x⟩

/-- **The real spectral cutoffs converge strongly to the identity.**

This is the one interface law with no real counterpart before now.  It descends
from the complex statement along the canonical real copy: `ofReal` is an
isometry, and the complex cutoff acts on `ofReal x` by the real cutoff. -/
theorem realSpectralCutoff_tendsto_identity
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    Tendsto (fun τ : ℝ => realSpectralCutoff A hA τ x) atTop (𝓝 x) := by
  have hC := spectraSpectralCutoff_tendsto_identity
    (PartialMapComplexification.complexify A)
    (PartialMapComplexification.isSelfAdjoint_complexify hA) (ofReal x)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hC ⊢
  refine hC.congr fun τ => ?_
  rw [spectraSpectralCutoff_ofReal A hA τ x, ← map_sub,
    LinearIsometry.norm_map]

/-- **The real implementation of the coherent spectral cutoff interface.** -/
noncomputable def realSpectraSpectralCutoffInterface
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) :
    SpectralCutoffInterface A hA where
  cutoff := realSpectralCutoff A hA
  isOrthogonalProjection := realSpectralCutoff_isOrthogonalProjection A hA
  range_le_domain := realSpectralCutoff_range_le_domain A hA
  commutes_on_domain := realSpectralCutoff_commutes_on_domain A hA
  tendsto_identity := realSpectralCutoff_tendsto_identity A hA

/-- The interface's cutoff family is the real spectral cutoff. -/
@[simp] theorem realSpectraSpectralCutoffInterface_cutoff
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) :
    (realSpectraSpectralCutoffInterface A hA).cutoff = realSpectralCutoff A hA :=
  rfl

end
end RealSpectralRestriction
end DavisKahan
end TauCeti
