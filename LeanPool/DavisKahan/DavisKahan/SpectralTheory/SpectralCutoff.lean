/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
public import LeanPool.DavisKahan.DavisKahan.Sylvester.CutoffInterface
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestriction

/-! # Spectral Cutoff -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Spectral cutoffs for the unbounded Sylvester argument

The cutoff at radius `τ` is the canonical spectral projection onto `[-τ, τ]`
for a self-adjoint partial map, taken from its projection-valued measure
`TauCeti.LinearPMap.spectralPVM`.

The four interface laws come from that measure: projection algebra,
bounded-band domain inclusion, commutation with the operator, and strong
convergence of bounded indicator symbols to the constant one symbol.

Spectra is retired and nothing here is vendored from it; no one-parameter
unitary group is constructed.
-/

open scoped InnerProductSpace Topology
open Filter

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral cutoff `E_A([-τ,τ])`. -/
noncomputable def spectraSpectralCutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) : H →L[ℂ] H :=
  selfAdjointSpectralProjection A hA (Set.Icc (-τ) τ) measurableSet_Icc

/-- Spectral cutoffs are orthogonal projections. -/
theorem spectraSpectralCutoff_isOrthogonalProjection
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    spectraSpectralCutoff A hA τ ∘L spectraSpectralCutoff A hA τ =
        spectraSpectralCutoff A hA τ ∧
      (spectraSpectralCutoff A hA τ).IsSymmetric := by
  constructor
  · exact (TauCeti.LinearPMap.spectralPVM hA).proj_idem (Set.Icc (-τ) τ) measurableSet_Icc
  · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      ((TauCeti.LinearPMap.spectralPVM hA).isSelfAdjoint_proj
        (Set.Icc (-τ) τ) measurableSet_Icc)

/-- Every spectral-cutoff vector lies in the closed-operator domain. -/
theorem spectraSpectralCutoff_range_le_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    LinearMap.range (spectraSpectralCutoff A hA τ).toLinearMap ≤ A.domain := by
  rintro y ⟨x, rfl⟩
  exact TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
    (M := max 0 τ) (fun s hs => le_trans (abs_le.mpr ⟨hs.1, hs.2⟩) (le_max_right 0 τ))
    ⟨x, rfl⟩

/-- Spectral cutoffs preserve the domain and commute with the closed operator
there. -/
theorem spectraSpectralCutoff_commutes_on_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) (x : A.domain) :
    ∃ hx : spectraSpectralCutoff A hA τ (x : H) ∈ A.domain,
      A ⟨spectraSpectralCutoff A hA τ (x : H), hx⟩ =
        spectraSpectralCutoff A hA τ (A x) :=
  ⟨selfAdjointSpectralProjection_mem_domain A hA measurableSet_Icc x,
    selfAdjoint_apply_spectralProjection A hA measurableSet_Icc x⟩

/-- Spectral cutoffs converge strongly to the identity. -/
theorem spectraSpectralCutoff_tendsto_identity
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : H) :
    Tendsto (fun τ : ℝ => spectraSpectralCutoff A hA τ x)
      atTop (𝓝 x) :=
  TauCeti.LinearPMap.tendsto_specProjection_Icc hA x

/-- The implementation of the coherent spectral cutoff interface. -/
noncomputable def spectraSpectralCutoffInterface
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    SpectralCutoffInterface A hA where
  cutoff := spectraSpectralCutoff A hA
  isOrthogonalProjection := spectraSpectralCutoff_isOrthogonalProjection A hA
  range_le_domain := spectraSpectralCutoff_range_le_domain A hA
  commutes_on_domain := spectraSpectralCutoff_commutes_on_domain A hA
  tendsto_identity := spectraSpectralCutoff_tendsto_identity A hA

end ExactSinTheta
end DavisKahan
end TauCeti
