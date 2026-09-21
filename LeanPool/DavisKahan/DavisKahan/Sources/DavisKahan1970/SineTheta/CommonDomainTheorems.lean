/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomain
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem62

/-! # Common Domain Theorems -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Literal common-domain source forms of Theorems 6.1 and 6.2

The unbounded appendix phrases the residual identity on the common dense domain
of `A E₀` and `E₀ A₀`.  These wrappers take that equality as public data and
construct the internal full-domain package.  No smaller unspecified core is
substituted.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v


/-- Scalar-generic source bookkeeping before choosing the spectral gap. -/
structure CommonDomainSinThetaData
    (𝕜 : Type u) [RCLike 𝕜]
    (E F G H : Type v)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  /-- The ambient self-adjoint partially defined operator. -/
  A : E →ₗ.[𝕜] E
  /-- The self-adjoint partially defined trial operator. -/
  A₀ : F →ₗ.[𝕜] F
  /-- The self-adjoint operator representing the complementary spectral part. -/
  Λ₁ : G →ₗ.[𝕜] G
  /-- The bounded trial map preserving the specified operator domains. -/
  E₀ : F →L[𝕜] E
  /-- The isometric parametrization of the exact subspace. -/
  F₀ : H →L[𝕜] E
  /-- The isometric parametrization of the complementary subspace. -/
  F₁ : G →L[𝕜] E
  /-- The bounded residual in the common-domain operator identity. -/
  R : F →L[𝕜] E
  A_selfAdjoint : IsSelfAdjoint A
  A₀_selfAdjoint : IsSelfAdjoint A₀
  Λ₁_selfAdjoint : IsSelfAdjoint Λ₁
  exact_decomposition : OrthogonalExactDecomposition F₀ F₁
  common_domain : HasCommonDomain A A₀ E₀
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_on_common_domain :
    ∀ x : F, (hx : E₀ x ∈ A.domain) → (hx₀ : x ∈ A₀.domain) →
      A ⟨E₀ x, hx⟩ - E₀ (A₀ ⟨x, hx₀⟩) = R x
  F₁_intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), F₁_maps_domain y⟩ =
      F₁ (Λ₁ y)

namespace CommonDomainSinThetaData

/-- Internal data canonically constructed from the exact source domain. -/
noncomputable def toUnboundedSinThetaData
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : CommonDomainSinThetaData 𝕜 E F G H) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) :=
  unboundedSinThetaDataOfCommonDomain
    P.A P.A₀ P.Λ₁ P.E₀ P.F₁ P.R P.common_domain
    P.F₁_maps_domain P.residual_on_common_domain P.F₁_intertwines

/-- The residual of the derived unbounded sine-theta data is the source's residual. -/
@[simp]
theorem toUnboundedSinThetaData_residual
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : CommonDomainSinThetaData 𝕜 E F G H) :
    P.toUnboundedSinThetaData.residual = P.R := rfl

end CommonDomainSinThetaData

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal common-domain input for Theorem 6.1. -/
structure CommonDomainTheorem61Data where
  /-- The common-domain operator and residual data over complex Hilbert spaces. -/
  source : CommonDomainSinThetaData ℂ E F G H
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace CommonDomainTheorem61Data

/-- Package common-domain Theorem 6.1 source data as the general Theorem 6.1 record. -/
noncomputable def toTheorem61Data
    (P : CommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H)) :
    Theorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_gap := P.spectral_gap

/-- Davis--Kahan Theorem 6.1 with the appendix's exact common-domain
hypothesis and literal universal norm quantifier. -/
theorem result_every_unitarilyInvariantNorm
    (P : CommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toTheorem61Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem61Data.result_every_unitarilyInvariantNorm S N hR

/-- Exact common-domain Theorem 6.1 with arbitrary representative
coordinate spaces. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : CommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toTheorem61Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end CommonDomainTheorem61Data

/-- Literal common-domain input for Theorem 6.2. -/
structure CommonDomainTheorem62Data where
  /-- The common-domain operator and residual data over complex Hilbert spaces. -/
  source : CommonDomainSinThetaData ℂ E F G H
  /-- The positive lower bound on pairwise spectral distances. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_distance : PairwiseSpectrumGap source.A₀ source.Λ₁ gap

namespace CommonDomainTheorem62Data

/-- Package common-domain Theorem 6.2 source data as the general Theorem 6.2 record. -/
noncomputable def toTheorem62Data
    (P : CommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H)) :
    Theorem62Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_distance := P.spectral_distance

/-- Davis--Kahan Theorem 6.2 with the appendix's exact common domain. -/
theorem result
    (P : CommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.result S hR

/-- The source bound-norm fallback under an explicit finite-rank premise. -/
theorem operatorNorm_result_of_rank_le
    (P : CommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem62Data.canonicalSinTheta)
    {r : ℕ} (hRank : P.source.R.rank ≤ (r : Cardinal)) :
    P.gap * P.epsilon * ‖S.operator‖ ≤ ‖P.source.R‖ * Real.sqrt r := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.operatorNorm_result_of_rank_le S hRank

/-- Exact common-domain Theorem 6.2 with arbitrary representative
coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : CommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.result_across S hR

end CommonDomainTheorem62Data

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real common-domain input for Theorem 6.1. -/
structure RealCommonDomainTheorem61Data where
  /-- The common-domain operator and residual data over real Hilbert spaces. -/
  source : CommonDomainSinThetaData ℝ E F G H
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace RealCommonDomainTheorem61Data

/-- Real-scalar packaging of common-domain Theorem 6.1 source data. -/
noncomputable def toTheorem61Data
    (P : RealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H)) :
    RealTheorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_gap := P.spectral_gap

/-- Real Davis--Kahan Theorem 6.1 with the exact common domain. -/
theorem result_every_unitarilyInvariantNorm
    (P : RealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toTheorem61Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem61Data.result_every_unitarilyInvariantNorm S N hR

/-- Real exact common-domain Theorem 6.1 with arbitrary representative
coordinate spaces. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toTheorem61Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end RealCommonDomainTheorem61Data

/-- Real common-domain input for Theorem 6.2. -/
structure RealCommonDomainTheorem62Data where
  /-- The common-domain operator and residual data over real Hilbert spaces. -/
  source : CommonDomainSinThetaData ℝ E F G H
  /-- The positive lower bound on distances between the two real spectra. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_distance :
    ∀ lam ∈ TauCeti.LinearPMap.realSpectrum source.A₀, ∀ α ∈ TauCeti.LinearPMap.realSpectrum source.Λ₁,
      gap ≤ |lam - α|

namespace RealCommonDomainTheorem62Data

/-- Real-scalar packaging of common-domain Theorem 6.2 source data. -/
noncomputable def toTheorem62Data
    (P : RealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H)) :
    RealTheorem62Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_distance := P.spectral_distance

/-- Real Davis--Kahan Theorem 6.2 with the exact common domain. -/
theorem result
    (P : RealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.result S hR

/-- Real source bound-norm fallback. -/
theorem operatorNorm_result_of_rank_le
    (P : RealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentative P.toTheorem62Data.canonicalSinTheta)
    {r : ℕ} (hRank : P.source.R.rank ≤ (r : Cardinal)) :
    P.gap * P.epsilon * ‖S.operator‖ ≤ ‖P.source.R‖ * Real.sqrt r := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.operatorNorm_result_of_rank_le S hRank

/-- Real exact common-domain Theorem 6.2 with arbitrary representative
coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toTheorem62Data,
    CommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.result_across S hR

end RealCommonDomainTheorem62Data

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
