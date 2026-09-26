/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonCore
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem62

/-! # Common Core Theorems -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Literal graph-core forms of the generalized sine theorems

These are source-facing forms for the interpretation in which the unbounded
residual equation is initially known only on a common operator core.  The core
is graph-dense for the trial operator, so closedness of the ambient operator
extends both domain compatibility and the residual equation to all of
`dom A₀`.  The actual sine-theta estimates then follow from the accepted full-
domain theorems without any stronger spectral or norm assumption.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v


/-- Scalar-generic source bookkeeping with the residual equation supplied on a
graph core of the trial operator. -/
structure CommonCoreSinThetaData
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
  /-- The bounded trial map into the ambient space. -/
  E₀ : F →L[𝕜] E
  /-- The isometric parametrization of the exact subspace. -/
  F₀ : H →L[𝕜] E
  /-- The isometric parametrization of the complementary subspace. -/
  F₁ : G →L[𝕜] E
  /-- The bounded residual whose identity is initially imposed on the graph core. -/
  R : F →L[𝕜] E
  A_selfAdjoint : IsSelfAdjoint A
  A₀_selfAdjoint : IsSelfAdjoint A₀
  Λ₁_selfAdjoint : IsSelfAdjoint Λ₁
  exact_decomposition : OrthogonalExactDecomposition F₀ F₁
  /-- The graph-core data certifying the residual identity. -/
  coreResidual : CommonCoreResidualData A A₀ E₀ R
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  F₁_intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), F₁_maps_domain y⟩ =
      F₁ (Λ₁ y)

namespace CommonCoreSinThetaData

/-- The accepted full-domain bookkeeping obtained by the graph-core extension
argument. -/
noncomputable def toUnboundedSinThetaData
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : CommonCoreSinThetaData 𝕜 E F G H) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) :=
  unboundedSinThetaDataOfCommonCore
    P.A P.A₀ P.Λ₁ P.E₀ P.F₁ P.R P.coreResidual P.A_selfAdjoint.isClosed
    P.F₁_maps_domain P.F₁_intertwines

/-- The residual of the derived unbounded sine-theta data is the source's residual. -/
@[simp]
theorem toUnboundedSinThetaData_residual
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : CommonCoreSinThetaData 𝕜 E F G H) :
    P.toUnboundedSinThetaData.residual = P.R := rfl

end CommonCoreSinThetaData

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 6.1 data with the residual equation supplied only on a graph core. -/
structure CommonCoreTheorem61Data where
  /-- The common-core operator and residual data over the complex Hilbert spaces. -/
  source : CommonCoreSinThetaData ℂ E F G H
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace CommonCoreTheorem61Data

/-- Package common-core Theorem 6.1 source data as the general Theorem 6.1 record. -/
noncomputable def toTheorem61Data
    (P : CommonCoreTheorem61Data
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

/-- Theorem 6.1 under the graph-core reading of the appendix. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : CommonCoreTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toTheorem61Data,
    CommonCoreSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end CommonCoreTheorem61Data

/-- Theorem 6.2 data with the residual equation supplied only on a graph core. -/
structure CommonCoreTheorem62Data where
  /-- The common-core operator and residual data over the complex Hilbert spaces. -/
  source : CommonCoreSinThetaData ℂ E F G H
  /-- The positive lower bound on pairwise spectral distances. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_distance : PairwiseSpectrumGap source.A₀ source.Λ₁ gap

namespace CommonCoreTheorem62Data

/-- Package common-core Theorem 6.2 source data as the general Theorem 6.2 record. -/
noncomputable def toTheorem62Data
    (P : CommonCoreTheorem62Data
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

/-- Theorem 6.2 under the graph-core reading of the appendix. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : CommonCoreTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toTheorem62Data,
    CommonCoreSinThetaData.toUnboundedSinThetaData] using
    P.toTheorem62Data.result_across S hR

end CommonCoreTheorem62Data

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real Theorem 6.1 data with the residual equation supplied on a graph core. -/
structure RealCommonCoreTheorem61Data where
  /-- The common-core operator and residual data over the real Hilbert spaces. -/
  source : CommonCoreSinThetaData ℝ E F G H
  /-- The positive form gap between the trial and complementary operators. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace RealCommonCoreTheorem61Data

/-- Real-scalar packaging of common-core Theorem 6.1 source data. -/
noncomputable def toRealTheorem61Data
    (P : RealCommonCoreTheorem61Data
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

/-- Real Theorem 6.1 under the graph-core reading of the appendix. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealCommonCoreTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toRealTheorem61Data.canonicalSinTheta)
    (N : SymmetricNormingFunction) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toRealTheorem61Data,
    CommonCoreSinThetaData.toUnboundedSinThetaData] using
    P.toRealTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end RealCommonCoreTheorem61Data

/-- Real Theorem 6.2 data with the residual equation supplied on a graph core. -/
structure RealCommonCoreTheorem62Data where
  /-- The common-core operator and residual data over the real Hilbert spaces. -/
  source : CommonCoreSinThetaData ℝ E F G H
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

namespace RealCommonCoreTheorem62Data

/-- Real-scalar packaging of common-core Theorem 6.2 source data. -/
noncomputable def toRealTheorem62Data
    (P : RealCommonCoreTheorem62Data
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

/-- Real Theorem 6.2 under the graph-core reading of the appendix. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : RealCommonCoreTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : SinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toRealTheorem62Data.canonicalSinTheta)
    (hR : approximationNumberEnergy P.source.R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      P.gap * P.epsilon * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤
        ContinuousLinearMap.hilbertSchmidtNorm P.source.R := by
  simpa [toRealTheorem62Data,
    CommonCoreSinThetaData.toUnboundedSinThetaData] using
    P.toRealTheorem62Data.result_across S hR

end RealCommonCoreTheorem62Data

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
