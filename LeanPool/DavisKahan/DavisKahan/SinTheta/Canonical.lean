/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.IntervalExterior
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.AllGap
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.FormBoundedGap

/-! # Canonical -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Source-shaped generalized and isometric problems over the form-bounded gap

The generalized problems and the complex isometric problem are proved through
the direct gap engine, so they are complete.  The scalar-generic isometric
theorem `FormBoundedIsometricSinThetaProblem.result` still runs through the
form-bounded engine and therefore stays with the open obligations; the manuscript
surface selects the complex proof here and the real proof in `Real.Canonical`.

## Two copies of each problem, and which one is redundant

`SinTheta/Unbounded/AllGap.lean` declares `SpectralGeneralSinThetaProblem` and
`SpectralIsometricSinThetaProblem` with the same fields as the structures here
and the same `result` statements, differing **only** in `spectral_gap`: those
take `SpectralSylvesterGap`, these take `FormBoundedSylvesterGap`.

`formBoundedSylvesterGap_of_spectral` (`Sylvester/Unbounded/FormBoundedGap.lean`)
turns a spectral gap into a form-bounded one in every configuration, so **the
structures here are the more general pair**: every spectral package yields one of
these, and `SpectralGeneralSinThetaProblem.result` is therefore a corollary of
`FormBoundedGeneralSinThetaProblem.result` rather than an independent theorem.
The converse fails on the ordered configurations — recovering a spectral
containment from a form bound is the half of the spectral theorem this tree does
not have — so the redundancy runs one way only.

Collapsing the pair is real work rather than a deletion, because the two `result`
proofs take different routes through the engines; it is posted as its own lane.

`FormBoundedIsometricSinThetaProblem` is additionally `RCLike`-generic where the
spectral one is `ℂ`-only, so it also carries the real-scalar surface in
`Real/Canonical.lean`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta



section ComplexGeneralized

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complete input package for the generalized Davis--Kahan 1970 sine theorem,
with the spectral gap given as `FormBoundedSylvesterGap`.

`data.A` is the ambient self-adjoint closed operator, `data.A₀` is the trial
block, and `data.Λ₁` is the complementary exact block.  The residual is bounded
on the ambient Hilbert spaces even when the diagonal operators are unbounded.
The lower frame bound permits a non-isometric trial map.

`SpectralGeneralSinThetaProblem` is the same package over the spectral gap; see the
module docstring for why both exist. -/
structure FormBoundedGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial operator and the complementary restriction. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace FormBoundedGeneralSinThetaProblem

/-- The complete generalized source target. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FormBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact_complex
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- The raw complementary-block form used before the final angle
identification. -/
theorem complementaryBlock_result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FormBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (sinThetaBlock P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (sinThetaBlock P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  generalizedSinTheta_unbounded_complex
    N P.data P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition.isometry₁ P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end FormBoundedGeneralSinThetaProblem

/-- Complete source-shaped package for the proved finite interval/exterior
branch.  Unlike `FormBoundedGeneralSinThetaProblem.spectral_gap`, this uses the genuine
`Spectra` spectrum and does not pass through the ordered half-line engine. -/
structure FiniteIntervalGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The lower endpoint of the interval containing the trial spectrum. -/
  intervalLower : ℝ
  /-- The upper endpoint of the interval containing the trial spectrum. -/
  intervalUpper : ℝ
  /-- The positive separation between the trial spectral interval and the complementary
  spectrum. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  interval_order : intervalLower ≤ intervalUpper
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : SpectralIntervalExteriorGap data.A₀ data.Λ₁
    intervalLower intervalUpper gap
  residual_mem : N.Mem data.residual

namespace FiniteIntervalGeneralSinThetaProblem

/-- Completed generalized finite interval/exterior theorem with the exact
source-facing directed sine operator. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FiniteIntervalGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  by
    simpa only [UnboundedSinThetaData,
      FanDominantIdealFamily.toSymmetric_mem,
      FanDominantIdealFamily.toSymmetric_gaugeReal] using
      generalizedSinTheta_unbounded_exact_of_intervalExteriorGap
        N.toSymmetricOperatorIdealFamily P.data P.exactMap
        P.ambient_selfAdjoint
        P.trial_selfAdjoint
        P.complement_selfAdjoint
        P.exact_decomposition P.interval_order P.gap_pos
        P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- Complementary-overlap form of the completed finite interval/exterior
branch. -/
theorem complementaryBlock_result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FiniteIntervalGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (sinThetaBlock P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (sinThetaBlock P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  by
    simpa only [UnboundedSinThetaData,
      FanDominantIdealFamily.toSymmetric_mem,
      FanDominantIdealFamily.toSymmetric_gaugeReal] using
      generalizedSinTheta_unbounded_of_intervalExteriorGap
        N.toSymmetricOperatorIdealFamily P.data
        P.ambient_selfAdjoint
        P.trial_selfAdjoint
        P.complement_selfAdjoint
        P.exact_decomposition.isometry₁ P.interval_order P.gap_pos
        P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end FiniteIntervalGeneralSinThetaProblem

end ComplexGeneralized

section GenericIsometric

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Complete input package for the isometric specialization, with the spectral
gap given as `FormBoundedSylvesterGap`.

Unlike `SpectralIsometricSinThetaProblem`, which is `ℂ`-only, this package is
`RCLike`-generic and carries the real-scalar surface in `Real/Canonical.lean`. -/
structure FormBoundedIsometricSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[𝕜] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  trial_isometry : IsometricEmbedding data.X
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial operator and the complementary restriction. -/
  gap : ℝ
  gap_pos : 0 < gap
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

end GenericIsometric

section ComplexIsometricBridge

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FormBoundedIsometricSinThetaProblem

/-- Complex specialization of the source-shaped isometric problem, routed
through the direct manuscript gap engine. -/
theorem result_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FormBoundedIsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        ((ContinuousLinearMap.id ℂ E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℂ E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.gauge P.data.residual :=
  sinTheta_unbounded_exact_complex
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

/-- Package a complex isometric problem as the generalized theorem with lower
frame bound one. -/
noncomputable def toGeneral
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : FormBoundedIsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
      (G := G) (H := H) N) :
    FormBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := 1
  gap_pos := P.gap_pos
  frameLowerBound_pos := zero_lt_one
  lowerFrame := lowerFrameBound_one_of_isometry P.trial_isometry
  spectral_gap := P.spectral_gap
  residual_mem := P.residual_mem

end FormBoundedIsometricSinThetaProblem

end ComplexIsometricBridge

section SpectralPackages

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complete source-shaped input package for the generalized all-gap theorem,
with the spectral gap stated as `SpectralSylvesterGap`.

`FormBoundedGeneralSinThetaProblem` is the same package over the form-bounded
gap, and is the more general of the two: `formBoundedSylvesterGap_of_spectral`
builds it from this one, so `result` here is a corollary of `result` there.
`SinTheta/Canonical.lean` records the details. -/
structure SpectralGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive spectral separation used in the Sylvester estimate. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : SpectralSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace SpectralGeneralSinThetaProblem

/-- **Every spectral package is a form-bounded package.**  Only the gap field changes, by
`formBoundedSylvesterGap_of_spectral`, which transports the spectral gap in all three
configurations; every other field is carried across unchanged.

This is what makes the redundancy of the two packages a *theorem* rather than an observation,
and it is why `result` below is a corollary rather than a second derivation.  The converse does
not exist: recovering a spectral containment from a form bound is the half of the spectral
theorem this tree does not have, so the redundancy runs one way only.

Prose merged from `edward (aiq-gpu)`'s parallel implementation of this lane, which kept the
structures in `SinTheta/Unbounded/AllGap.lean`; the relocation here is `jon (toothbrush)`'s. -/
def toFormBounded
    {N : KyFanDominantIdealFamily (𝕜 := ℂ)}
    (P : SpectralGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    FormBoundedGeneralSinThetaProblem (E := E) (F := F) (G := G) (H := H) N where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := P.frameLowerBound
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.frameLowerBound_pos
  lowerFrame := P.lowerFrame
  spectral_gap :=
    formBoundedSylvesterGap_of_spectral P.trial_selfAdjoint
      P.complement_selfAdjoint P.spectral_gap
  residual_mem := P.residual_mem

/-- Source-shaped generalized spectral all-gap endpoint, as a corollary of the form-bounded
endpoint at `P.toFormBounded`.  The statement is unchanged: the conversion touches no field
the conclusion mentions. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : SpectralGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  FormBoundedGeneralSinThetaProblem.result N P.toFormBounded

end SpectralGeneralSinThetaProblem

/-- Complete source-shaped input package for the isometric all-gap theorem, with
the spectral gap stated as `SpectralSylvesterGap`.

This package is `ℂ`-only; `FormBoundedIsometricSinThetaProblem` is the
`RCLike`-generic form-bounded counterpart. -/
structure SpectralIsometricSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  trial_isometry : IsometricEmbedding data.X
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive spectral separation used in the Sylvester estimate. -/
  gap : ℝ
  gap_pos : 0 < gap
  spectral_gap : SpectralSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace SpectralIsometricSinThetaProblem

/-- Every spectral isometric package is a form-bounded one, by the same gap
transport. -/
def toFormBounded
    {N : KyFanDominantIdealFamily (𝕜 := ℂ)}
    (P : SpectralIsometricSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    FormBoundedIsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
      (G := G) (H := H) N where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  trial_isometry := P.trial_isometry
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  gap_pos := P.gap_pos
  spectral_gap :=
    formBoundedSylvesterGap_of_spectral P.trial_selfAdjoint
      P.complement_selfAdjoint P.spectral_gap
  residual_mem := P.residual_mem

/-- Source-shaped isometric spectral all-gap endpoint. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : SpectralIsometricSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        ((ContinuousLinearMap.id ℂ E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℂ E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.gauge P.data.residual :=
  FormBoundedIsometricSinThetaProblem.result_complex N P.toFormBounded

end SpectralIsometricSinThetaProblem

end SpectralPackages


end ExactSinTheta
end DavisKahan
end TauCeti
