/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.FormBoundedGap
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Canonical

/-! # Reducing -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Natural reducing-subspace inputs for the unbounded sine-theta theorem

This module separates the operator-theoretic bookkeeping from spectral theory.
A caller supplies an ambient self-adjoint closed operator and a reducing exact
subspace. The complementary restriction, inclusion intertwiners, orthogonal
exact decomposition, and `UnboundedSinThetaData` package are constructed
canonically.

The problem records are scalar-generic. Their result methods are explicitly
specialized to the two scalar fields for which the complete analytic engines
are available.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

open TauCeti.DavisKahan

/-- An orthogonally complemented subspace is complete.  This repeats the
instance carried by the reducing-restriction core, which declares it locally and
therefore does not export it to importing modules. -/
noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The canonical inclusions of an orthogonally complemented subspace and its
orthogonal complement form exact Hilbert coordinates. -/
theorem reducingSubspace_orthogonalExactDecomposition
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    OrthogonalExactDecomposition U.subtypeL Uᗮ.subtypeL := by
  refine
    { isometry₀ := fun _ => rfl
      isometry₁ := fun _ => rfl
      orthogonal := ?_
      projection_sum := ?_ }
  · change U.subtypeL.adjoint ∘L Uᗮ.subtypeL = 0
    rw [Submodule.adjoint_subtypeL]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change U.starProjection (x : E) = 0
    have hfix : Uᗮ.starProjection (x : E) = (x : E) :=
      Submodule.starProjection_eq_self_iff.mpr x.property
    have hsum := U.starProjection_add_starProjection_orthogonal (x : E)
    rw [hfix] at hsum
    exact add_eq_right.mp hsum
  · change U.subtypeL ∘L U.subtypeL.adjoint +
        Uᗮ.subtypeL ∘L Uᗮ.subtypeL.adjoint =
      ContinuousLinearMap.id 𝕜 E
    rw [Submodule.adjoint_subtypeL, Submodule.adjoint_subtypeL]
    apply ContinuousLinearMap.ext
    intro x
    exact U.starProjection_add_starProjection_orthogonal x

/-- Internal unbounded sine-theta data constructed from a reducing exact
subspace.  Density and graph closedness are carried as hypotheses rather than
bundled into the operator, so the complementary restriction inherits both from
the canonical `LinearPMap` reducing-restriction API. -/
def unboundedSinThetaDataOfReducingSubspace
    (A : E →ₗ.[𝕜] E)
    (_hAdense : Dense (A.domain : Set E)) (_hAclosed : A.IsClosed)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : F →ₗ.[𝕜] F)
    (_hA0dense : Dense (A0.domain : Set F)) (_hA0closed : A0.IsClosed)
    (X Rop : F →L[𝕜] E)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := Uᗮ) where
  A := A
  A₀ := A0
  Λ₁ := TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal
  X := X
  F₁ := Uᗮ.subtypeL
  residual := Rop
  X_maps_domain := hXdom
  F₁_maps_domain := fun y => y.property
  residual_eq := hReq
  intertwines := fun _ => rfl

/-- Scalar-generic natural isometric problem over a reducing exact subspace. -/
structure NaturalReducingIsometricSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] where
  /-- The ambient densely defined self-adjoint operator reduced by the selected subspace. -/
  A : E →ₗ.[𝕜] E
  A_dense : Dense (A.domain : Set E)
  A_closed : A.IsClosed
  ambient_selfAdjoint : _root_.IsSelfAdjoint A
  reduces : TauCeti.LinearPMap.ReducesSubspace A U
  /-- The densely defined self-adjoint trial operator. -/
  A₀ : F →ₗ.[𝕜] F
  A₀_dense : Dense (A₀.domain : Set F)
  A₀_closed : A₀.IsClosed
  trial_selfAdjoint : _root_.IsSelfAdjoint A₀
  /-- The isometric trial map, carrying the trial domain into the ambient domain. -/
  X : F →L[𝕜] E
  /-- The bounded extension of the residual obtained by comparing the ambient and trial
  operators. -/
  residual : F →L[𝕜] E
  trial_isometry : IsometricEmbedding X
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A ⟨X (x : F), X_maps_domain x⟩ - X (A₀ x) = residual (x : F)
  /-- The positive form gap between the trial operator and the complementary restriction. -/
  gap : ℝ
  gap_pos : 0 < gap
  spectral_gap : FormBoundedSylvesterGap A₀
    (TauCeti.LinearPMap.reducingRestriction A Uᗮ reduces.orthogonal) gap
  residual_mem : N.Mem residual

namespace NaturalReducingIsometricSinThetaProblem

/-- Canonical internal data of a natural reducing-subspace problem. -/
noncomputable def toData
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (P : NaturalReducingIsometricSinThetaProblem
      (𝕜 := 𝕜) (E := E) (F := F) N U) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := Uᗮ) :=
  unboundedSinThetaDataOfReducingSubspace
    P.A P.A_dense P.A_closed U P.reduces P.A₀ P.A₀_dense P.A₀_closed
    P.X P.residual P.X_maps_domain P.residual_eq

end NaturalReducingIsometricSinThetaProblem

/-- Scalar-generic natural lower-frame problem over a reducing exact
subspace. -/
structure NaturalReducingGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] where
  /-- The ambient densely defined self-adjoint operator reduced by the selected subspace. -/
  A : E →ₗ.[𝕜] E
  A_dense : Dense (A.domain : Set E)
  A_closed : A.IsClosed
  ambient_selfAdjoint : _root_.IsSelfAdjoint A
  reduces : TauCeti.LinearPMap.ReducesSubspace A U
  /-- The densely defined self-adjoint trial operator. -/
  A₀ : F →ₗ.[𝕜] F
  A₀_dense : Dense (A₀.domain : Set F)
  A₀_closed : A₀.IsClosed
  trial_selfAdjoint : _root_.IsSelfAdjoint A₀
  /-- The trial map with a positive lower frame bound, preserving the operator domains. -/
  X : F →L[𝕜] E
  /-- The bounded extension of the residual obtained by comparing the ambient and trial
  operators. -/
  residual : F →L[𝕜] E
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A ⟨X (x : F), X_maps_domain x⟩ - X (A₀ x) = residual (x : F)
  /-- The positive form gap between the trial operator and the complementary restriction. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap A₀
    (TauCeti.LinearPMap.reducingRestriction A Uᗮ reduces.orthogonal) gap
  residual_mem : N.Mem residual

namespace NaturalReducingGeneralSinThetaProblem

/-- Canonical internal data of a natural reducing lower-frame problem. -/
noncomputable def toData
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := 𝕜) (E := E) (F := F) N U) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := Uᗮ) :=
  unboundedSinThetaDataOfReducingSubspace
    P.A P.A_dense P.A_closed U P.reduces P.A₀ P.A₀_dense P.A₀_closed
    P.X P.residual P.X_maps_domain P.residual_eq

end NaturalReducingGeneralSinThetaProblem

section Complex

variable {EC FC : Type v}
  [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [CompleteSpace EC]
  [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [CompleteSpace FC]

namespace NaturalReducingIsometricSinThetaProblem

/-- Complex result for the scalar-generic natural reducing problem. -/
theorem result_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {U : Submodule ℂ EC} [U.HasOrthogonalProjection]
    (P : NaturalReducingIsometricSinThetaProblem
      (𝕜 := ℂ) (E := EC) (F := FC) N U) :
    N.Mem
        ((ContinuousLinearMap.id ℂ EC - U.subtypeL ∘L U.subtypeL.adjoint) ∘L P.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℂ EC - U.subtypeL ∘L U.subtypeL.adjoint) ∘L P.X)
        ≤ N.gauge P.residual := by
  let D := P.toData N
  have hcomp : _root_.IsSelfAdjoint D.Λ₁ :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint
      P.A Uᗮ P.reduces.orthogonal P.A_dense P.ambient_selfAdjoint
  have hdecomp : OrthogonalExactDecomposition U.subtypeL D.F₁ := by
    simpa only [D, NaturalReducingIsometricSinThetaProblem.toData,
      unboundedSinThetaDataOfReducingSubspace] using
      reducingSubspace_orthogonalExactDecomposition (𝕜 := ℂ) U
  have hmain := sinTheta_unbounded_exact_complex
    N D U.subtypeL P.ambient_selfAdjoint P.trial_selfAdjoint hcomp
      P.trial_isometry hdecomp P.gap_pos P.spectral_gap P.residual_mem
  simpa only [D, NaturalReducingIsometricSinThetaProblem.toData,
    unboundedSinThetaDataOfReducingSubspace,
    ] using hmain

end NaturalReducingIsometricSinThetaProblem

namespace NaturalReducingGeneralSinThetaProblem

/-- Complex lower-frame result for the scalar-generic natural problem. -/
theorem result_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {U : Submodule ℂ EC} [U.HasOrthogonalProjection]
    (P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := ℂ) (E := EC) (F := FC) N U) :
    N.Mem
        (directedSinThetaOperator P.X U.subtypeL
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.X U.subtypeL
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.residual := by
  let D := P.toData N
  have hcomp : _root_.IsSelfAdjoint D.Λ₁ :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint
      P.A Uᗮ P.reduces.orthogonal P.A_dense P.ambient_selfAdjoint
  have hdecomp : OrthogonalExactDecomposition U.subtypeL D.F₁ := by
    simpa only [D, NaturalReducingGeneralSinThetaProblem.toData,
      unboundedSinThetaDataOfReducingSubspace] using
      reducingSubspace_orthogonalExactDecomposition (𝕜 := ℂ) U
  have hmain := generalizedSinTheta_unbounded_exact_complex
    N D U.subtypeL P.ambient_selfAdjoint P.trial_selfAdjoint hcomp
      hdecomp P.gap_pos P.frameLowerBound_pos P.lowerFrame
      P.spectral_gap P.residual_mem
  simpa only [D, NaturalReducingGeneralSinThetaProblem.toData,
    unboundedSinThetaDataOfReducingSubspace,
    ] using hmain

end NaturalReducingGeneralSinThetaProblem

/-- Complex natural reducing-subspace sine-theta theorem without a problem
record at the call site. -/
theorem sinTheta_unbounded_complex_reducingSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : EC →ₗ.[ℂ] EC)
    (hAdense : Dense (A.domain : Set EC)) (hAclosed : A.IsClosed)
    (hA : _root_.IsSelfAdjoint A)
    (U : Submodule ℂ EC) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : FC →ₗ.[ℂ] FC)
    (hA0dense : Dense (A0.domain : Set FC)) (hA0closed : A0.IsClosed)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : FC →L[ℂ] EC) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : FC) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : FC), hXdom x⟩ - X (A0 x) = Rop (x : FC))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hR : N.Mem Rop) :
    N.Mem
        ((ContinuousLinearMap.id ℂ EC - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X) ∧
      δ * N.gauge
          ((ContinuousLinearMap.id ℂ EC - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X)
        ≤ N.gauge Rop := by
  let P : NaturalReducingIsometricSinThetaProblem
      (𝕜 := ℂ) (E := EC) (F := FC) N U :=
    { A := A
      A_dense := hAdense
      A_closed := hAclosed
      ambient_selfAdjoint := hA
      reduces := hred
      A₀ := A0
      A₀_dense := hA0dense
      A₀_closed := hA0closed
      trial_selfAdjoint := hA0
      X := X
      residual := Rop
      trial_isometry := hX
      X_maps_domain := hXdom
      residual_eq := hReq
      gap := δ
      gap_pos := hδ
      spectral_gap := hgap
      residual_mem := hR }
  exact P.result_complex N

/-- Complex natural lower-frame theorem over a supplied reducing subspace. -/
theorem generalizedSinTheta_unbounded_complex_reducingSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : EC →ₗ.[ℂ] EC)
    (hAdense : Dense (A.domain : Set EC)) (hAclosed : A.IsClosed)
    (hA : _root_.IsSelfAdjoint A)
    (U : Submodule ℂ EC) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : FC →ₗ.[ℂ] FC)
    (hA0dense : Dense (A0.domain : Set FC)) (hA0closed : A0.IsClosed)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : FC →L[ℂ] EC)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : FC) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : FC), hXdom x⟩ - X (A0 x) = Rop (x : FC))
    (hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hR : N.Mem Rop) :
    N.Mem
        (directedSinThetaOperator X U.subtypeL hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperator X U.subtypeL hframe hε)
        ≤ N.gauge Rop := by
  let P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := ℂ) (E := EC) (F := FC) N U :=
    { A := A
      A_dense := hAdense
      A_closed := hAclosed
      ambient_selfAdjoint := hA
      reduces := hred
      A₀ := A0
      A₀_dense := hA0dense
      A₀_closed := hA0closed
      trial_selfAdjoint := hA0
      X := X
      residual := Rop
      X_maps_domain := hXdom
      residual_eq := hReq
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_gap := hgap
      residual_mem := hR }
  exact P.result_complex N

end Complex

section Real

variable {ER FR : Type v}
  [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
  [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]

namespace NaturalReducingIsometricSinThetaProblem

/-- Real result for the scalar-generic natural reducing problem. -/
theorem result_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    {U : Submodule ℝ ER} [U.HasOrthogonalProjection]
    (P : NaturalReducingIsometricSinThetaProblem
      (𝕜 := ℝ) (E := ER) (F := FR) N U) :
    N.Mem
        ((ContinuousLinearMap.id ℝ ER - U.subtypeL ∘L U.subtypeL.adjoint) ∘L P.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℝ ER - U.subtypeL ∘L U.subtypeL.adjoint) ∘L P.X)
        ≤ N.gauge P.residual := by
  let D := P.toData N
  have hcomp : _root_.IsSelfAdjoint D.Λ₁ :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint
      P.A Uᗮ P.reduces.orthogonal P.A_dense P.ambient_selfAdjoint
  have hdecomp : OrthogonalExactDecomposition U.subtypeL D.F₁ := by
    simpa only [D, NaturalReducingIsometricSinThetaProblem.toData,
      unboundedSinThetaDataOfReducingSubspace] using
      reducingSubspace_orthogonalExactDecomposition (𝕜 := ℝ) U
  -- The real engines have no raw twin yet, so the conversion to the
  -- bundled representation is made explicit here rather than hidden in the record.
  have hmain := sinTheta_unbounded_exact_real
    N D U.subtypeL P.ambient_selfAdjoint P.trial_selfAdjoint hcomp
      P.trial_isometry hdecomp P.gap_pos P.spectral_gap P.residual_mem
  simpa only [D, NaturalReducingIsometricSinThetaProblem.toData,
    unboundedSinThetaDataOfReducingSubspace,
    ] using hmain

end NaturalReducingIsometricSinThetaProblem

namespace NaturalReducingGeneralSinThetaProblem

/-- Real lower-frame result for the scalar-generic natural problem. -/
theorem result_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    {U : Submodule ℝ ER} [U.HasOrthogonalProjection]
    (P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := ℝ) (E := ER) (F := FR) N U) :
    N.Mem
        (directedSinThetaOperatorReal P.X U.subtypeL
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperatorReal P.X U.subtypeL
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.residual := by
  let D := P.toData N
  have hcomp : _root_.IsSelfAdjoint D.Λ₁ :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint
      P.A Uᗮ P.reduces.orthogonal P.A_dense P.ambient_selfAdjoint
  have hdecomp : OrthogonalExactDecomposition U.subtypeL D.F₁ := by
    simpa only [D, NaturalReducingGeneralSinThetaProblem.toData,
      unboundedSinThetaDataOfReducingSubspace] using
      reducingSubspace_orthogonalExactDecomposition (𝕜 := ℝ) U
  -- As in the isometric real method: explicit conversion, no raw twin yet.
  have hmain := generalizedSinTheta_unbounded_exact_real
    N D U.subtypeL P.ambient_selfAdjoint P.trial_selfAdjoint hcomp
      hdecomp P.gap_pos P.frameLowerBound_pos P.lowerFrame
      P.spectral_gap P.residual_mem
  simpa only [D, NaturalReducingGeneralSinThetaProblem.toData,
    unboundedSinThetaDataOfReducingSubspace,
    ] using hmain

end NaturalReducingGeneralSinThetaProblem

/-- Real natural reducing-subspace sine-theta theorem without a problem record
at the call site. -/
theorem sinTheta_unbounded_real_reducingSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : ER →ₗ.[ℝ] ER)
    (hAdense : Dense (A.domain : Set ER)) (hAclosed : A.IsClosed)
    (hA : _root_.IsSelfAdjoint A)
    (U : Submodule ℝ ER) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : FR →ₗ.[ℝ] FR)
    (hA0dense : Dense (A0.domain : Set FR)) (hA0closed : A0.IsClosed)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : FR →L[ℝ] ER) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : FR) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : FR), hXdom x⟩ - X (A0 x) = Rop (x : FR))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hR : N.Mem Rop) :
    N.Mem
        ((ContinuousLinearMap.id ℝ ER - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X) ∧
      δ * N.gauge
          ((ContinuousLinearMap.id ℝ ER - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X)
        ≤ N.gauge Rop := by
  let P : NaturalReducingIsometricSinThetaProblem
      (𝕜 := ℝ) (E := ER) (F := FR) N U :=
    { A := A
      A_dense := hAdense
      A_closed := hAclosed
      ambient_selfAdjoint := hA
      reduces := hred
      A₀ := A0
      A₀_dense := hA0dense
      A₀_closed := hA0closed
      trial_selfAdjoint := hA0
      X := X
      residual := Rop
      trial_isometry := hX
      X_maps_domain := hXdom
      residual_eq := hReq
      gap := δ
      gap_pos := hδ
      spectral_gap := hgap
      residual_mem := hR }
  exact P.result_real N

/-- Real natural lower-frame theorem over a supplied reducing subspace. -/
theorem generalizedSinTheta_unbounded_real_reducingSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : ER →ₗ.[ℝ] ER)
    (hAdense : Dense (A.domain : Set ER)) (hAclosed : A.IsClosed)
    (hA : _root_.IsSelfAdjoint A)
    (U : Submodule ℝ ER) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (A0 : FR →ₗ.[ℝ] FR)
    (hA0dense : Dense (A0.domain : Set FR)) (hA0closed : A0.IsClosed)
    (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : FR →L[ℝ] ER)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hXdom : ∀ x : A0.domain, X (x : FR) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : FR), hXdom x⟩ - X (A0 x) = Rop (x : FR))
    (hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hR : N.Mem Rop) :
    N.Mem
        (directedSinThetaOperatorReal X U.subtypeL hframe hε) ∧
      δ * ε * N.gauge
          (directedSinThetaOperatorReal X U.subtypeL hframe hε)
        ≤ N.gauge Rop := by
  let P : NaturalReducingGeneralSinThetaProblem
      (𝕜 := ℝ) (E := ER) (F := FR) N U :=
    { A := A
      A_dense := hAdense
      A_closed := hAclosed
      ambient_selfAdjoint := hA
      reduces := hred
      A₀ := A0
      A₀_dense := hA0dense
      A₀_closed := hA0closed
      trial_selfAdjoint := hA0
      X := X
      residual := Rop
      X_maps_domain := hXdom
      residual_eq := hReq
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_gap := hgap
      residual_mem := hR }
  exact P.result_real N

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
