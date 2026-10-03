/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Bounded
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.Reducing
public import LeanPool.DavisKahan.DavisKahan.SinTheta.Natural.GapConvenience
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-! # Examples -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Compile-only usage examples for the natural sine-theta API

These examples are regression tests for theorem usability. They instantiate the
ordinary operator-norm ideal family, exercise both scalar fields, and include a
finite-dimensional zero-residual model whose exact subspace is the whole
ambient space. The latter has an empty complementary block, hence an ordered
positive gap for every positive separation.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace NaturalExamples


noncomputable section

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan

universe v

section AbstractComplexUse


variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

example
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℂ] F) (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℂ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X‖ ≤
      ‖Rop‖ := by
  have hmain := sinTheta_unbounded_spectralSubspace_of_spectrumGap
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℂ))
      A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap (by
        rw [FanDominantIdealFamily.mem_iff]
        simp [KyFanDominantIdealFamily.operatorNorm])
  exact hmain.2

/-- The same natural theorem instantiated with the nontrivial two-term Ky Fan
gauge rather than the operator norm. -/
example
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℂ] F) (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℂ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * kyFanApproximationGauge 2
        ((ContinuousLinearMap.id ℂ E -
          selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
            (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X)
      ≤ kyFanApproximationGauge 2 Rop := by
  have hk : 0 < (2 : ℕ) := by omega
  let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 2 hk
  have hmain := sinTheta_unbounded_spectralSubspace_of_spectrumGap
    N A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) 2 hk Rop)
  simpa only [N, KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

end AbstractComplexUse

section AbstractRealUse

open RealSpectralRestriction

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

example
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →ₗ.[ℝ] F) (hA0 : _root_.IsSelfAdjoint A0)
    (X Rop : F →L[ℝ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A ⟨X (x : F), hXdom x⟩ - X (A0 x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A0
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (realSelfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X‖ ≤
      ‖Rop‖ := by
  have hmain := sinTheta_unbounded_real_spectralSubspace
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ))
      A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap (by
        rw [FanDominantIdealFamily.mem_iff]
        simp [KyFanDominantIdealFamily.operatorNorm])
  exact hmain.2

end AbstractRealUse

section AbstractBoundedUse


variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The bounded convenience theorem removes every domain-side argument. -/
example
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectralSylvesterGap
      ((A0.toLinearMap.toPMap ⊤))
      (selfAdjointSpectralRestriction ((A.toLinearMap.toPMap ⊤))
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)) Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)) S hS ∘L
        (selfAdjointSpectralSubspaceInclusion ((A.toLinearMap.toPMap ⊤))
          (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := A)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)) S hS).adjoint) ∘L X‖
      ≤ ‖generalResidual A X A0‖ := by
  have hmain := sinTheta_bounded_spectralSubspace_of_spectrumGap
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℂ))
      A hA S hS A0 hA0 X hX hδ hgap (by
        rw [FanDominantIdealFamily.mem_iff]
        simp [KyFanDominantIdealFamily.operatorNorm])
  exact hmain.2

end AbstractBoundedUse

section FiniteRealModel

/-- The real Euclidean plane, the concrete space these examples are stated over. -/
abbrev RealPlane := EuclideanSpace ℝ (Fin 2)

/-- A concrete finite-dimensional, zero-residual use of the natural reducing
API. The whole plane is the exact subspace and the complementary block is the
zero Hilbert space. -/
theorem realPlane_zeroResidual_model :
    let _A : RealPlane →ₗ.[ℝ] RealPlane :=
      ((0 : RealPlane →L[ℝ] RealPlane).toLinearMap.toPMap ⊤)
    let _A0 : RealPlane →ₗ.[ℝ] RealPlane :=
      ((0 : RealPlane →L[ℝ] RealPlane).toLinearMap.toPMap ⊤)
    let U : Submodule ℝ RealPlane := ⊤
    let X : RealPlane →L[ℝ] RealPlane := ContinuousLinearMap.id ℝ RealPlane
    let Rop : RealPlane →L[ℝ] RealPlane := 0
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).Mem
      ((ContinuousLinearMap.id ℝ RealPlane - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X) ∧
      1 * (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).gauge
        ((ContinuousLinearMap.id ℝ RealPlane - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X)
      ≤ (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).gauge Rop := by
  dsimp
  let A : RealPlane →ₗ.[ℝ] RealPlane :=
    ((0 : RealPlane →L[ℝ] RealPlane).toLinearMap.toPMap ⊤)
  let A0 : RealPlane →ₗ.[ℝ] RealPlane :=
    ((0 : RealPlane →L[ℝ] RealPlane).toLinearMap.toPMap ⊤)
  let U : Submodule ℝ RealPlane := ⊤
  have hred : TauCeti.LinearPMap.ReducesSubspace A U := by
    simp [A, U, TauCeti.LinearPMap.ReducesSubspace,
      TauCeti.LinearPMap.InvariantSubspace]
  have hA : IsSelfAdjoint A := by
    exact TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := (0 : RealPlane →L[ℝ] RealPlane))
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by intro x y; simp))
  have hA0 : _root_.IsSelfAdjoint A0 := by
    exact TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := (0 : RealPlane →L[ℝ] RealPlane))
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by intro x y; simp))
  have hA0upper : TauCeti.LinearPMap.SemiboundedAbove A0 0 := by
    intro x
    change RCLike.re
      ⟪(0 : RealPlane →L[ℝ] RealPlane) (x : RealPlane), (x : RealPlane)⟫_ℝ ≤ _
    simp
  have hcompLower : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) 1 := by
    intro x
    have hzero : ((x.1 : RealPlane)) = 0 :=
      inner_self_eq_zero.mp
        (Submodule.inner_right_of_mem_orthogonal (K := U) Submodule.mem_top x.1.2)
    have hx : x = 0 := Subtype.ext (Subtype.ext hzero)
    rw [hx]
    simp
  have hgap : FormBoundedSylvesterGap A0
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) 1 := by
    exact FormBoundedSylvesterGap.trialBelow_complementAbove hA0upper
      (by simpa using hcompLower)
  apply sinTheta_unbounded_real_reducingSubspace
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ))
      A hA.dense_domain hA.isClosed hA U hred
      A0 hA0.dense_domain hA0.isClosed hA0
      (ContinuousLinearMap.id ℝ RealPlane) 0 (fun _ => rfl)
  case hXdom => exact fun x => Submodule.mem_top
  case hReq =>
    intro x
    change (0 : RealPlane) - (0 : RealPlane) = (0 : RealPlane)
    simp
  case hδ => exact zero_lt_one
  case hgap => exact hgap
  case hR =>
    rw [FanDominantIdealFamily.mem_iff]
    simp

end FiniteRealModel

end

end NaturalExamples
end ExactSinTheta
end DavisKahan
end TauCeti
