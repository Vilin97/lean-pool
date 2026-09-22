/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

/-
Source-scope review (2026-09-09): the bounded-trial declarations in this module
remain valid specializations, not full coverage of the unbounded trial scope.
Their `hVdom`/`hPdom` hypotheses put every trial vector in the exact operator's
domain, and their trial operator `M` is bounded. The common-dense-domain setup
of the source does not require either restriction. In the final conjunction,
these shared hypotheses also restrict the ambient clause unnecessarily; use
`SinTwoThetaAmbientUnbounded` for its independent ambient estimate.
`SinTwoThetaCommonDomain` contains a replacement candidate pending compiler
validation. It is not imported here or certified by the result inventory.
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.TrialReflection
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ReflectedDefectDoubling
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleGeneric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Sin Two Theta Directed RCLike -/

open TauCeti.DavisKahan.Sylvester

/-!
# Scalar-generic directed `sin 2Θ₀` residual theorem

This module removes the last real/complex split from the Davis--Kahan Section 2
`sin 2Θ` theorem.  The fixed-field proofs had already converged to the same
architecture.  Their only substantive fork was the single-angle block estimate;
`SineTheta/ScalarGeneric.lean` now supplies that block estimate over every
`RCLike` field.

The canonical endpoint here is stated at an arbitrary reducing subspace.  That
matches the source setup more closely than the spectral-selection wrappers: the
source assumes that the exact decomposition reduces the operator, while a
spectral projector is only one way to obtain such a decomposition.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
  {M : V →L[𝕜] V} {R : V →L[𝕜] H}
  {A : H →ₗ.[𝕜] H}

/-- Scalar-generic reflection-residual block estimate at an arbitrary reducing
subspace.  This is the common engine formerly duplicated in the complex and real
unbounded double-angle files. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_reducing_rclike
    (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (D : H →L[𝕜] H) (hD : D.IsSymmetric)
    (W : Submodule 𝕜 H) [W.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hJdom : ∀ x : A.domain, W.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A D)
          ⟨W.reflectionOperator (x : H), hJdom x⟩ =
        W.reflectionOperator (A x))
    (hDmem : N.Mem D) :
    N.Mem (sinTwoThetaIdealBlock U W) ∧
      δ * N.gauge (sinTwoThetaIdealBlock U W) ≤
        N.gauge (U.starProjection ∘L D ∘L
          (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) := by
  set Uc := (Uᗮ : Submodule 𝕜 H) with hUc
  set A₀ := TauCeti.LinearPMap.reducingRestriction A U hred with hA₀def
  set Λ := TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal with hΛdef
  set J : H →L[𝕜] H := W.reflectionOperator with hJ
  set X : U →L[𝕜] H := U.subtypeL with hX
  set F₁ : Uc →L[𝕜] H := J ∘L Uc.subtypeL with hF₁
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain := fun x =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp x.2
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) := fun x =>
    (TauCeti.LinearPMap.coe_reducingRestriction_apply A U hred (x : U)
      (hXdom x)).symm
  have hUcdom : ∀ y : Λ.domain, ((y : Uc) : H) ∈ A.domain := fun y =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A Uᗮ hred.orthogonal
      _).mp y.2
  have hF₁dom : ∀ y : Λ.domain, F₁ (y : Uc) ∈ A.domain := fun y =>
    hJdom ⟨((y : Uc) : H), hUcdom y⟩
  have hF₁int : ∀ y : Λ.domain,
      (TauCeti.LinearPMap.addBounded A D) ⟨F₁ (y : Uc), hF₁dom y⟩ =
        F₁ (Λ y) := by
    intro y
    have hAy : A ⟨((y : Uc) : H), hUcdom y⟩ = ((Λ y : Uc) : H) :=
      (TauCeti.LinearPMap.coe_reducingRestriction_apply A Uᗮ hred.orthogonal
        (y : Uc) (hUcdom y)).symm
    calc
      (TauCeti.LinearPMap.addBounded A D) ⟨F₁ (y : Uc), hF₁dom y⟩
          = J (A ⟨((y : Uc) : H), hUcdom y⟩) :=
            hJintertwines ⟨((y : Uc) : H), hUcdom y⟩
      _ = J ((Λ y : Uc) : H) := congrArg J hAy
      _ = F₁ (Λ y) := rfl
  have hF₁iso : IsometricEmbedding F₁ :=
    isometricEmbedding_reflection_comp W (fun _ => rfl)
  have hraw := sinTheta_addBounded_gauge_block_of_formGap_rclike
    N A hA D hD
    A₀ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred
      hA.dense_domain hA)
    Λ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A Uᗮ hred.orthogonal
      hA.dense_domain hA)
    X F₁ hXdom hXint hF₁dom hF₁int hF₁iso hδ hgap hDmem
  have hFproj : F₁ ∘L F₁.adjoint =
      (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection := by
    rw [starProjection_map_unitary Uᗮ W.reflection]
    refine ContinuousLinearMap.ext fun x => ?_
    have hUcU : Uc.subtypeL ∘L Uc.subtypeL.adjoint = Uc.starProjection := by
      refine ContinuousLinearMap.ext fun z => ?_
      rw [Submodule.adjoint_subtypeL]
      rfl
    have hadj : F₁.adjoint = Uc.subtypeL.adjoint ∘L J := by
      rw [hF₁, ContinuousLinearMap.adjoint_comp, hJ, adjoint_reflectionOperator W]
    have hsymm : W.reflection.symm = W.reflection := W.reflection_symm
    change J (Uc.subtypeL (F₁.adjoint x)) = _
    rw [hadj]
    change J (Uc.subtypeL (Uc.subtypeL.adjoint (J x))) = _
    rw [show Uc.subtypeL (Uc.subtypeL.adjoint (J x)) =
        (Uc.subtypeL ∘L Uc.subtypeL.adjoint) (J x) from rfl, hUcU]
    change J (Uc.starProjection (J x)) =
      W.reflection (Uc.starProjection (W.reflection.symm x))
    rw [hsymm]
    rfl
  have hambient := projectionProduct_mem_and_gauge_le_isometric
    N.toSymmetricOperatorIdealFamily U
    (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)) F₁ hF₁iso hFproj hraw.1
  have hF₁adjF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id 𝕜 Uc := by
    have hUcadj : Uc.subtypeL.adjoint ∘L Uc.subtypeL = ContinuousLinearMap.id 𝕜 Uc := by
      ext z
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
      exact congrArg (fun q : Uc => (q : H))
        (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z)
    have hJJ : (J ∘L J : H →L[𝕜] H) = ContinuousLinearMap.id 𝕜 H :=
      Submodule.reflectionOperator_involutive W
    calc F₁.adjoint ∘L F₁
        = (Uc.subtypeL.adjoint ∘L J.adjoint) ∘L (J ∘L Uc.subtypeL) := by
          rw [hF₁, ContinuousLinearMap.adjoint_comp]
      _ = Uc.subtypeL.adjoint ∘L (J ∘L J) ∘L Uc.subtypeL := by
          rw [hJ, adjoint_reflectionOperator W]
          rfl
      _ = Uc.subtypeL.adjoint ∘L Uc.subtypeL := by
          rw [hJJ, ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id 𝕜 Uc := hUcadj
  have hPF : (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection ∘L F₁ =
      F₁ := by
    rw [← hFproj, ContinuousLinearMap.comp_assoc, hF₁adjF₁,
      ContinuousLinearMap.comp_id]
  have hPX : X.adjoint ∘L U.starProjection = X.adjoint := by
    rw [hX]
    ext x
    rw [ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL,
      Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hDadj : D.adjoint = D :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hD
  have hfac : (D ∘L X).adjoint ∘L F₁ =
      X.adjoint ∘L (U.starProjection ∘L D ∘L
        (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) ∘L F₁ := by
    rw [ContinuousLinearMap.adjoint_comp, hDadj]
    calc X.adjoint ∘L D ∘L F₁
        = (X.adjoint ∘L U.starProjection) ∘L D ∘L
            ((Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection ∘L
              F₁) := by rw [hPX, hPF]
      _ = X.adjoint ∘L (U.starProjection ∘L D ∘L
            (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) ∘L
            F₁ := rfl
  have hMid : N.Mem (U.starProjection ∘L D ∘L
      (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) :=
    N.toSymmetricOperatorIdealFamily.comp_mem U.starProjection
      (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection hDmem
  have hcontract : N.gauge ((D ∘L X).adjoint ∘L F₁) ≤
      N.gauge (U.starProjection ∘L D ∘L
        (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) := by
    rw [hfac]
    have hXadjNorm : ‖X.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hF₁norm : ‖F₁‖ ≤ 1 := opNorm_le_one_of_isometry hF₁iso
    exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_le_of_contractions
      X.adjoint F₁ hMid hXadjNorm hF₁norm
  refine ⟨hambient.1, ?_⟩
  calc
    δ * N.gauge (sinTwoThetaIdealBlock U W)
        ≤ δ * N.gauge (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hambient.2 hδ.le
    _ ≤ N.gauge ((D ∘L X).adjoint ∘L F₁) := hraw.2
    _ ≤ N.gauge (U.starProjection ∘L D ∘L
        (Uᗮ.map (W.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) := hcontract

/-- Scalar-generic Ky Fan estimate for the printed directed `sin 2Θ₀` residual clause,
at an arbitrary reducing subspace. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_kyFan_rclike
    (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ) :
    ∀ k : ℕ,
      δ * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V) ≤
        2 * kyFanApproximationGauge k R := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hSsa : IsSelfAdjoint (trialOffDiagonalPart V M R) :=
    isSelfAdjoint_trialOffDiagonalPart
  have hDsa' : IsSelfAdjoint ((-2 : 𝕜) • trialOffDiagonalPart V M R) := by
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hDsa : ((-2 : 𝕜) • trialOffDiagonalPart V M R).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDsa'
  have hraw := sinTwoTheta_reflectionResidual_block_gauge_reducing_rclike
    hA hred (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk)
    ((-2 : 𝕜) • trialOffDiagonalPart V M R) hDsa V hδ hgap
    (reflectionOperator_mem_domain hVdom)
    (trialReflection_intertwines hA hVdom hres)
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk _)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge] at hraw
  have hflip : kyFanApproximationGauge k
        (U.starProjection ∘L
          ((-2 : 𝕜) • trialOffDiagonalPart V M R) ∘L
          (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) =
      kyFanApproximationGauge k
        ((Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection ∘L
          ((-2 : 𝕜) • trialOffDiagonalPart V M R) ∘L U.starProjection) := by
    rw [← kyFanApproximationGauge_adjoint]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hDsa']
    rfl
  have hdouble := kyFan_reflectionDefectBlock_le_two_mul hSsa U V k
  rw [reflectionDefect_trialOffDiagonalPart, trialOffDiagonalPart_upper] at hdouble
  have hblockR : kyFanApproximationGauge k (trialOffDiagonalBlock V M R) ≤
      kyFanApproximationGauge k R := by
    rw [trialOffDiagonalBlock_eq]
    refine (kyFanApproximationGauge_comp_le k Vᗮ.starProjection R
      V.subtypeL.adjoint).trans ?_
    have hQ : ‖(Vᗮ.starProjection : H →L[𝕜] H)‖ ≤ 1 :=
      Submodule.starProjection_norm_le _
    have hI : ‖(V.subtypeL.adjoint : H →L[𝕜] V)‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hnn : 0 ≤ kyFanApproximationGauge k R := kyFanApproximationGauge_nonneg k R
    calc
      ‖(Vᗮ.starProjection : H →L[𝕜] H)‖ * kyFanApproximationGauge k R *
            ‖(V.subtypeL.adjoint : H →L[𝕜] V)‖
          ≤ 1 * kyFanApproximationGauge k R * 1 := by gcongr
      _ = kyFanApproximationGauge k R := by ring
  calc
    δ * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V)
        ≤ kyFanApproximationGauge k
          (U.starProjection ∘L
            ((-2 : 𝕜) • trialOffDiagonalPart V M R) ∘L
            (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection) := hraw.2
    _ = kyFanApproximationGauge k
          ((Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection ∘L
            ((-2 : 𝕜) • trialOffDiagonalPart V M R) ∘L U.starProjection) := hflip
    _ ≤ 2 * kyFanApproximationGauge k (trialOffDiagonalBlock V M R) := hdouble
    _ ≤ 2 * kyFanApproximationGauge k R := by gcongr

/-- Scalar-generic symmetric-norming engine for the directed `sin 2Θ₀` residual clause,
in the proof's block representation. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock U V) ≤ 2 * N.gauge R := by
  let R0 : H →L[𝕜] H := R ∘L V.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R :=
    sameApproximationSingularValues_extendDomainByZero V R
  have htransport := hsameR.normingMem_iff_and_gauge_eq N
  have hMem0 : N.Mem R0 := htransport.1.mpr hRmem
  have hgauge : N.gauge R0 = N.gauge R := htransport.2
  have htwo : ‖(2 : 𝕜)‖ = 2 := by simp
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V) ≤
        kyFanApproximationGauge k ((2 : 𝕜) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo, hsameR.kyFanApproximationGauge_eq k]
    exact sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_kyFan_rclike
      hA hred hVdom hres hδ hgap k
  have hMem2 : N.Mem ((2 : 𝕜) • R0) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem0 h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hδ hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hMem0, htwo, hgauge] at hle
  exact hle

/-- Scalar-generic directed `sin 2Θ₀` residual theorem on the paper's own trial-side angle,
at an arbitrary reducing subspace. -/
theorem sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hRmem : N.Mem R) :
    N.Mem (Angle.directedSinTwoAngleOperator V U) ∧
      δ * N.gauge (Angle.directedSinTwoAngleOperator V U) ≤ 2 * N.gauge R := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_rclike
      N hA hred hVdom hres hδ hgap hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

/-- Davis--Kahan Section 2 directed `sin 2Θ₀` residual clause at the where-defined
unitarily invariant norm boundary, scalar-generic over `RCLike`.

The exact subspace is required only to reduce the (possibly unbounded) self-adjoint
operator.  The inequality is asserted when both displayed norms are defined; no
ideal-membership transfer is added to the source statement. -/
theorem sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
    
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ) :
    N.Mem (Angle.directedSinTwoAngleOperator V U) →
    N.Mem R →
      δ * N.gaugeReal (Angle.directedSinTwoAngleOperator V U) ≤ 2 * N.gaugeReal R := by
  intro hAngle hR
  have hhalf : N.ScaledGaugeLEWhereDefined (δ / 2)
      (Angle.directedSinTwoAngleOperator V U) R := by
    apply N.scaledGaugeLEWhereDefined_of_all_mul_kyFan_le
      (div_pos hδ (by norm_num : (0 : ℝ) < 2))
    intro k
    by_cases hk0 : k = 0
    · subst k
      simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge_zero_index]
    · have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hmain :=
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
          (kyFanNormingFunction k hk) hA hred hVdom hres hδ hgap
          (kyFanNormingFunction_mem k hk R)
      have hky :
          δ * kyFanApproximationGauge k (Angle.directedSinTwoAngleOperator V U) ≤
            2 * kyFanApproximationGauge k R := by
        simpa only [kyFanNormingFunction_gauge] using hmain.2
      nlinarith
  have hle := hhalf hAngle hR
  nlinarith


/-- Combined bounded-trial specialization of the double-angle inequalities.

The shared `hPdom` and bounded `M` assumptions restrict both conclusions. This
is retained for compatibility, not as full source-scope certification. The
separate ambient theorem needs no such trial data. See the common-domain
replacement candidate and the 2026-09-09 source review. -/
theorem sinTwoTheta_unbounded_perturbedGap_whereDefinedUIN_rclike
    
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    (Hop : H →L[𝕜] H) (hHop : Hop.IsSymmetric)
    {P Q : Submodule 𝕜 H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {M : P →L[𝕜] P} {R : P →L[𝕜] H}
    (hPdom : ∀ p : P, (p : H) ∈ (TauCeti.LinearPMap.addBounded A Hop).domain)
    (hres : ∀ p : P,
      (TauCeti.LinearPMap.addBounded A Hop) ⟨(p : H), hPdom p⟩ =
        R p + ((M p : P) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    (N.Mem (Angle.directedSinTwoAngleOperator P Q) →
      N.Mem R →
        δ * N.gaugeReal (Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal R) ∧
    (N.Mem (Angle.sinTwoAngleOperator P Q) →
      N.Mem Hop →
        δ * N.gaugeReal (Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) := by
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    addBounded_isSelfAdjoint A hA Hop hHop
  refine ⟨?_, ?_⟩
  · exact sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
      N hAH hQred hPdom hres hδ hgap
  · exact sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
      N hA Hop hHop hPred hQred hδ hgap

end

end DavisKahan1970
end TauCeti
