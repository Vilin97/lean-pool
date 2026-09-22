/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.Unbounded
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbationIdeal
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Unbounded Ideal -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Ideal-gauge unbounded sine two theta

The rectangular ideal interface naturally controls the reflected
complementary overlap block.  Its operator norm is exactly the norm of the
complex sine-two-angle operator, while its ideal gauge remains meaningful for
families whose rectangular source and target spaces differ.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

universe u v

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The directed sine-two-theta ideal block `P_U P_{J_V Uᗮ}`: the overlap of `U`
with the `V`-reflection of `Uᗮ`.

This is the object the unbounded directed `sin 2Θ` estimates are proved about.  It
is a one-sided block, not an angle;
`Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_rclike` identifies its
singular-value sequence with that of `Angle.directedSinTwoAngleOperator U V`, and
`Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide` with that of the
other ordering `Angle.directedSinTwoAngleOperator V U`, which is the one Davis and
Kahan's `Θ₀` names when `U` carries the gap and `V` is the trial subspace. -/
noncomputable def sinTwoThetaIdealBlock
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  U.starProjection ∘L
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[𝕜] H)).starProjection

/-- A rectangular overlap block controls the corresponding ambient projection
product in every rectangular symmetric ideal family.

The right-hand coordinate space is presented by an arbitrary isometric
embedding `Y` whose associated projection is the one being overlapped, rather
than by the inclusion of a submodule.  That is what lets the reflected
complementary block be read either through `Uᗮ.map J_V` or through
`J_V ∘ Uᗮ.subtypeL`, which are the same operator but not the same coordinate
presentation. -/
theorem projectionProduct_mem_and_gauge_le_isometric
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    
    (U W : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    [CompleteSpace U]
    (Y : G →L[𝕜] H) (hYiso : IsometricEmbedding Y)
    (hYproj : Y ∘L Y.adjoint = W.starProjection)
    (hT : N.Mem (U.subtypeL.adjoint ∘L Y)) :
    N.Mem (U.starProjection ∘L W.starProjection) ∧
      N.gaugeReal (U.starProjection ∘L W.starProjection) ≤
        N.gaugeReal (U.subtypeL.adjoint ∘L Y) := by
  let T : G →L[𝕜] U := U.subtypeL.adjoint ∘L Y
  have hfactor :
      U.starProjection ∘L W.starProjection =
        U.subtypeL ∘L T ∘L Y.adjoint := by
    have hUU : U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection := by
      ext x
      rw [Submodule.adjoint_subtypeL]
      rfl
    calc
      U.starProjection ∘L W.starProjection
          = (U.subtypeL ∘L U.subtypeL.adjoint) ∘L (Y ∘L Y.adjoint) := by
            rw [hUU, hYproj]
      _ = U.subtypeL ∘L T ∘L Y.adjoint := rfl
  have hmemFactor : N.Mem (U.subtypeL ∘L T ∘L Y.adjoint) :=
    N.comp_mem U.subtypeL Y.adjoint hT
  have hUiso : IsometricEmbedding U.subtypeL := by
    intro x
    rfl
  have hUnorm : ‖U.subtypeL‖ ≤ 1 := opNorm_le_one_of_isometry hUiso
  have hYadjNorm : ‖Y.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact opNorm_le_one_of_isometry hYiso
  refine ⟨?_, ?_⟩
  · rw [hfactor]
    exact hmemFactor
  · rw [hfactor]
    have hgauge := N.gaugeReal_comp_le U.subtypeL Y.adjoint hT
    have hnonneg := N.gaugeReal_nonneg hT
    calc
      N.gaugeReal (U.subtypeL ∘L T ∘L Y.adjoint) ≤
          ‖U.subtypeL‖ * N.gaugeReal T * ‖Y.adjoint‖ := hgauge
      _ ≤ 1 * N.gaugeReal T * ‖Y.adjoint‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hUnorm hnonneg)
          (norm_nonneg Y.adjoint)
      _ ≤ 1 * N.gaugeReal T * 1 := by
        exact mul_le_mul_of_nonneg_left hYadjNorm
          (mul_nonneg zero_le_one hnonneg)
      _ = N.gaugeReal (U.subtypeL.adjoint ∘L Y) := by
        dsimp [T]
        ring

/-- A rectangular overlap block controls the corresponding ambient projection
product in every rectangular symmetric ideal family. -/
theorem projectionProduct_mem_and_gauge_le_overlap
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (U W : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace W]
    (hT : N.Mem (U.subtypeL.adjoint ∘L W.subtypeL)) :
    N.Mem (U.starProjection ∘L W.starProjection) ∧
      N.gaugeReal (U.starProjection ∘L W.starProjection) ≤
        N.gaugeReal (U.subtypeL.adjoint ∘L W.subtypeL) := by
  refine projectionProduct_mem_and_gauge_le_isometric N U W W.subtypeL
    (fun _ => rfl) ?_ hT
  ext x
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- The bounded reflection residual remains in every rectangular symmetric
ideal containing the perturbation, with gauge cost at most two. -/
theorem reflectionPerturbation_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (E : H →L[𝕜] H) (hEmem : N.Mem E) :
    N.Mem (reflectionPerturbation V E) ∧
      N.gaugeReal (reflectionPerturbation V E) ≤ 2 * N.gaugeReal E := by
  let W : H →L[𝕜] H :=
    V.reflection.toLinearIsometry.toContinuousLinearMap
  let W' : H →L[𝕜] H :=
    V.reflection.symm.toLinearIsometry.toContinuousLinearMap
  have hWiso : IsometricEmbedding W := by
    intro x
    exact V.reflection.norm_map x
  have hW'iso : IsometricEmbedding W' := by
    intro x
    exact V.reflection.symm.norm_map x
  have hconjMem : N.Mem (boundedUnitaryConjugate V.reflection E) := by
    change N.Mem (W ∘L E ∘L W')
    exact N.comp_mem W W' hEmem
  have hconjGauge :
      N.gaugeReal (boundedUnitaryConjugate V.reflection E) ≤ N.gaugeReal E := by
    change N.gaugeReal (W ∘L E ∘L W') ≤ N.gaugeReal E
    exact N.gaugeReal_comp_le_of_contractions W W' hEmem
      (opNorm_le_one_of_isometry hWiso)
      (opNorm_le_one_of_isometry hW'iso)
  refine ⟨?_, ?_⟩
  · unfold reflectionPerturbation
    exact N.sub_mem hEmem hconjMem
  · unfold reflectionPerturbation
    have hsub := N.gaugeReal_sub_le hEmem hconjMem
    calc
      N.gaugeReal (E - boundedUnitaryConjugate V.reflection E) ≤
          N.gaugeReal E + N.gaugeReal (boundedUnitaryConjugate V.reflection E) := hsub
      _ ≤ N.gaugeReal E + N.gaugeReal E :=
        add_le_add le_rfl hconjGauge
      _ = 2 * N.gaugeReal E := by ring

omit [CompleteSpace H] [CompleteSpace G] in
/-- The reflection of a subspace is a self-adjoint unitary, so reflecting an
isometric embedding preserves isometry. -/
theorem isometricEmbedding_reflection_comp
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    {Y : G →L[𝕜] H} (hY : IsometricEmbedding Y) :
    IsometricEmbedding (V.reflectionOperator ∘L Y) := by
  intro y
  change ‖V.reflection (Y y)‖ = ‖y‖
  rw [V.reflection.norm_map]
  exact hY y

omit [CompleteSpace G] in
/-- The reflection operator is its own adjoint. -/
theorem adjoint_reflectionOperator (V : Submodule 𝕜 H)
    [V.HasOrthogonalProjection] :
    (V.reflectionOperator : H →L[𝕜] H).adjoint = V.reflectionOperator := by
  have hP : IsSelfAdjoint (V.starProjection : H →L[𝕜] H) :=
    isSelfAdjoint_starProjection V
  have hform : (V.reflectionOperator : H →L[𝕜] H) =
      (2 : 𝕜) • V.starProjection - 1 := by
    ext x
    simp [Submodule.reflectionOperator_apply]
  refine IsSelfAdjoint.adjoint_eq ?_
  rw [hform, IsSelfAdjoint, star_sub, star_smul, star_ofNat, hP.star_eq,
    star_one]

end ScalarGeneric

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator norm of the ambient ideal block is exactly the norm of sine
of twice the complex operator angle. -/
theorem norm_sinTwoThetaIdealBlock_complex
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoThetaIdealBlock U V‖ = ‖directedSinTwoAngleOperatorC U V‖ := by
  exact norm_starProjection_reflectedComplementary_eq_sinTwoAngle U V

/-- **Block form of the residual reflection sine-two-theta estimate.**

The right-hand side is a single block of the reflection residual, read between
the exact spectral subspace and the mirror of its complement, rather than the
whole residual.  `sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap` below
contracts that block back to `R`; the sharp directed residual `sin 2Theta_0`
estimate cannot afford the contraction, because it is exactly the block that the
reflection-defect doubling identity halves. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ≤
        N.gaugeReal ((selfAdjointSpectralSubspace A hA B hB).starProjection ∘L R ∘L
          ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
  let U := selfAdjointSpectralSubspace A hA B hB
  let Uc := selfAdjointSpectralSubspace A hA Bᶜ hB.compl
  let Wc := Uc.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  let A₀ := selfAdjointSpectralRestriction A hA B hB
  let Λ := selfAdjointSpectralRestriction A hA Bᶜ hB.compl
  let hA₀ : IsSelfAdjoint A₀ :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB
  let hΛ : _root_.IsSelfAdjoint Λ :=
    selfAdjointSpectralRestriction_isSelfAdjoint A hA Bᶜ hB.compl
  let : U.HasOrthogonalProjection :=
    selfAdjointSpectralSubspace_hasOrthogonalProjection A hA B hB
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : Wc.HasOrthogonalProjection := by
    dsimp [Wc]
    infer_instance
  let : CompleteSpace Wc :=
    (Wc.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let e : Uc ≃ₗᵢ[ℂ] Wc := unitarySubmoduleMapIsometry V.reflection Uc
  let ΛJ := unitaryConjugate e Λ hΛ
  let hΛJ : _root_.IsSelfAdjoint ΛJ := unitaryConjugate_isSelfAdjoint e Λ hΛ
  let X : U →L[ℂ] H := U.subtypeL
  let F₁ : Wc →L[ℂ] H := Wc.subtypeL
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) :=
    selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB
  -- Shared by `hFdom` and `hFint` below, which otherwise open with the same
  -- three lines.  The rest of their common preamble is entangled with the
  -- `Λ.domain`/`A.domain` coercions and is left in place deliberately.
  have hzΛ : ∀ y : ΛJ.domain, e.symm (y : Wc) ∈ Λ.domain := fun y =>
    (mem_unitaryConjugate_domain_iff e Λ hΛ).mp (by simpa only [ΛJ] using y.property)
  have hFdom : ∀ y : ΛJ.domain, F₁ (y : Wc) ∈ A.domain := by
    intro y
    let z : Λ.domain := ⟨e.symm (y : Wc), hzΛ y⟩
    have hzdom : (((z : Uc) : H)) ∈ A.domain :=
      selfAdjointSpectralRestriction_inclusion_mem_domain
        A hA Bᶜ hB.compl z
    let za : A.domain := ⟨((z : Uc) : H), hzdom⟩
    have hy : (y : H) = V.reflectionOperator (za : H) :=
      (congrArg Subtype.val (e.apply_symm_apply (y : Wc))).symm
    change (y : H) ∈ A.domain
    rw [hy]
    exact hJdom za
  have hFint : ∀ y : ΛJ.domain,
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Wc), hFdom y⟩ =
        F₁ (ΛJ y) := by
    intro y
    let z : Λ.domain := ⟨e.symm (y : Wc), hzΛ y⟩
    have hzdom : (((z : Uc) : H)) ∈ A.domain :=
      selfAdjointSpectralRestriction_inclusion_mem_domain
        A hA Bᶜ hB.compl z
    let za : A.domain := ⟨((z : Uc) : H), hzdom⟩
    have hy : (y : H) = V.reflectionOperator (za : H) :=
      (congrArg Subtype.val (e.apply_symm_apply (y : Wc))).symm
    have hsub :
        (⟨F₁ (y : Wc), hFdom y⟩ : (TauCeti.LinearPMap.addBounded A R).domain) =
          ⟨V.reflectionOperator (za : H), hJdom za⟩ :=
      Subtype.ext hy
    have hAint := selfAdjointSpectralRestriction_inclusion_intertwines
      A hA Bᶜ hB.compl z
    have hright :
        V.reflectionOperator (A za) =
          F₁ (ΛJ y) := by
      change V.reflectionOperator (A za) =
        ((ΛJ y : Wc) : H)
      calc
        V.reflectionOperator (A za) =
            V.reflectionOperator (((Λ z : Uc) : H)) :=
          congrArg V.reflectionOperator hAint
        _ = ((e (Λ z) : Wc) : H) := by
          rfl
        _ = ((ΛJ y : Wc) : H) := by
          exact congrArg Subtype.val
            (unitaryConjugate_apply e Λ hΛ y).symm
    calc
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Wc), hFdom y⟩ =
          (TauCeti.LinearPMap.addBounded A R)
            ⟨V.reflectionOperator (za : H), hJdom za⟩ := by
        exact congrArg (fun q : (TauCeti.LinearPMap.addBounded A R).domain =>
          TauCeti.LinearPMap.addBounded A R q) hsub
      _ = V.reflectionOperator (A za) := hJintertwines za
      _ = F₁ (ΛJ y) := hright
  have hXiso : IsometricEmbedding X := by
    intro x
    rfl
  have hFiso : IsometricEmbedding F₁ := by
    intro y
    rfl
  have hΛJspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum ΛJ := by
    intro lam hlam
    rw [unitaryConjugate_spectrum_eq e Λ hΛ]
    exact hBcomplSpec lam hlam
  have hraw := sinTheta_addBounded_gauge_block_of_spectrum_gap
    N A hA R hR A₀ hA₀ ΛJ hΛJ X F₁ hXdom hXint hFdom hFint
      hβα hδ hBlow hBhigh hΛJspec hRmem
  change
    N.Mem (U.subtypeL.adjoint ∘L Wc.subtypeL) ∧
      δ * N.gaugeReal (U.subtypeL.adjoint ∘L Wc.subtypeL) ≤
        N.gaugeReal ((R ∘L U.subtypeL).adjoint ∘L Wc.subtypeL) at hraw
  have hambient := projectionProduct_mem_and_gauge_le_overlap
    N U Wc hraw.1
  have hUcProjection : Uc.starProjection = Uᗮ.starProjection :=
    starProjection_selfAdjointSpectralSubspace_compl A hA B hB
  have hWcProjection : Wc.starProjection =
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection := by
    calc
      Wc.starProjection =
          boundedUnitaryConjugate V.reflection Uc.starProjection :=
        starProjection_map_unitary Uc V.reflection
      _ = boundedUnitaryConjugate V.reflection Uᗮ.starProjection := by
        rw [hUcProjection]
      _ = (Uᗮ.map
          (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection :=
        (starProjection_map_unitary Uᗮ V.reflection).symm
  have hblock :
      sinTwoThetaIdealBlock U V =
        U.starProjection ∘L Wc.starProjection := by
    unfold sinTwoThetaIdealBlock
    rw [hWcProjection]
  have hRadj : R.adjoint = R :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hR
  have hUadjProj : U.subtypeL.adjoint ∘L U.starProjection = U.subtypeL.adjoint := by
    ext x
    simp only [Submodule.adjoint_subtypeL, ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr
      (U.starProjection_apply_mem x)
  have hWcProj : (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
      Wc.subtypeL = Wc.subtypeL := by
    ext v
    change (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection (v : H)
      = (v : H)
    rw [← hWcProjection]
    exact Wc.starProjection_eq_self_iff.mpr v.property
  have hfac : (R ∘L U.subtypeL).adjoint ∘L Wc.subtypeL =
      U.subtypeL.adjoint ∘L
        (U.starProjection ∘L R ∘L
          (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L
        Wc.subtypeL := by
    rw [ContinuousLinearMap.adjoint_comp, hRadj]
    calc
      U.subtypeL.adjoint ∘L R ∘L Wc.subtypeL
          = (U.subtypeL.adjoint ∘L U.starProjection) ∘L R ∘L
              ((Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
                Wc.subtypeL) := by
            rw [hUadjProj, hWcProj]
      _ = U.subtypeL.adjoint ∘L
            (U.starProjection ∘L R ∘L
              (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L
            Wc.subtypeL := by
            rfl
  have hMidMem : N.Mem (U.starProjection ∘L R ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) :=
    N.comp_mem U.starProjection
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection hRmem
  have hcontract : N.gaugeReal ((R ∘L U.subtypeL).adjoint ∘L Wc.subtypeL) ≤
      N.gaugeReal (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
    rw [hfac]
    have hUadjNorm : ‖U.subtypeL.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hWcNorm : ‖Wc.subtypeL‖ ≤ 1 :=
      opNorm_le_one_of_isometry (fun _ => rfl)
    exact N.gaugeReal_comp_le_of_contractions U.subtypeL.adjoint Wc.subtypeL
      hMidMem hUadjNorm hWcNorm
  rw [hblock]
  refine ⟨hambient.1, ?_⟩
  calc
    δ * N.gaugeReal (U.starProjection ∘L Wc.starProjection) ≤
        δ * N.gaugeReal (U.subtypeL.adjoint ∘L Wc.subtypeL) :=
      mul_le_mul_of_nonneg_left hambient.2 hδ.le
    _ ≤ N.gaugeReal ((R ∘L U.subtypeL).adjoint ∘L Wc.subtypeL) := hraw.2
    _ ≤ N.gaugeReal (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := hcontract

/-- Residual reflection form of unbounded sine two theta at rectangular
ideal-gauge scope.  The block form above, with the block contracted back to the
whole reflection residual. -/
theorem sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ≤ N.gaugeReal R := by
  obtain ⟨hmem, hle⟩ := sinTwoTheta_reflectionResidual_block_gauge_of_spectrum_gap
    N A hA R hR B hB V hβα hδ hBlow hBhigh hBcomplSpec hJdom hJintertwines hRmem
  refine ⟨hmem, hle.trans ?_⟩
  exact N.gaugeReal_comp_le_of_contractions
    (selfAdjointSpectralSubspace A hA B hB).starProjection
    ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
      (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection hRmem
    (Submodule.starProjection_norm_le _)
    (Submodule.starProjection_norm_le _)

/-- Canonical bounded-perturbation unbounded sine-two-theta theorem at
rectangular ideal-gauge scope. -/
theorem sinTwoTheta_addBounded_gauge_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gaugeReal E := by
  let C := TauCeti.LinearPMap.addBounded A E
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA E hE
  let V := selfAdjointSpectralSubspace C hC S hS
  let D := reflectionPerturbation V E
  have hD : D.IsSymmetric :=
    reflectionPerturbation_isSelfAdjoint V E hE
  have hDideal := reflectionPerturbation_mem_and_gauge_le N V E hEmem
  have hmain := sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    N A hA D hD B hB V hβα hδ hBlow hBhigh hBcomplSpec
      (perturbedSpectralReflection_mem_domain A hA E hE S hS)
      (add_reflectionPerturbation_intertwines A hA E hE S hS)
      hDideal.1
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact hDideal.2

/-- Set-localized canonical ideal-gauge form of unbounded sine two theta. -/
theorem sinTwoTheta_addBounded_gauge_of_intervalExterior
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gaugeReal (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gaugeReal E := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hBcomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA Bᶜ hB.compl hBcomplDisj
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec hEmem


/-- Source-facing unitary-invariant-family wrapper for the spectrum-gap ideal
form. -/
theorem sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gauge E := by
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem

/-- Source-facing unitary-invariant-family wrapper for the set-localized ideal
form. -/
theorem sinTwoTheta_addBounded_unitaryInvariant_of_intervalExterior
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅)
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
        2 * N.gauge E := by
  exact sinTwoTheta_addBounded_gauge_of_intervalExterior
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBsub hBcomplDisj hEmem

/-- Residual reflection form of the unbounded sine-two-theta theorem, operator norm.  The
bounded operator `R` is required to implement reflection of `A` on its full domain.

This is `sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap` read at the operator-norm
family, where membership is vacuous and the gauge is the norm; the geometric spine is proved
once, above. -/
theorem sinTwoTheta_reflectionResidual_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x)) :
    δ * ‖directedSinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB) V‖ ≤ ‖R‖ := by
  have h := (sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    (TauCeti.operatorNormFamily ℂ) A hA R hR B hB V hβα hδ
    hBlow hBhigh hBcomplSpec hJdom hJintertwines
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily R)).2
  rwa [TauCeti.SymmetricOperatorIdealFamily.gaugeReal_operatorNormFamily,
    TauCeti.SymmetricOperatorIdealFamily.gaugeReal_operatorNormFamily,
    norm_sinTwoThetaIdealBlock_complex] at h

/-- Canonical complex operator-norm unbounded sine-two-theta theorem for a
bounded self-adjoint perturbation. -/
theorem sinTwoTheta_addBounded_of_spectrum_gap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl)) :
    δ * ‖directedSinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)‖ ≤
      2 * ‖E‖ := by
  let C := TauCeti.LinearPMap.addBounded A E
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA E hE
  let V := selfAdjointSpectralSubspace C hC S hS
  let D := reflectionPerturbation V E
  have hD : D.IsSymmetric :=
    reflectionPerturbation_isSelfAdjoint V E hE
  have hmain :
      δ * ‖directedSinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB) V‖ ≤ ‖D‖ :=
    sinTwoTheta_reflectionResidual_of_spectrum_gap
      A hA D hD B hB V hβα hδ hBlow hBhigh hBcomplSpec
      (perturbedSpectralReflection_mem_domain A hA E hE S hS)
      (add_reflectionPerturbation_intertwines A hA E hE S hS)
  exact hmain.trans (norm_reflectionPerturbation_le V E)

/-- Set-localized form of the canonical complex unbounded sine-two-theta
theorem. -/
theorem sinTwoTheta_addBounded_of_intervalExterior
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsub : B ⊆ Set.Icc β α)
    (hBcomplDisj : Bᶜ ∩ Set.Ioo (β - δ) (α + δ) = ∅) :
    δ * ‖directedSinTwoAngleOperatorC
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
          (addBounded_isSelfAdjoint A hA E hE) S hS)‖ ≤
      2 * ‖E‖ := by
  obtain ⟨hBlow, hBhigh⟩ :=
    selfAdjointSpectralRestriction_semibounded_of_subset_Icc
      A hA B hB hBsub
  have hBcomplSpec :=
    selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA Bᶜ hB.compl hBcomplDisj
  exact sinTwoTheta_addBounded_of_spectrum_gap
    A hA E hE B S hB hS hβα hδ hBlow hBhigh hBcomplSpec

end DavisKahan
end TauCeti
