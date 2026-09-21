/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.FrameFactorizationGeneric
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Frame Factorization -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real infinite-dimensional lower-frame polar factorization

A bounded-below real trial map is complexified.  The positive square root and
inverse square root of its complex Gram operator are fixed by canonical
conjugation and therefore descend to real bounded operators.  All package laws
are then reflected through the injective complexification functor.

## Where this sits among the three frame-factorization modules

This file is the **`ℝ` existence proof** for `LowerFramePolarData`. Its two
siblings, documented at length in `DavisKahan/SinTheta/FrameFactorization.lean`:
that module declares the structure and proves it inhabited over `ℂ`, and
`DavisKahan/SinTheta/FrameFactorizationGeneric.lean` is the `𝕜`-generic consumer
layer, which proves no existence at all. The scalar field separates this file
from the first and is irrelevant to the third.

-/

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
open RealComplexification

noncomputable section

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-! The real algebra structure and the real continuous functional calculus on the
complexified operator algebra are `scoped instance`s of
`RealComplexification`, opened below.  They used to be reinstalled
here as a second `local instance`, which made them a *different declaration* from the
one the imported lemmas are stated against; see lane `{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.RealComplexification

omit [CompleteSpace E] [CompleteSpace F] in
/-- A positive real lower-frame estimate survives coordinatewise
complexification with the same constant. -/
theorem lowerFrameBound_complexify
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    LowerFrameBound (complexify X) ε := by
  intro z
  have hre := hX (re z)
  have him := hX (im z)
  have hre0 : 0 ≤ ε * ‖re z‖ := mul_nonneg hε (norm_nonneg _)
  have him0 : 0 ≤ ε * ‖im z‖ := mul_nonneg hε (norm_nonneg _)
  have hreSq : (ε * ‖re z‖) ^ 2 ≤ ‖X (re z)‖ ^ 2 :=
    (sq_le_sq₀ hre0 (norm_nonneg _)).2 hre
  have himSq : (ε * ‖im z‖) ^ 2 ≤ ‖X (im z)‖ ^ 2 :=
    (sq_le_sq₀ him0 (norm_nonneg _)).2 him
  have hsq : (ε * ‖z‖) ^ 2 ≤ ‖complexify X z‖ ^ 2 := by
    rw [mul_pow, norm_sq, norm_sq]
    simp only [re_complexify, im_complexify]
    nlinarith
  exact (sq_le_sq₀
    (mul_nonneg hε (norm_nonneg z)) (norm_nonneg (complexify X z))).1 hsq

/-- The complex Gram operator of a complexified real map is fixed by canonical
conjugation. -/
theorem conjugateOperator_complexify_gram
    (X : F →L[ℝ] E) :
    conjugateOperator ((complexify X).adjoint ∘L complexify X) =
      (complexify X).adjoint ∘L complexify X := by
  rw [← complexify_gram]
  exact conjugateOperator_complexify (X.adjoint ∘L X)

/-- Real continuous functional calculus descent for a positive real power of a
complexified positive operator. -/
theorem conjugateOperator_rpow_eq
    (C : RealComplexification F →L[ℂ] RealComplexification F)
    (hC : 0 ≤ C) (hunit : IsUnit C)
    (hfix : conjugateOperator C = C) (r : ℝ) :
    conjugateOperator (C ^ r) = C ^ r := by
  rw [CFC.rpow_eq_cfc_real hC]
  refine conjugateOperator_cfc_eq C hC.isSelfAdjoint hfix
    (fun x : ℝ => x ^ r) ?_
  refine continuousOn_id.rpow_const fun x hx => Or.inl ?_
  intro hx0
  rw [id_eq] at hx0
  subst hx0
  exact (spectrum.zero_notMem ℝ hunit) hx

private theorem gramRpow_half_identities
    (G : RealComplexification F →L[ℂ] RealComplexification F)
    (hG : 0 ≤ G) (hunit : IsUnit G) :
    G ^ (-1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) = 1 ∧
      G ^ (1 / 2 : ℝ) * G ^ (-1 / 2 : ℝ) = 1 ∧
      G ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ) = G := by
  have hadd : ∀ s t : ℝ, G ^ s * G ^ t = G ^ (s + t) :=
    fun _ _ => (CFC.rpow_add hunit).symm
  constructor
  · rw [hadd]
    norm_num [CFC.rpow_zero G hG]
  constructor
  · rw [hadd]
    norm_num [CFC.rpow_zero G hG]
  · rw [hadd]
    norm_num [CFC.rpow_one G hG]

/-- Existence of the real lower-frame polar package. -/
theorem lowerFramePolarData_real_nonempty
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Nonempty (LowerFramePolarData X ε hX hε) := by
  let XC : RealComplexification F →L[ℂ] RealComplexification E := complexify X
  let gramR : F →L[ℝ] F := X.adjoint ∘L X
  let gramC : RealComplexification F →L[ℂ] RealComplexification F :=
    XC.adjoint ∘L XC
  have hframeC : LowerFrameBound XC ε := by
    simpa [XC] using lowerFrameBound_complexify X hX hε.le
  have hgramC_eq : complexify gramR = gramC := by
    simpa [gramR, gramC, XC] using complexify_gram X
  have hgram_nonneg : 0 ≤ gramC := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive (f := gramC)).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self XC)
  have hgram_unit : IsUnit gramC := by
    refine TauCeti.ContinuousLinearMap.isUnit_of_coercive
      (sq_pos_of_pos hε) ?_
    simpa [gramC] using gram_coercive hframeC hε.le
  have hgram_fix : conjugateOperator gramC = gramC := by
    rw [← hgramC_eq]
    exact conjugateOperator_complexify gramR
  let sqrtC : RealComplexification F →L[ℂ] RealComplexification F :=
    gramC ^ (1 / 2 : ℝ)
  let invSqrtC : RealComplexification F →L[ℂ] RealComplexification F :=
    gramC ^ (-1 / 2 : ℝ)
  have hsqrt_fix : conjugateOperator sqrtC = sqrtC := by
    simpa [sqrtC] using
      conjugateOperator_rpow_eq gramC hgram_nonneg hgram_unit hgram_fix (1 / 2 : ℝ)
  have hinvSqrt_fix : conjugateOperator invSqrtC = invSqrtC := by
    simpa [invSqrtC] using
      conjugateOperator_rpow_eq gramC hgram_nonneg hgram_unit hgram_fix (-1 / 2 : ℝ)
  let sqrtR : F →L[ℝ] F := realPartOperator sqrtC
  let invSqrtR : F →L[ℝ] F := realPartOperator invSqrtC
  have hsqrt_complexify : complexify sqrtR = sqrtC := by
    simpa [sqrtR] using complexify_realPartOperator hsqrt_fix
  have hinvSqrt_complexify : complexify invSqrtR = invSqrtC := by
    simpa [invSqrtR] using complexify_realPartOperator hinvSqrt_fix
  have hident := gramRpow_half_identities gramC hgram_nonneg hgram_unit
  have hinvSqrt_sqrtC :
      invSqrtC ∘L sqrtC = ContinuousLinearMap.id ℂ (RealComplexification F) := hident.1
  have hsqrt_invSqrtC :
      sqrtC ∘L invSqrtC = ContinuousLinearMap.id ℂ (RealComplexification F) := hident.2.1
  have hsqrt_sqC : sqrtC ∘L sqrtC = gramC := hident.2.2
  have hinvSqrt_sqrtR :
      invSqrtR ∘L sqrtR = ContinuousLinearMap.id ℝ F := by
    apply complexify_injective
    rw [complexify_comp, hinvSqrt_complexify, hsqrt_complexify,
      complexify_id]
    exact hinvSqrt_sqrtC
  have hsqrt_invSqrtR :
      sqrtR ∘L invSqrtR = ContinuousLinearMap.id ℝ F := by
    apply complexify_injective
    rw [complexify_comp, hsqrt_complexify, hinvSqrt_complexify,
      complexify_id]
    exact hsqrt_invSqrtC
  have hsqrt_sqR : sqrtR ∘L sqrtR = X.adjoint ∘L X := by
    apply complexify_injective
    rw [complexify_comp, hsqrt_complexify, hgramC_eq]
    exact hsqrt_sqC
  have hinvSqrt_adjointC : invSqrtC.adjoint = invSqrtC := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (CFC.rpow_nonneg (a := gramC) (y := (-1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hinvSqrt_gramC : invSqrtC ∘L gramC = sqrtC := by
    change invSqrtC * gramC = sqrtC
    calc
      invSqrtC * gramC = gramC ^ (-1 / 2 : ℝ) * gramC ^ (1 : ℝ) := by
        rw [CFC.rpow_one gramC hgram_nonneg]
      _ = gramC ^ ((-1 / 2 : ℝ) + (1 : ℝ)) :=
        (CFC.rpow_add hgram_unit).symm
      _ = gramC ^ (1 / 2 : ℝ) := by norm_num
      _ = sqrtC := rfl
  have hnormalized_gramC :
      (XC ∘L invSqrtC).adjoint ∘L (XC ∘L invSqrtC) =
        ContinuousLinearMap.id ℂ (RealComplexification F) := by
    rw [ContinuousLinearMap.adjoint_comp, hinvSqrt_adjointC]
    calc
      (invSqrtC ∘L XC.adjoint) ∘L (XC ∘L invSqrtC) =
          invSqrtC ∘L ((XC.adjoint ∘L XC) ∘L invSqrtC) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (invSqrtC ∘L gramC) ∘L invSqrtC := by
        simp only [gramC, ContinuousLinearMap.comp_assoc]
      _ = sqrtC ∘L invSqrtC := by rw [hinvSqrt_gramC]
      _ = ContinuousLinearMap.id ℂ (RealComplexification F) := hsqrt_invSqrtC
  have hnormalizedC : IsometricEmbedding (XC ∘L invSqrtC) := by
    intro z
    have hinner :
        ⟪(XC ∘L invSqrtC) z, (XC ∘L invSqrtC) z⟫_ℂ = ⟪z, z⟫_ℂ := by
      calc
        ⟪(XC ∘L invSqrtC) z, (XC ∘L invSqrtC) z⟫_ℂ =
            ⟪((XC ∘L invSqrtC).adjoint ∘L (XC ∘L invSqrtC)) z, z⟫_ℂ := by
          simpa only [ContinuousLinearMap.comp_apply] using
            ((XC ∘L invSqrtC).adjoint_inner_left z
              ((XC ∘L invSqrtC) z)).symm
        _ = ⟪z, z⟫_ℂ := by rw [hnormalized_gramC]; simp
    have hsquare : ‖(XC ∘L invSqrtC) z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    nlinarith [norm_nonneg ((XC ∘L invSqrtC) z), norm_nonneg z]
  have hnormalizedR : IsometricEmbedding (X ∘L invSqrtR) := by
    intro x
    calc
      ‖(X ∘L invSqrtR) x‖ = ‖ofReal ((X ∘L invSqrtR) x)‖ := by
        rw [ofReal.norm_map]
      _ = ‖(XC ∘L invSqrtC) (ofReal x)‖ := by
        congr 1
        simp only [ContinuousLinearMap.comp_apply, XC,
          ← hinvSqrt_complexify, complexify_ofReal]
      _ = ‖ofReal x‖ := hnormalizedC (ofReal x)
      _ = ‖x‖ := ofReal.norm_map x
  have hfactorizationR : X = (X ∘L invSqrtR) ∘L sqrtR := by
    symm
    calc
      (X ∘L invSqrtR) ∘L sqrtR = X ∘L (invSqrtR ∘L sqrtR) :=
        ContinuousLinearMap.comp_assoc _ _ _
      _ = X := by rw [hinvSqrt_sqrtR]; simp
  have hinvSqrt_normR : ‖invSqrtR‖ ≤ ε⁻¹ := by
    refine invSqrtR.opNorm_le_bound (inv_nonneg.mpr hε.le) ?_
    intro x
    rw [le_inv_mul_iff₀ hε]
    calc
      ε * ‖invSqrtR x‖ ≤ ‖X (invSqrtR x)‖ := hX (invSqrtR x)
      _ = ‖x‖ := hnormalizedR x
  have hrangeR :
      LinearMap.range (X ∘L invSqrtR).toLinearMap =
        LinearMap.range X.toLinearMap := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨invSqrtR x, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨sqrtR x, ?_⟩
      have hx := DFunLike.congr_fun hfactorizationR x
      exact hx.symm
  let gramInvR : F →L[ℝ] F := invSqrtR ∘L invSqrtR
  have hgramInv_left :
      gramInvR ∘L (X.adjoint ∘L X) = ContinuousLinearMap.id ℝ F := by
    rw [← hsqrt_sqR]
    simp only [gramInvR, ContinuousLinearMap.comp_assoc]
    calc
      invSqrtR ∘L (invSqrtR ∘L (sqrtR ∘L sqrtR)) =
          invSqrtR ∘L ((invSqrtR ∘L sqrtR) ∘L sqrtR) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id ℝ F := by
        rw [hinvSqrt_sqrtR, ContinuousLinearMap.id_comp]
        exact hinvSqrt_sqrtR
  have hgramInv_right :
      (X.adjoint ∘L X) ∘L gramInvR = ContinuousLinearMap.id ℝ F := by
    rw [← hsqrt_sqR]
    simp only [gramInvR, ContinuousLinearMap.comp_assoc]
    calc
      (sqrtR ∘L sqrtR) ∘L (invSqrtR ∘L invSqrtR) =
          sqrtR ∘L ((sqrtR ∘L invSqrtR) ∘L invSqrtR) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id ℝ F := by
        rw [hsqrt_invSqrtR, ContinuousLinearMap.id_comp]
        exact hsqrt_invSqrtR
  refine ⟨{
    sqrt := sqrtR
    invSqrt := invSqrtR
    gramInverse := {
      inv := gramInvR
      left_inv := hgramInv_left
      right_inv := hgramInv_right
    }
    invSqrt_sqrt := hinvSqrt_sqrtR
    sqrt_invSqrt := hsqrt_invSqrtR
    sqrt_sq := hsqrt_sqR
    normalized_isometry := hnormalizedR
    factorization := hfactorizationR
    invSqrt_norm_le := hinvSqrt_normR
    range_normalized := hrangeR
    invSqrt_eq_id_of_isometry := ?_
  }⟩
  intro hIso
  have hgram_id : gramR = ContinuousLinearMap.id ℝ F := by
    simpa [gramR] using adjoint_comp_self_eq_id_of_isometry hIso
  apply complexify_injective
  rw [hinvSqrt_complexify, complexify_id]
  change gramC ^ (-1 / 2 : ℝ) = ContinuousLinearMap.id ℂ (RealComplexification F)
  rw [← hgramC_eq, hgram_id, complexify_id]
  exact CFC.one_rpow

/-- The selected real lower-frame polar package. -/
noncomputable def lowerFramePolarDataReal
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LowerFramePolarData X ε hX hε :=
  Classical.choice (lowerFramePolarData_real_nonempty X hX hε)

/-- The selected real normalized frame isometry. -/
noncomputable def frameIsometryReal
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℝ] E :=
  frameIsometryOfPolarData (lowerFramePolarDataReal X hX hε)

/-- The selected real generalized complementary sine block. -/
noncomputable def sinThetaBlockReal
    (X : F →L[ℝ] E) (F₁ : G →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : G →L[ℝ] F :=
  sinThetaBlockOfPolarData (lowerFramePolarDataReal X hX hε) F₁

end

end ExactSinTheta
end DavisKahan
end TauCeti
