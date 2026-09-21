/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.Sylvester.Bounded
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Frame Factorization -/

open TauCeti.DavisKahan.Sylvester

/-!
# Infinite-dimensional lower-frame factorization

The generalized theorem permits a non-isometric trial map with a positive lower
frame bound.  This module exposes the closed-range, Gram inverse, polar factor,
and ideal-norm transport seams separately.

## The three frame-factorization modules, and how they relate

Documented 2026-07-30 (lane DK-FRAME) because none of the three said anything
about the other two, and the third is named `Generic`, which reads as *the
general existence theorem* when it is in fact *the layer that needs no field*.

* **`DavisKahan/SinTheta/FrameFactorization.lean`** (this file) declares
  `structure LowerFramePolarData` and proves it **inhabited over `ℂ`**
  (`lowerFramePolarData_nonempty`): the Gram operator `X⋆X` is strictly positive
  by the lower-frame estimate, and its real powers under the continuous
  functional calculus supply the square root and inverse square root.
* **`DavisKahan/SinTheta/Real/FrameFactorization.lean`** proves the same package
  **inhabited over `ℝ`** (`lowerFramePolarData_real_nonempty`), by complexifying
  the trial map and descending: the square root and inverse square root of the
  complex Gram operator are fixed by the canonical conjugation, so they are real.
* **`DavisKahan/SinTheta/FrameFactorizationGeneric.lean`** consumes a package and
  proves **nothing about existence**. Factorization, ideal transport and the
  exact-angle arguments are pure Hilbert-space algebra once the data is in hand,
  so they are stated `𝕜`-generically there.

**The separating hypothesis is the scalar field, and it separates only the two
existence proofs.** `Generic` is downstream of both and independent of the field;
it is not a strengthening of either.

-/

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Generic

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A quantitative lower frame bound. -/
def LowerFrameBound (X : F →L[𝕜] E) (ε : ℝ) : Prop :=
  ∀ x, ε * ‖x‖ ≤ ‖X x‖

omit [CompleteSpace E] [CompleteSpace F] in
/-- A lower frame bound remains valid after decreasing its constant. -/
theorem LowerFrameBound.mono
    {X : F →L[𝕜] E} {ε ε' : ℝ}
    (hX : LowerFrameBound X ε) (hε'ε : ε' ≤ ε) :
    LowerFrameBound X ε' := by
  intro x
  exact (mul_le_mul_of_nonneg_right hε'ε (norm_nonneg x)).trans (hX x)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A positive lower frame bound implies injectivity. -/
theorem LowerFrameBound.injective
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Function.Injective X := by
  intro x y hxy
  have hbound := hX (x - y)
  have hzero : X (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

omit [CompleteSpace E] [CompleteSpace F] in
/-- An isometric trial map has lower frame bound one. -/
theorem lowerFrameBound_one_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    LowerFrameBound X 1 := by
  intro x
  simpa using le_of_eq (hX x).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- An isometric embedding is a contraction in operator norm. -/
theorem opNorm_le_one_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    ‖X‖ ≤ 1 := by
  refine X.opNorm_le_bound zero_le_one ?_
  intro x
  simpa using le_of_eq (hX x)

/-- The Gram operator of an isometric embedding is the identity. -/
theorem adjoint_comp_self_eq_id_of_isometry
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X) :
    X.adjoint ∘L X = ContinuousLinearMap.id 𝕜 F := by
  let U : F →ₗᵢ[𝕜] E :=
    { toLinearMap := X.toLinearMap
      norm_map' := hX }
  ext x
  exact ext_inner_right 𝕜 fun y => by
    calc
      ⟪(X.adjoint ∘L X) x, y⟫_𝕜 = ⟪X x, X y⟫_𝕜 := by
        rw [ContinuousLinearMap.comp_apply, X.adjoint_inner_left]
      _ = ⟪x, y⟫_𝕜 := U.inner_map_map x y
      _ = ⟪(ContinuousLinearMap.id 𝕜 F) x, y⟫_𝕜 := by simp

omit [CompleteSpace E] in
/-- A positive lower frame bound implies closed range. -/
theorem LowerFrameBound.closedRange
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsClosed (Set.range X) := by
  obtain ⟨K, hanti⟩ : ∃ K : NNReal, AntilipschitzWith K X :=
    (antilipschitzWith_iff_exists_mul_le_norm (f := X)).2 ⟨ε, hε, hX⟩
  exact hanti.isClosed_range X.uniformContinuous

/-- Coercivity of the Gram operator. -/
theorem gram_coercive
    {X : F →L[𝕜] E} {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    ∀ x, ε ^ 2 * ‖x‖ ^ 2
      ≤ RCLike.re ⟪(X.adjoint ∘L X) x, x⟫_𝕜 := by
  intro x
  rw [ContinuousLinearMap.comp_apply, X.adjoint_inner_left,
    ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  have hle : ε * ‖x‖ ≤ ‖X x‖ := hX x
  have hleft : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
  have hdiff : 0 ≤ ‖X x‖ - ε * ‖x‖ := sub_nonneg.mpr hle
  have hsum : 0 ≤ ‖X x‖ + ε * ‖x‖ :=
    add_nonneg (norm_nonneg (X x)) hleft
  have hprod := mul_nonneg hdiff hsum
  nlinarith

/-- Proof-carrying lower-frame polar data.  The single existence theorem below
is the functional-calculus seam; all public factorization and transport results
are projections or consequences of this package. -/
structure LowerFramePolarData
    (X : F →L[𝕜] E) (ε : ℝ)
    (hX : LowerFrameBound X ε) (hε : 0 < ε) where
  sqrt : F →L[𝕜] F
  invSqrt : F →L[𝕜] F
  gramInverse : BoundedInverseData (X.adjoint ∘L X)
  invSqrt_sqrt : invSqrt ∘L sqrt = ContinuousLinearMap.id 𝕜 F
  sqrt_invSqrt : sqrt ∘L invSqrt = ContinuousLinearMap.id 𝕜 F
  sqrt_sq : sqrt ∘L sqrt = X.adjoint ∘L X
  normalized_isometry : IsometricEmbedding (X ∘L invSqrt)
  factorization : X = (X ∘L invSqrt) ∘L sqrt
  invSqrt_norm_le : ‖invSqrt‖ ≤ ε⁻¹
  range_normalized :
    LinearMap.range (X ∘L invSqrt).toLinearMap = LinearMap.range X.toLinearMap
  invSqrt_eq_id_of_isometry :
    ∀ _hIso : IsometricEmbedding X, invSqrt = ContinuousLinearMap.id 𝕜 F

/-- The polar package is explicit when the trial map is already isometric. -/
def lowerFramePolarDataOfIsometry
    (X : F →L[𝕜] E) (hIso : IsometricEmbedding X) :
    LowerFramePolarData X 1 (lowerFrameBound_one_of_isometry hIso) zero_lt_one := by
  let I : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F
  have hgram : X.adjoint ∘L X = I := adjoint_comp_self_eq_id_of_isometry hIso
  refine {
    sqrt := I
    invSqrt := I
    gramInverse := {
      inv := I
      left_inv := ?_
      right_inv := ?_
    }
    invSqrt_sqrt := ?_
    sqrt_invSqrt := ?_
    sqrt_sq := ?_
    normalized_isometry := ?_
    factorization := ?_
    invSqrt_norm_le := ?_
    range_normalized := ?_
    invSqrt_eq_id_of_isometry := ?_
  }
  · rw [hgram]
    simp [I]
  · rw [hgram]
    simp [I]
  · simp [I]
  · simp [I]
  · simpa [I] using hgram.symm
  · simpa [I] using hIso
  · simp [I]
  · simpa [I] using (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F))
  · simp [I]
  · intro _
    rfl

end Generic

section Complex

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Existence of the bounded-below polar package over a complex Hilbert
space.  The Gram operator is strictly positive by the lower-frame estimate;
its real powers supply the square root and inverse square root. -/
theorem lowerFramePolarData_nonempty
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Nonempty (LowerFramePolarData X ε hX hε) := by
  let gram : F →L[ℂ] F := X.adjoint ∘L X
  have hgram_nonneg : 0 ≤ gram := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive gram).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self X)
  have hgram_unit : IsUnit gram := by
    refine TauCeti.ContinuousLinearMap.isUnit_of_coercive
      (sq_pos_of_pos hε) ?_
    simpa [gram] using gram_coercive hX hε.le
  let sqrt : F →L[ℂ] F := gram ^ (1 / 2 : ℝ)
  let invSqrt : F →L[ℂ] F := gram ^ (-1 / 2 : ℝ)
  let gramInv : F →L[ℂ] F := Ring.inverse gram
  -- The three compositions below are one `rpow_add` each, differing only in the exponents;
  -- naming that step keeps the difference visible instead of repeating the calc three times.
  have hrpow : ∀ s t : ℝ, gram ^ s * gram ^ t = gram ^ (s + t) :=
    fun _ _ => (CFC.rpow_add hgram_unit).symm
  have hinvSqrt_sqrt : invSqrt ∘L sqrt = ContinuousLinearMap.id ℂ F := by
    change invSqrt * sqrt = 1
    calc
      invSqrt * sqrt = gram ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) := hrpow _ _
      _ = gram ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero gram hgram_nonneg
  have hsqrt_invSqrt : sqrt ∘L invSqrt = ContinuousLinearMap.id ℂ F := by
    change sqrt * invSqrt = 1
    calc
      sqrt * invSqrt = gram ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) := hrpow _ _
      _ = gram ^ (0 : ℝ) := by norm_num
      _ = 1 := CFC.rpow_zero gram hgram_nonneg
  have hsqrt_sq : sqrt ∘L sqrt = X.adjoint ∘L X := by
    change sqrt * sqrt = gram
    calc
      sqrt * sqrt = gram ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := hrpow _ _
      _ = gram ^ (1 : ℝ) := by norm_num
      _ = gram := CFC.rpow_one gram hgram_nonneg
  have hinvSqrt_adjoint : invSqrt.adjoint = invSqrt := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (CFC.rpow_nonneg (a := gram) (y := (-1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hinvSqrt_gram : invSqrt ∘L gram = sqrt := by
    change invSqrt * gram = sqrt
    calc
      invSqrt * gram = gram ^ (-1 / 2 : ℝ) * gram ^ (1 : ℝ) := by
        rw [CFC.rpow_one gram hgram_nonneg]
      _ = gram ^ ((-1 / 2 : ℝ) + (1 : ℝ)) :=
        (CFC.rpow_add hgram_unit).symm
      _ = gram ^ (1 / 2 : ℝ) := by norm_num
      _ = sqrt := rfl
  have hnormalized_gram :
      (X ∘L invSqrt).adjoint ∘L (X ∘L invSqrt) =
        ContinuousLinearMap.id ℂ F := by
    rw [ContinuousLinearMap.adjoint_comp, hinvSqrt_adjoint]
    calc
      (invSqrt ∘L X.adjoint) ∘L (X ∘L invSqrt) =
          invSqrt ∘L ((X.adjoint ∘L X) ∘L invSqrt) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (invSqrt ∘L gram) ∘L invSqrt := by
        simp only [gram, ContinuousLinearMap.comp_assoc]
      _ = sqrt ∘L invSqrt := by rw [hinvSqrt_gram]
      _ = ContinuousLinearMap.id ℂ F := hsqrt_invSqrt
  have hnormalized : IsometricEmbedding (X ∘L invSqrt) := by
    intro x
    have hinner :
        ⟪(X ∘L invSqrt) x, (X ∘L invSqrt) x⟫_ℂ = ⟪x, x⟫_ℂ := by
      calc
        ⟪(X ∘L invSqrt) x, (X ∘L invSqrt) x⟫_ℂ =
            ⟪((X ∘L invSqrt).adjoint ∘L (X ∘L invSqrt)) x, x⟫_ℂ := by
          simpa only [ContinuousLinearMap.comp_apply] using
            ((X ∘L invSqrt).adjoint_inner_left x ((X ∘L invSqrt) x)).symm
        _ = ⟪x, x⟫_ℂ := by rw [hnormalized_gram]; simp
    have hsquare : ‖(X ∘L invSqrt) x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),
        norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
    nlinarith [norm_nonneg ((X ∘L invSqrt) x), norm_nonneg x]
  have hfactorization : X = (X ∘L invSqrt) ∘L sqrt := by
    symm
    calc
      (X ∘L invSqrt) ∘L sqrt = X ∘L (invSqrt ∘L sqrt) :=
        ContinuousLinearMap.comp_assoc _ _ _
      _ = X := by rw [hinvSqrt_sqrt]; simp
  have hinvSqrt_norm : ‖invSqrt‖ ≤ ε⁻¹ := by
    refine invSqrt.opNorm_le_bound (inv_nonneg.mpr hε.le) ?_
    intro x
    rw [le_inv_mul_iff₀ hε]
    calc
      ε * ‖invSqrt x‖ ≤ ‖X (invSqrt x)‖ := hX (invSqrt x)
      _ = ‖x‖ := hnormalized x
  have hrange :
      LinearMap.range (X ∘L invSqrt).toLinearMap =
        LinearMap.range X.toLinearMap := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨invSqrt x, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨sqrt x, ?_⟩
      have hx := DFunLike.congr_fun hfactorization x
      exact hx.symm
  have hgramInv_left :
      gramInv ∘L gram = ContinuousLinearMap.id ℂ F := by
    change gramInv * gram = 1
    exact Ring.inverse_mul_cancel gram hgram_unit
  have hgramInv_right :
      gram ∘L gramInv = ContinuousLinearMap.id ℂ F := by
    change gram * gramInv = 1
    exact Ring.mul_inverse_cancel gram hgram_unit
  refine ⟨{
    sqrt := sqrt
    invSqrt := invSqrt
    gramInverse := {
      inv := gramInv
      left_inv := by simpa [gram] using hgramInv_left
      right_inv := by simpa [gram] using hgramInv_right
    }
    invSqrt_sqrt := hinvSqrt_sqrt
    sqrt_invSqrt := hsqrt_invSqrt
    sqrt_sq := hsqrt_sq
    normalized_isometry := hnormalized
    factorization := hfactorization
    invSqrt_norm_le := hinvSqrt_norm
    range_normalized := hrange
    invSqrt_eq_id_of_isometry := ?_
  }⟩
  intro hIso
  have hgram_id : gram = ContinuousLinearMap.id ℂ F := by
    simpa [gram] using adjoint_comp_self_eq_id_of_isometry hIso
  change gram ^ (-1 / 2 : ℝ) = ContinuousLinearMap.id ℂ F
  rw [hgram_id]
  exact CFC.one_rpow

/-- The selected proof-carrying lower-frame polar package. -/
noncomputable def lowerFramePolarData
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LowerFramePolarData X ε hX hε :=
  Classical.choice (lowerFramePolarData_nonempty X hX hε)

/-- Bounded inverse of the positive Gram operator. -/
noncomputable def gramInverseData
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    BoundedInverseData (X.adjoint ∘L X) :=
  (lowerFramePolarData X hX hε).gramInverse

/-- Inverse square root of the Gram operator. -/
noncomputable def gramInvSqrt
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[ℂ] F :=
  (lowerFramePolarData X hX hε).invSqrt

/-- Square root of the Gram operator. -/
noncomputable def gramSqrt
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℂ] F :=
  (lowerFramePolarData X hX hε).sqrt

/-- Isometric polar factor of a bounded-below trial map. -/
noncomputable def frameIsometry
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    F →L[ℂ] E :=
  X ∘L gramInvSqrt X hX hε

/-- For an isometric trial map, the lower-frame polar factor is the trial
map itself.  This is the bridge used to derive the isometric theorem from the
generalized lower-frame theorem rather than maintaining two independent
canonical proofs. -/
theorem frameIsometry_eq_of_isometry
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X) :
    frameIsometry X (lowerFrameBound_one_of_isometry hX) zero_lt_one = X := by
  have hinv :
      gramInvSqrt X (lowerFrameBound_one_of_isometry hX) zero_lt_one =
        ContinuousLinearMap.id ℂ F :=
    (lowerFramePolarData X
      (lowerFrameBound_one_of_isometry hX) zero_lt_one).invSqrt_eq_id_of_isometry hX
  unfold frameIsometry
  rw [hinv]
  simp

/-- The polar factor preserves norms. -/
theorem frameIsometry_isometry
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    IsometricEmbedding (frameIsometry X hX hε) := by
  simpa [frameIsometry, gramInvSqrt] using
    (lowerFramePolarData X hX hε).normalized_isometry

/-- Polar factorization of the trial map. -/
theorem frameFactorization
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    X = frameIsometry X hX hε ∘L gramSqrt X hX hε := by
  simpa [frameIsometry, gramInvSqrt, gramSqrt] using
    (lowerFramePolarData X hX hε).factorization

/-- Quantitative inverse-square-root estimate. -/
theorem norm_gramInvSqrt_le
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    ‖gramInvSqrt X hX hε‖ ≤ ε⁻¹ := by
  simpa [gramInvSqrt] using
    (lowerFramePolarData X hX hε).invSqrt_norm_le

/-- The range of the polar factor agrees with the range of the trial map. -/
theorem range_frameIsometry_eq_range
    (X : F →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LinearMap.range (frameIsometry X hX hε).toLinearMap =
      LinearMap.range X.toLinearMap := by
  simpa [frameIsometry, gramInvSqrt] using
    (lowerFramePolarData X hX hε).range_normalized

/-- Directed sine block used in the paper-facing generalized theorem. -/
noncomputable def sinThetaBlock
    (X : F →L[ℂ] E) (F₁ : G →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    G →L[ℂ] F :=
  (frameIsometry X hX hε).adjoint ∘L F₁

/-- Lower-frame transport from the raw complementary block to the sine block. -/
theorem lowerFrame_sinThetaBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (X : F →L[ℂ] E) (F₁ : G →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hRaw : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem (sinThetaBlock X F₁ hX hε) ∧
      ε * N.gaugeReal (sinThetaBlock X F₁ hX hε)
        ≤ N.gaugeReal (X.adjoint ∘L F₁) := by
  have hBlock :
      sinThetaBlock X F₁ hX hε =
        (gramInvSqrt X hX hε).adjoint ∘L (X.adjoint ∘L F₁) := by
    unfold sinThetaBlock frameIsometry
    rw [ContinuousLinearMap.adjoint_comp]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hMem :
      N.Mem ((gramInvSqrt X hX hε).adjoint ∘L (X.adjoint ∘L F₁)) :=
    N.comp_left_mem (gramInvSqrt X hX hε).adjoint hRaw
  have hnorm : ‖(gramInvSqrt X hX hε).adjoint‖ ≤ ε⁻¹ := by
    simpa using norm_gramInvSqrt_le X hX hε
  have hgauge :
      N.gaugeReal (sinThetaBlock X F₁ hX hε) ≤
        ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁) := by
    rw [hBlock]
    exact (N.gaugeReal_comp_left_le_mul
      (gramInvSqrt X hX hε).adjoint hRaw).trans
        (mul_le_mul_of_nonneg_right hnorm (N.gaugeReal_nonneg hRaw))
  refine ⟨hBlock ▸ hMem, ?_⟩
  calc
    ε * N.gaugeReal (sinThetaBlock X F₁ hX hε)
        ≤ ε * (ε⁻¹ * N.gaugeReal (X.adjoint ∘L F₁)) :=
      mul_le_mul_of_nonneg_left hgauge hε.le
    _ = N.gaugeReal (X.adjoint ∘L F₁) := by
      rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

end Complex

end ExactSinTheta
end DavisKahan
end TauCeti
