/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section4
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.BasisAngleEnergy
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus

/-! # Section4Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Section 4 over a **real** Hilbert space

Standing assumption 1 of the paper is that the Hilbert space is "real or
complex", and Section 4 is written over an infinite orthonormal sequence, so its
printed scope is a real *or* complex Hilbert space of arbitrary dimension.
This module supplies the real Section 4 statements in arbitrary dimension, with
the same constants as the complex forms and with ideal membership concluded by
the corresponding dominance theorem.

## Why no new analysis is needed

Two facts already in the repository do all the work, and neither was recorded
against the Section 4 rows.

* `…ExactSinTheta.ComplexificationApproximation.approximationNumber_complexify`
  says a real operator and its complexification have **equal** approximation
  numbers -- not merely comparable ones.  Its two halves are the real
  Courant--Fischer localization (lower) and complexification of real finite-rank
  approximants (upper).  Consequently every finite Ky Fan approximation gauge is
  preserved exactly, which is
  `…ComplexificationApproximation.kyFanApproximationGauge_complexify`.
* `DavisKahan/Geometry/Polar/DirectRotationReal.lean` supplies the real direct
  rotation and proves it is the real restriction of the complex one.

So the real minimizer is the real direct rotation, the real competitor is an
arbitrary real orthogonal operator carrying `U` onto `V`, and the inequality is
the complex one read through an equality of approximation numbers.

## The ideal family is real

Corollary 4.1 is stated here over a **real** `KyFanDominantIdealFamily`, not by
transporting a complex one.  That is deliberate: `KyFanDominantIdealFamily` is
`RCLike`-generic but carries no gauge-complexification law, so a complex family's
gauge cannot be read on real operators.  Nothing needs it to be: the certificate
`RestrictedDisplacementApproximationDominance` and the bridge
`restrictedDisplacement_idealGauge_le` are both `RCLike`-generic, so a real
certificate feeds a real family directly.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 4, Propositions 4.1 and
  4.3 and Corollary 4.1, and standing assumption 1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Real form of the abstract spectral-cutoff argument used by Proposition 4.1.  Complexification
preserves approximation numbers and all three quadratic estimates; the only nonlinear step is the
two-coordinate Cauchy--Schwarz inequality for `‖Cz‖ ‖z‖`. -/
private theorem real_approximationNumber_direct_le_competitor
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (C : X →L[ℝ] X) (A B : X →L[ℝ] Y)
    (hCsa : C.IsSymmetric)
    (hCpos : ∀ x, 0 ≤ inner ℝ (C x) x)
    (hAnorm : ‖A‖ ≤ Real.sqrt 2)
    (hAsq : ∀ x, ‖A x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * inner ℝ (C x) x)
    (hBsq : ∀ x, 2 * ‖x‖ ^ 2 - 2 * ‖C x‖ * ‖x‖ ≤ ‖B x‖ ^ 2)
    (n : ℕ) : A.approximationNumber n ≤ B.approximationNumber n := by
  let D : TauCeti.DavisKahan.Section4.CosineDisplacementData
      (complexify C) (complexify A) (complexify B) := {
    cosine_selfAdjoint :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        ((complexify_isSelfAdjoint_iff C).2
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hCsa))
    cosine_nonnegative := by
      intro z
      rw [TauCeti.DavisKahan.Foundation.RealComplexification.re_inner_complexify]
      exact add_nonneg (hCpos _) (hCpos _)
    direct_norm_le_sqrt_two := by simpa only [norm_complexify] using hAnorm
    direct_norm_sq := by
      intro z
      rw [TauCeti.RealComplexification.norm_sq,
        TauCeti.DavisKahan.Foundation.RealComplexification.re_inner_complexify,
        TauCeti.RealComplexification.norm_sq]
      change ‖A (TauCeti.RealComplexification.re z)‖ ^ 2 +
          ‖A (TauCeti.RealComplexification.im z)‖ ^ 2 = _
      rw [hAsq, hAsq]
      ring
    competitor_norm_sq_lower := by
      intro z
      have hx := hBsq (TauCeti.RealComplexification.re z)
      have hy := hBsq (TauCeti.RealComplexification.im z)
      have hcs :
          ‖C (TauCeti.RealComplexification.re z)‖ *
              ‖TauCeti.RealComplexification.re z‖ +
            ‖C (TauCeti.RealComplexification.im z)‖ *
              ‖TauCeti.RealComplexification.im z‖ ≤
            ‖complexify C z‖ * ‖z‖ := by
        have hsq :
            (‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.re z‖ +
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.im z‖) ^ 2 ≤
              (‖complexify C z‖ * ‖z‖) ^ 2 := by
          rw [mul_pow, TauCeti.RealComplexification.norm_sq,
            TauCeti.RealComplexification.norm_sq]
          change _ ≤
            (‖C (TauCeti.RealComplexification.re z)‖ ^ 2 +
              ‖C (TauCeti.RealComplexification.im z)‖ ^ 2) *
            (‖TauCeti.RealComplexification.re z‖ ^ 2 +
              ‖TauCeti.RealComplexification.im z‖ ^ 2)
          nlinarith [sq_nonneg
            (‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.im z‖ -
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.re z‖)]
        have hleft : 0 ≤
            ‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.re z‖ +
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.im z‖ := by positivity
        have hright : 0 ≤ ‖complexify C z‖ * ‖z‖ := by positivity
        exact (sq_le_sq₀ hleft hright).1 hsq
      rw [TauCeti.RealComplexification.norm_sq,
        TauCeti.RealComplexification.norm_sq]
      simp only [re_complexify, im_complexify]
      nlinarith }
  rw [← approximationNumber_complexify, ← approximationNumber_complexify]
  exact D.approximationNumber_direct_le_competitor n


/-- Real form of the exact direct/sine cutoff identity.  Complexification
preserves both approximation-number sequences and the quadratic source model. -/
private theorem real_approximationNumber_direct_cosineCutoff_eq_sine
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (C : X →L[ℝ] X) (A B S : X →L[ℝ] Y)
    (hCsa : C.IsSymmetric)
    (hCpos : ∀ x, 0 <= inner ℝ (C x) x)
    (hAnorm : ‖A‖ <= Real.sqrt 2)
    (hAsq : ∀ x, ‖A x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * inner ℝ (C x) x)
    (hBsq : ∀ x, 2 * ‖x‖ ^ 2 - 2 * ‖C x‖ * ‖x‖ <= ‖B x‖ ^ 2)
    (hSsq : ∀ x, ‖S x‖ ^ 2 = ‖x‖ ^ 2 - ‖C x‖ ^ 2)
    (n : ℕ) :
    1 - ((A.approximationNumber n : Real) ^ 2) / 2 =
      Real.sqrt (1 - ((S.approximationNumber n : Real) ^ 2)) := by
  let D : TauCeti.DavisKahan.Section4.CosineDisplacementData
      (complexify C) (complexify A) (complexify B) := {
    cosine_selfAdjoint :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        ((complexify_isSelfAdjoint_iff C).2
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hCsa))
    cosine_nonnegative := by
      intro z
      rw [TauCeti.DavisKahan.Foundation.RealComplexification.re_inner_complexify]
      exact add_nonneg (hCpos _) (hCpos _)
    direct_norm_le_sqrt_two := by simpa only [norm_complexify] using hAnorm
    direct_norm_sq := by
      intro z
      rw [TauCeti.RealComplexification.norm_sq,
        TauCeti.DavisKahan.Foundation.RealComplexification.re_inner_complexify,
        TauCeti.RealComplexification.norm_sq]
      change ‖A (TauCeti.RealComplexification.re z)‖ ^ 2 +
          ‖A (TauCeti.RealComplexification.im z)‖ ^ 2 = _
      rw [hAsq, hAsq]
      ring
    competitor_norm_sq_lower := by
      intro z
      have hx := hBsq (TauCeti.RealComplexification.re z)
      have hy := hBsq (TauCeti.RealComplexification.im z)
      have hcs :
          ‖C (TauCeti.RealComplexification.re z)‖ *
              ‖TauCeti.RealComplexification.re z‖ +
            ‖C (TauCeti.RealComplexification.im z)‖ *
              ‖TauCeti.RealComplexification.im z‖ <=
            ‖complexify C z‖ * ‖z‖ := by
        have hsq :
            (‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.re z‖ +
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.im z‖) ^ 2 <=
              (‖complexify C z‖ * ‖z‖) ^ 2 := by
          rw [mul_pow, TauCeti.RealComplexification.norm_sq,
            TauCeti.RealComplexification.norm_sq]
          change _ <=
            (‖C (TauCeti.RealComplexification.re z)‖ ^ 2 +
              ‖C (TauCeti.RealComplexification.im z)‖ ^ 2) *
            (‖TauCeti.RealComplexification.re z‖ ^ 2 +
              ‖TauCeti.RealComplexification.im z‖ ^ 2)
          nlinarith [sq_nonneg
            (‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.im z‖ -
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.re z‖)]
        have hleft : 0 <=
            ‖C (TauCeti.RealComplexification.re z)‖ *
                ‖TauCeti.RealComplexification.re z‖ +
              ‖C (TauCeti.RealComplexification.im z)‖ *
                ‖TauCeti.RealComplexification.im z‖ := by positivity
        have hright : 0 <= ‖complexify C z‖ * ‖z‖ := by positivity
        exact (sq_le_sq₀ hleft hright).1 hsq
      rw [TauCeti.RealComplexification.norm_sq,
        TauCeti.RealComplexification.norm_sq]
      simp only [re_complexify, im_complexify]
      nlinarith }
  have hSsqC : ∀ z,
      ‖complexify S z‖ ^ 2 = ‖z‖ ^ 2 - ‖complexify C z‖ ^ 2 := by
    intro z
    rw [TauCeti.RealComplexification.norm_sq, TauCeti.RealComplexification.norm_sq,
      TauCeti.RealComplexification.norm_sq]
    simp only [re_complexify, im_complexify]
    rw [hSsq, hSsq]
    ring
  have h :=
    TauCeti.DavisKahan.Section4.CosineDisplacementData.approximationNumber_direct_cosineCutoff_eq_sine
      D (S := complexify S) hSsqC n
  simpa only [approximationNumber_complexify] using h

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

local instance sourceCompleteSpaceR : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-! ### Real source-coordinate model -/

/-- The positive real Halmos cosine restricted to source coordinates. -/
noncomputable def sourceCosineR : U →L[ℝ] U := by
  let C := TauCeti.DavisKahan.canonicalAbsoluteValueR U V
  have hcomm : Commute C (U.starProjection) := by
    refine TauCeti.RealComplexification.complexify_injective ?_
    rw [TauCeti.DavisKahan.complexify_mul,
      TauCeti.DavisKahan.complexify_mul,
      TauCeti.DavisKahan.complexify_canonicalAbsoluteValueR,
      TauCeti.DavisKahan.complexify_projection]
    exact (TauCeti.DavisKahan.spectraCanonicalAbsoluteValue_commute_projection
      (complexifySubmodule U) (complexifySubmodule V)).eq
  have hCU : TauCeti.DavisKahan.Foundation.InvariantFor C U := by
    intro x hx
    apply U.starProjection_eq_self_iff.mp
    have happ := congrArg (fun T : E →L[ℝ] E => T x) hcomm.eq
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hx] at happ
    exact happ.symm
  exact C.restrict hCU

/-- Restricted displacement with a real source-coordinate domain. -/
noncomputable def sourceRestrictedDisplacementR (T : E →L[ℝ] E) : U →L[ℝ] E :=
  (1 - T) ∘L U.subtypeL

/-- Evaluating the real source cosine block, in ambient coordinates. -/
@[simp]
theorem sourceCosineR_apply_coe (x : U) :
    ((sourceCosineR U V x : U) : E) =
      TauCeti.DavisKahan.canonicalAbsoluteValueR U V (x : E) :=
  rfl

/-- The restricted real Halmos cosine is symmetric and nonnegative. -/
theorem sourceCosineR_selfAdjoint : (sourceCosineR U V).IsSymmetric := by
  intro x y
  change ⟪TauCeti.DavisKahan.canonicalAbsoluteValueR U V (x : E), (y : E)⟫_ℝ =
    ⟪(x : E), TauCeti.DavisKahan.canonicalAbsoluteValueR U V (y : E)⟫_ℝ
  exact (TauCeti.DavisKahan.isPositive_canonicalAbsoluteValueR U V).inner_left_eq_inner_right
    (x : E) (y : E)

/-- The real source cosine block is a nonnegative operator. -/
theorem sourceCosineR_nonnegative (x : U) :
    0 ≤ inner ℝ (sourceCosineR U V x) x := by
  change 0 ≤ ⟪TauCeti.DavisKahan.canonicalAbsoluteValueR U V (x : E), (x : E)⟫_ℝ
  exact (TauCeti.DavisKahan.isPositive_canonicalAbsoluteValueR U V).inner_nonneg_left _

/-- The real functional-calculus modulus agrees with the conjugation-descended modulus. -/
theorem spectraAbsoluteValue_canonicalIntertwinerR_eq :
    ContinuousLinearMap.modulus
        (TauCeti.DavisKahan.canonicalIntertwinerR U V) =
      TauCeti.DavisKahan.canonicalAbsoluteValueR U V := by
  have hsquare :
      TauCeti.DavisKahan.canonicalAbsoluteValueR U V *
          TauCeti.DavisKahan.canonicalAbsoluteValueR U V =
        star (TauCeti.DavisKahan.canonicalIntertwinerR U V) *
          TauCeti.DavisKahan.canonicalIntertwinerR U V := by
    refine TauCeti.RealComplexification.complexify_injective ?_
    rw [TauCeti.DavisKahan.complexify_mul, TauCeti.DavisKahan.complexify_mul,
      TauCeti.DavisKahan.complexify_star,
      TauCeti.DavisKahan.complexify_canonicalAbsoluteValueR,
      TauCeti.DavisKahan.complexify_canonicalIntertwinerR]
    exact ContinuousLinearMap.modulus_mul_self_eq_star_mul_self _
  have h := ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (T := TauCeti.DavisKahan.canonicalIntertwinerR U V)
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
      (TauCeti.DavisKahan.isPositive_canonicalAbsoluteValueR U V))
    (by simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.star_eq_adjoint] using hsquare)
  exact h.symm

/-- The real source cosine has the length of the target projection. -/
theorem norm_sourceCosineR_eq_norm_targetProjection (x : U) :
    ‖sourceCosineR U V x‖ = ‖V.starProjection (x : E)‖ := by
  have h := TauCeti.DavisKahan.Section4.norm_absoluteValue_apply_eq_norm_projection
    (complexifySubmodule U) (complexifySubmodule V)
    ((ofReal_mem_complexifySubmodule_iff U _).2 x.property)
  change ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V (x : E)‖ = _
  rw [← TauCeti.DavisKahan.complexify_canonicalAbsoluteValueR,
    ← TauCeti.DavisKahan.complexify_projection,
    complexify_ofReal, complexify_ofReal,
    ofReal.norm_map, ofReal.norm_map] at h
  exact h

/-- Squared displacement identity for a real orthogonal operator. -/
private theorem norm_sub_one_apply_sq_of_mem_unitary_real
    (T : E →L[ℝ] E) (hT : T ∈ unitary (E →L[ℝ] E)) (x : E) :
    ‖(T - 1) x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * inner ℝ (T x) x := by
  have hnorm : ‖T x‖ = ‖x‖ :=
    Unitary.norm_map (⟨T, hT⟩ : unitary (E →L[ℝ] E)) x
  rw [sub_apply, one_apply_eq_self, norm_sub_sq (𝕜 := ℝ), hnorm]
  simp only [RCLike.re_to_real]
  ring

/-- The completed nonacute real rotation has the positive-cosine quadratic model. -/
theorem sourceRestrictedDisplacementR_nonacute_norm_sq
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V) (x : U) :
    ‖sourceRestrictedDisplacementR U
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J) x‖ ^ 2 =
      2 * ‖x‖ ^ 2 - 2 * inner ℝ (sourceCosineR U V x) x := by
  let D : E →L[ℝ] E := TauCeti.DavisKahan.nonacuteDirectRotation U V J
  have hdisp := norm_sub_one_apply_sq_of_mem_unitary_real D
    (TauCeti.DavisKahan.nonacuteDirectRotation_mem_unitary U V J) (x : E)
  have hform := TauCeti.DavisKahan.re_inner_nonacuteDirectRotation_eq_absoluteValue
    U V J (x : E)
  change ‖(1 - D) (x : E)‖ ^ 2 = _
  have hneg : (1 - D) (x : E) = -((D - 1) (x : E)) := by simp
  rw [hneg, norm_neg, hdisp]
  change 2 * ‖(x : E)‖ ^ 2 - 2 * inner ℝ (D (x : E)) (x : E) = _
  dsimp only [D]
  change 2 * ‖(x : E)‖ ^ 2 -
      2 * inner ℝ (TauCeti.DavisKahan.nonacuteDirectRotation U V J (x : E)) (x : E) =
    2 * ‖x‖ ^ 2 -
      2 * inner ℝ (TauCeti.DavisKahan.canonicalAbsoluteValueR U V (x : E)) (x : E)
  have hT : TauCeti.DavisKahan.spectraCanonicalIntertwiner U V =
      TauCeti.DavisKahan.canonicalIntertwinerR U V := rfl
  rw [hT, spectraAbsoluteValue_canonicalIntertwinerR_eq] at hform
  have hxnorm : ‖(x : E)‖ = ‖x‖ := rfl
  simpa only [RCLike.re_to_real, hxnorm] using congrArg
      (fun r : ℝ => 2 * ‖(x : E)‖ ^ 2 - 2 * r) hform

/-- A real orthogonal competitor has the lower quadratic displacement estimate. -/
theorem sourceRestrictedDisplacementR_competitor_norm_sq_lower
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (x : U) :
    2 * ‖x‖ ^ 2 - 2 * ‖sourceCosineR U V x‖ * ‖x‖ ≤
      ‖sourceRestrictedDisplacementR U W x‖ ^ 2 := by
  have hWxV : W (x : E) ∈ V := by
    apply V.starProjection_eq_self_iff.mp
    have happ := congrArg (fun T : E →L[ℝ] E => T (x : E)) hWmap
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr x.property] at happ
    exact happ.symm
  have hinner : inner ℝ (W (x : E)) (x : E) ≤
      ‖sourceCosineR U V x‖ * ‖x‖ := by
    calc
      inner ℝ (W (x : E)) (x : E) =
          inner ℝ (W (x : E)) (V.starProjection (x : E)) := by
        rw [← V.inner_starProjection_left_eq_right]
        rw [Submodule.starProjection_eq_self_iff.mpr hWxV]
      _ ≤ ‖W (x : E)‖ * ‖V.starProjection (x : E)‖ :=
        real_inner_le_norm _ _
      _ = ‖sourceCosineR U V x‖ * ‖x‖ := by
        rw [norm_sourceCosineR_eq_norm_targetProjection U V]
        rw [Unitary.norm_map (⟨W, hWunitary⟩ : unitary (E →L[ℝ] E))]
        exact mul_comm _ _
  have hdisp := norm_sub_one_apply_sq_of_mem_unitary_real W hWunitary (x : E)
  change _ ≤ ‖(1 - W) (x : E)‖ ^ 2
  have hneg : (1 - W) (x : E) = -((W - 1) (x : E)) := by simp
  rw [hneg, norm_neg, hdisp]
  have hxnorm : ‖(x : E)‖ = ‖x‖ := rfl
  rw [hxnorm]
  linarith

/-- Source-coordinate approximation-number dominance for the chosen real nonacute rotation. -/
theorem proposition4_1_nonacute_real
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (n : ℕ) :
    (sourceRestrictedDisplacementR U
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J)).approximationNumber n ≤
      (sourceRestrictedDisplacementR U W).approximationNumber n := by
  apply real_approximationNumber_direct_le_competitor
      (sourceCosineR U V)
      (sourceRestrictedDisplacementR U
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J))
      (sourceRestrictedDisplacementR U W)
      (sourceCosineR_selfAdjoint U V) (sourceCosineR_nonnegative U V)
      _ (sourceRestrictedDisplacementR_nonacute_norm_sq U V J)
      (sourceRestrictedDisplacementR_competitor_norm_sq_lower U V W hWunitary hWmap) n
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun x => ?_
  have hsq := sourceRestrictedDisplacementR_nonacute_norm_sq U V J x
  have hpos := sourceCosineR_nonnegative U V x
  have hroot : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hleft := norm_nonneg
    (sourceRestrictedDisplacementR U
      (TauCeti.DavisKahan.nonacuteDirectRotation U V J) x)
  have hright : 0 ≤ Real.sqrt 2 * ‖x‖ := by positivity
  apply (sq_le_sq₀ hleft hright).1
  rw [hsq, mul_pow, hroot]
  nlinarith

/-- Extending the real source-coordinate displacement by zero gives the ambient restriction. -/
theorem sourceRestrictedDisplacementR_extendDomainByZero (T : E →L[ℝ] E) :
    sourceRestrictedDisplacementR U T ∘L U.subtypeL.adjoint =
      (1 - T) ∘L U.starProjection := by
  ext x
  simp [sourceRestrictedDisplacementR, Submodule.adjoint_subtypeL]

/-- The real source and ambient restricted displacements have the same approximation sequence. -/
theorem sourceRestrictedDisplacementR_sameApproximationSingularSequence (T : E →L[ℝ] E) :
    SameApproximationSingularSequence
      ((1 - T) ∘L U.starProjection) (sourceRestrictedDisplacementR U T) := by
  intro n
  rw [← sourceRestrictedDisplacementR_extendDomainByZero U T]
  exact sameApproximationSingularValues_extendDomainByZero U
    (sourceRestrictedDisplacementR U T) n

/-- **Proposition 4.1 over `ℝ` at the exact matched-defect, nonacute scope.** -/
theorem Proposition4_1_nonacute_real
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (n : ℕ) :
    ContinuousLinearMap.approximationNumber
        ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) n ≤
      ContinuousLinearMap.approximationNumber
        ((1 - W) ∘L U.starProjection) n := by
  have hsource := proposition4_1_nonacute_real U V J W hWunitary hWmap n
  have hD := sourceRestrictedDisplacementR_sameApproximationSingularSequence U
    (TauCeti.DavisKahan.nonacuteDirectRotation U V J) n
  have hW := sourceRestrictedDisplacementR_sameApproximationSingularSequence U W n
  change approximationSingularValue n
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection) ≤
    approximationSingularValue n ((1 - W) ∘L U.starProjection)
  calc
    _ = approximationSingularValue n
        (sourceRestrictedDisplacementR U
          (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) := hD
    _ ≤ approximationSingularValue n (sourceRestrictedDisplacementR U W) := by
      simpa only [approximationSingularValue] using hsource
    _ = _ := hW.symm

/-- The nonacute real Proposition 4.1 dominance certificate. -/
theorem restrictedDisplacementDominance_nonacute_real
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    TauCeti.DavisKahan.Section4.RestrictedDisplacementApproximationDominance
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection)
      ((1 - W) ∘L U.starProjection) where
  approximation_le n := Proposition4_1_nonacute_real U V J W hWunitary hWmap n

/-- **Corollary 4.1 over `ℝ` at the exact matched-defect, nonacute scope.** -/
theorem Corollary4_1_nonacute_real (N : FanDominantIdealFamily (𝕜 := ℝ))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection) ∧
      N.gauge ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  TauCeti.DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (restrictedDisplacementDominance_nonacute_real U V J W hWunitary hWmap) hWmem

/-! ### Transport of the two displacement shapes -/

omit [CompleteSpace E] in
/-- The restricted displacement of a complexified operator is the
complexification of the real restricted displacement. -/
theorem complexify_restrictedDisplacement (W : E →L[ℝ] E) :
    complexify ((1 - W) ∘L U.starProjection) =
      (1 - complexify W) ∘L Submodule.starProjection (complexifySubmodule U) := by
  rw [complexify_comp, complexify_sub, TauCeti.DavisKahan.complexify_one,
    TauCeti.DavisKahan.complexify_projection]

/-- The squared full displacement of a complexified operator is the
complexification of the real one. -/
theorem complexify_displacementSquare (W : E →L[ℝ] E) :
    complexify ((1 - star W) * (1 - W)) =
      (1 - star (complexify W)) * (1 - complexify W) := by
  rw [TauCeti.DavisKahan.complexify_mul, complexify_sub, complexify_sub, TauCeti.DavisKahan.complexify_one,
    TauCeti.DavisKahan.complexify_star]

omit [CompleteSpace E] in
/-- A real intertwining relation complexifies. -/
theorem complexify_intertwines {W : E →L[ℝ] E}
    (hWmap : W * U.starProjection = V.starProjection * W) :
    complexify W * Submodule.starProjection (complexifySubmodule U) =
      Submodule.starProjection (complexifySubmodule V) * complexify W := by
  rw [← TauCeti.DavisKahan.complexify_projection, ← TauCeti.DavisKahan.complexify_projection,
    ← TauCeti.DavisKahan.complexify_mul, ← TauCeti.DavisKahan.complexify_mul, hWmap]

/-! ### Proposition 4.1 -/

/-- **Davis--Kahan 1970, Proposition 4.1, over a real Hilbert space of arbitrary
dimension.**

For every orthogonal `W` on a real Hilbert space carrying `U` onto `V`, every
approximation number of the displacement restricted to `U` is minimized by the
real direct rotation.  Approximation numbers stand in for singular values, which
is the correct reading past the compact case. -/
theorem proposition4_1_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (n : ℕ) :
    ContinuousLinearMap.approximationNumber
        ((1 - TauCeti.DavisKahan.directRotationR U V hacute) ∘L U.starProjection) n ≤
      ContinuousLinearMap.approximationNumber ((1 - W) ∘L U.starProjection) n := by
  rw [← approximationNumber_complexify, ← approximationNumber_complexify,
    complexify_restrictedDisplacement, complexify_restrictedDisplacement,
    TauCeti.DavisKahan.complexify_directRotationR]
  exact TauCeti.DavisKahan.Section4.proposition4_1_restrictedDisplacement_approximationNumbers
    (complexifySubmodule U) (complexifySubmodule V)
    (TauCeti.DavisKahan.isUniformlyAcute_complexifySubmodule U V hacute) (complexify W)
    (TauCeti.DavisKahan.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap) n

/-- The Proposition 4.1 certificate for a real pair, in the shape the ideal
bridge consumes. -/
theorem restrictedDisplacementDominance_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    TauCeti.DavisKahan.Section4.RestrictedDisplacementApproximationDominance
      ((1 - TauCeti.DavisKahan.directRotationR U V hacute) ∘L U.starProjection)
      ((1 - W) ∘L U.starProjection) where
  approximation_le n := proposition4_1_real U V hacute W hWunitary hWmap n

/-! ### Corollary 4.1 -/

/-- **Davis--Kahan 1970, Corollary 4.1, over a real Hilbert space of arbitrary
dimension.**

For every Ky-Fan-dominant symmetric ideal family of operators on real Hilbert
spaces, the real direct rotation's restricted displacement lies in the ideal and
its gauge is least among all orthogonal `W` carrying `U` onto `V`.  Membership is
concluded. -/
theorem corollary4_1_real (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - TauCeti.DavisKahan.directRotationR U V hacute) ∘L U.starProjection) ∧
      N.gauge ((1 - TauCeti.DavisKahan.directRotationR U V hacute) ∘L U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  TauCeti.DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (restrictedDisplacementDominance_real U V hacute W hWunitary hWmap) hWmem

/-- The operator-norm specialization of Corollary 4.1 over `ℝ`. -/
theorem corollary4_1_opNorm_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ‖(1 - TauCeti.DavisKahan.directRotationR U V hacute) ∘L U.starProjection‖ ≤
      ‖(1 - W) ∘L U.starProjection‖ :=
  TauCeti.DavisKahan.Section4.restrictedDisplacement_opNorm_le
    (restrictedDisplacementDominance_real U V hacute W hWunitary hWmap)

/-! ### Proposition 4.2 -/

/-- The squared sine of the angle between a unit vector and its displacement
under a real orthogonal operator. -/
def displacementAngleSineSqR (W : E →L[ℝ] E) (x : E) : ℝ :=
  1 - ⟪x, W x⟫_ℝ ^ 2

omit [CompleteSpace E] in
/-- The real displacement-angle cost is the complex one evaluated on the real
copy. -/
theorem displacementAngleSineSq_complexify (W : E →L[ℝ] E) (x : E) :
    TauCeti.DavisKahan.Section4.displacementAngleSineSq (complexify W) (ofReal x) =
      displacementAngleSineSqR W x := by
  rw [TauCeti.DavisKahan.Section4.displacementAngleSineSq, displacementAngleSineSqR, complexify_ofReal,
    inner_ofReal]
  norm_num

/-- **Davis--Kahan 1970, Proposition 4.2, termwise, over a real Hilbert space of
arbitrary dimension.** -/
theorem displacementAngleSineSq_ge_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    {x : E} (hx : x ∈ U) (hxnorm : ‖x‖ = 1) :
    1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V x‖ ^ 2 ≤
      displacementAngleSineSqR W x := by
  have h := TauCeti.DavisKahan.Section4.displacementAngleSineSq_ge_complex
    (complexifySubmodule U) (complexifySubmodule V)
    (complexify W) (TauCeti.DavisKahan.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap)
    ((ofReal_mem_complexifySubmodule_iff U x).2 hx)
    (by rw [ofReal.norm_map]; exact hxnorm)
  rwa [displacementAngleSineSq_complexify,
    ← TauCeti.DavisKahan.complexify_canonicalAbsoluteValueR, complexify_ofReal,
    ofReal.norm_map] at h

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space**, on an
arbitrary finite subfamily of unit vectors of `U`.  As over `ℂ`, orthonormality
is what makes the two sides the paper's energies, not what makes the estimate
true. -/
theorem sum_displacementAngleSineSq_ge_of_mem_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    {ι : Type*} (b : ι → E) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1)
    (s : Finset ι) :
    ∑ i ∈ s, (1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V (b i)‖ ^ 2) ≤
      ∑ i ∈ s, displacementAngleSineSqR W (b i) :=
  Finset.sum_le_sum fun i _ =>
    displacementAngleSineSq_ge_real U V W hWunitary hWmap (hb i) (hbnorm i)

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space, with no
summability convention.**  Both sums are unconditionally defined in `ℝ≥0∞` and
the index type is arbitrary. -/
theorem tsum_displacementAngleSineSq_ge_of_mem_real
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    {ι : Type*} (b : ι → E) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1) :
    ∑' i, ENNReal.ofReal (1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V (b i)‖ ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W (b i)) :=
  ENNReal.tsum_le_tsum fun i =>
    ENNReal.ofReal_le_ofReal
      (displacementAngleSineSq_ge_real U V W hWunitary hWmap (hb i) (hbnorm i))

/-! ### The printed right-hand side over `ℝ`

`sum_displacementAngleSineSq_ge_of_mem_real` bounds the competitor's energy below
by `∑ᵢ (1 - ‖C_ℝ bᵢ‖²)`; the paper prints `∑ₖ sin² θₖ`.  The identification is the
one used over `ℂ`, transported by the same complexification the rest of this
module uses: `‖C_ℝ x‖ = ‖P_V x‖` on `U`, then the Pythagorean basis reading
`TauCeti.sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection`, which is
`RCLike`-generic and so applies at `ℝ` unchanged.

Two traps recorded on the complex side apply verbatim here.  Sorted decreasingly,
`sin² θ` is the **reverse** of `1 - cos² θ`, so no termwise cosine-to-sine
identity is available — only the sums agree.  And the `dim U - tr((C|_U)²)` route
would need the eigenvalues of the compression `C|_U`, which nothing supplies:
`∑ᵢ ‖C bᵢ‖² = tr(C⋆C)` holds for a basis of the *whole* space, not for a basis of
`U`. -/

/-- **On a source vector the real Halmos cosine has the length of the target
projection**: `‖C_ℝ x‖ = ‖P_V x‖` for `x ∈ U`.

This is `norm_absoluteValue_apply_eq_norm_projection` read on the real copy: the
complexified real modulus is the modulus of the complexified pair, and both the
projection and the vector complexify isometrically. -/
theorem norm_canonicalAbsoluteValueR_apply_eq_norm_projection {x : E} (hx : x ∈ U) :
    ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V x‖ = ‖V.starProjection x‖ := by
  have h := TauCeti.DavisKahan.Section4.norm_absoluteValue_apply_eq_norm_projection
    (complexifySubmodule U) (complexifySubmodule V)
    ((ofReal_mem_complexifySubmodule_iff U x).2 hx)
  rw [← TauCeti.DavisKahan.complexify_canonicalAbsoluteValueR,
    ← TauCeti.DavisKahan.complexify_projection, complexify_ofReal, complexify_ofReal,
    ofReal.norm_map, ofReal.norm_map] at h
  exact h

/-- **The right-hand side of Proposition 4.2 over `ℝ` is `∑ₖ sin² θₖ`.**

For every orthonormal basis `b` of a real `U`,

  `∑ᵢ (1 - ‖C_ℝ bᵢ‖²) = ∑ₖ sin² θₖ`,

with `C_ℝ` the real positive Halmos cosine and `sin θₖ` the principal sines of
`(U, V)` — the singular values of `P_{Vᗮ} P_U`.  In particular the left side does
not depend on the basis, which is what the paper's basis-free statement asserts.

This is the finite-dimensional compatibility form of the arbitrary-dimensional
identity `tsum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_tsum_sq_principalSineSequence`.
It uses `TauCeti.principalSines` and a basis indexed by `Fin (finrank ℝ U)`. -/
theorem sum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_sum_sq_principalSines
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ U) :
    ∑ i, (1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V ((b i : U) : E)‖ ^ 2) =
      ∑ i : Fin (Module.finrank ℝ U),
        TauCeti.principalSines U V (i : ℕ) ^ 2 := by
  rw [TauCeti.sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection U V b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_canonicalAbsoluteValueR_apply_eq_norm_projection U V (b i).2]
  -- the two spellings of the orthogonal projector: the bounded-operator
  -- `DavisKahan.projection` and the linear-map `TauCeti.projection`
  rfl

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space, with the
printed right-hand side.**

For every orthonormal basis of `U` and every orthogonal `W` carrying `U` onto `V`,

  `∑ᵢ sin²(bᵢ, W bᵢ)  ≥  ∑ₖ sin² θₖ`.

This is the finite-dimensional compatibility form of
`tsum_displacementAngleSineSqR_ge_tsum_sq_principalSineSequence`, expressed with
the existing `TauCeti.principalSines` list. -/
theorem sum_displacementAngleSineSqR_ge_sum_sq_principalSines
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∑ i : Fin (Module.finrank ℝ U), TauCeti.principalSines U V (i : ℕ) ^ 2 ≤
      ∑ i, displacementAngleSineSqR W ((b i : U) : E) := by
  rw [← sum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_sum_sq_principalSines U V b]
  refine sum_displacementAngleSineSq_ge_of_mem_real U V W hWunitary hWmap
    (fun i => ((b i : U) : E)) (fun i => (b i).2) (fun i => ?_) Finset.univ
  have h : ‖((b i : U) : E)‖ = ‖(b i : U)‖ := rfl
  rw [h]
  exact b.orthonormal.1 i

/-! ### Proposition 4.2 with the infinite principal-sine sequence -/

/-- On a unit real source vector, the basis-free Proposition 4.2 summand is the
squared norm of the directed sine operator. -/
theorem ofReal_one_sub_sq_norm_canonicalAbsoluteValueR_eq_enorm_principalSineOperator
    {x : E} (hx : x ∈ U) (hxnorm : ‖x‖ = 1) :
    ENNReal.ofReal (1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V x‖ ^ 2) =
      ‖TauCeti.principalSineOperator U V ⟨x, hx⟩‖ₑ ^ 2 := by
  have hC := norm_canonicalAbsoluteValueR_apply_eq_norm_projection U V hx
  have hpy := V.norm_sq_eq_add_norm_sq_starProjection x
  have hreal :
      1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V x‖ ^ 2 =
        ‖Vᗮ.starProjection x‖ ^ 2 := by
    rw [hxnorm, one_pow] at hpy
    rw [hC]
    linarith
  rw [hreal, TauCeti.principalSineOperator_apply]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- For every Hilbert basis of a real source subspace, the basis-free energy in
Proposition 4.2 is the squared principal-sine sequence, including the divergent
case. -/
theorem tsum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_tsum_sq_principalSineSequence
    {ι : Type v} (b : HilbertBasis ι ℝ U) :
    (∑' i, ENNReal.ofReal
        (1 - ‖TauCeti.DavisKahan.canonicalAbsoluteValueR U V ((b i : U) : E)‖ ^ 2)) =
      ∑' n : ℕ, ENNReal.ofReal (TauCeti.principalSineSequence U V n) ^ 2 := by
  rw [TauCeti.tsum_sq_principalSineSequence_eq_tsum_enorm_projection U V b]
  refine tsum_congr fun i => ?_
  exact ofReal_one_sub_sq_norm_canonicalAbsoluteValueR_eq_enorm_principalSineOperator
    U V (b i).property (b.orthonormal.1 i)

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space, in arbitrary
Hilbert dimension with the printed right-hand side.**

The extended-real sums include the case where the sum of squared principal
sines is infinite. -/
theorem tsum_displacementAngleSineSqR_ge_tsum_sq_principalSineSequence
    {ι : Type v} (b : HilbertBasis ι ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal (TauCeti.principalSineSequence U V n) ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W ((b i : U) : E)) := by
  rw [← tsum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_tsum_sq_principalSineSequence
    U V b]
  exact tsum_displacementAngleSineSq_ge_of_mem_real U V W hWunitary hWmap
    (fun i => ((b i : U) : E)) (fun i => (b i).property)
    (fun i => b.orthonormal.1 i)

/-- **Davis--Kahan 1970, Proposition 4.2 over a real Hilbert space, literal
principal-angle form.**

For every Hilbert basis of `U` and every orthogonal `W` carrying `U` onto `V`,
the total squared displacement sine dominates `∑ₙ sin² θₙ`.  The extended-real
form includes a divergent right-hand side. -/
theorem tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence
    {ι : Type v} (b : HilbertBasis ι ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W ((b i : U) : E)) := by
  rw [TauCeti.tsum_sq_sin_principalAngleSequence_eq_tsum_sq_principalSineSequence]
  exact tsum_displacementAngleSineSqR_ge_tsum_sq_principalSineSequence
    U V b W hWunitary hWmap

/-- **Davis--Kahan 1970, Proposition 4.2, real scalars, carrying the Section 4
setup it is printed under.**

The real analogue of `proposition4_2_compact_nonacute`.  Section 4 opens
by fixing the compact/classification setup, and Proposition 4.2 is printed under
it without restating it; the inherited hypotheses are carried here explicitly and
discharged by the stronger theorem, which needs neither.  They are underscored
because the proof does not consume them, following this tree's convention for
retained source hypotheses. -/
theorem proposition4_2_compact_nonacute_real
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (_hcrossed : CrossedDefectsEquivalent U V)
    {ι : Type v} (b : HilbertBasis ι ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W ((b i : U) : E)) :=
  tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence
    U V b W hWunitary hWmap

/-! ### Proposition 4.3 -/

/-- The Gram operator of a real bounded map. -/
private noncomputable def gramOperatorR {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) : X →L[ℝ] X := A.adjoint ∘L A

/-- Gram operators commute with real-to-complex scalar extension. -/
private theorem complexify_gramOperator_real {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) :
    complexify (gramOperatorR A) = gramOperator (complexify A) := by
  rw [gramOperatorR, gramOperator, complexify_comp, complexify_adjoint]

/-- The Gram-square approximation-number identity over `ℝ`, descended from the complex one. -/
private theorem approximationNumber_gramOperator_real {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (n : ℕ) :
    (gramOperatorR A).approximationNumber n = A.approximationNumber n ^ 2 := by
  rw [← approximationNumber_complexify, complexify_gramOperator_real,
    TauCeti.ApproximationNumber.approximationNumber_gramOperator_complex,
    approximationNumber_complexify]

/-- Ky Fan gauges of real Gram operators inherit pointwise approximation dominance. -/
private theorem kyFanApproximationGauge_gramOperator_mono_real {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (A : X →L[ℝ] Y) (B : X →L[ℝ] Z)
    (h : ∀ n, A.approximationNumber n ≤ B.approximationNumber n) (k : ℕ) :
    kyFanApproximationGauge k (gramOperatorR A) ≤
      kyFanApproximationGauge k (gramOperatorR B) := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  refine Finset.sum_le_sum fun n _ => ?_
  rw [approximationNumber_gramOperator_real, approximationNumber_gramOperator_real]
  nlinarith [h n, A.approximationNumber_nonneg n]

omit [CompleteSpace E] in
/-- Even reflection blocks commute with scalar extension. -/
private theorem diagonalPart_complexify_real (A : E →L[ℝ] E) :
    (complexifySubmodule U).diagonalPart (complexify A) =
      complexify (U.diagonalPart A) := by
  rw [Submodule.diagonalPart_eq, Submodule.diagonalPart_eq,
    starProjection_complexifySubmodule, starProjection_complexifySubmodule_orthogonal,
    complexify_add, complexify_comp, complexify_comp, complexify_comp, complexify_comp]

/-- Pinching contracts every real Ky Fan approximation gauge. -/
private theorem kyFanApproximationGauge_diagonalPart_le_real
    (A : E →L[ℝ] E) (k : ℕ) :
    kyFanApproximationGauge k (U.diagonalPart A) ≤ kyFanApproximationGauge k A := by
  rw [← kyFanApproximationGauge_complexify, ← kyFanApproximationGauge_complexify,
    ← diagonalPart_complexify_real U]
  exact TauCeti.ApproximationNumber.kyFanApproximationGauge_diagonalPart_le_complex
    (complexifySubmodule U) (complexify A) k

omit [CompleteSpace E] in
/-- Conjugating a real operator by a contraction pair cannot increase a Ky Fan gauge. -/
private theorem kyFanApproximationGauge_conj_le_real {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {L : E →L[ℝ] F} {R : F →L[ℝ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (A : E →L[ℝ] E) (k : ℕ) :
    kyFanApproximationGauge k (L ∘L A ∘L R) ≤ kyFanApproximationGauge k A := by
  have hcomp := kyFanApproximationGauge_comp_le
    (𝕜 := ℝ) (E := E) (F := E) (G := F) (H := F) k L A R
  refine hcomp.trans ?_
  have hnn := kyFanApproximationGauge_nonneg k A
  calc
    ‖L‖ * kyFanApproximationGauge k A * ‖R‖ ≤
        1 * kyFanApproximationGauge k A * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hL hnn) hR (norm_nonneg _) (by linarith)
    _ = kyFanApproximationGauge k A := by ring

omit [CompleteSpace E] in
/-- Ky Fan gauges are invariant under a real isometric change of chart. -/
private theorem kyFanApproximationGauge_conj_eq_real {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {L : E →L[ℝ] F} {R : F →L[ℝ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hRL : R ∘L L = ContinuousLinearMap.id ℝ E)
    (A : E →L[ℝ] E) (k : ℕ) :
    kyFanApproximationGauge k (L ∘L A ∘L R) = kyFanApproximationGauge k A := by
  refine le_antisymm
    (kyFanApproximationGauge_conj_le_real (E := E) (F := F) hL hR A k) ?_
  have hRLapp : ∀ y : E, R (L y) = y := by
    intro y
    have h := congrArg (fun T : E →L[ℝ] E => T y) hRL
    simpa using h
  have hcomp : R ∘L (L ∘L A ∘L R) ∘L L = A := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hRLapp x, hRLapp (A x)]
  have h := kyFanApproximationGauge_conj_le_real
    (E := F) (F := E) hR hL (L ∘L A ∘L R) k
  rwa [hcomp] at h

/-- A real compression of a Gram operator is the Gram operator of the restricted map. -/
private theorem orthogonalProjectionOnto_comp_gram_comp_subtypeL_real
    (T : E →L[ℝ] E) (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    [CompleteSpace (K : Type v)] :
    K.orthogonalProjectionOnto ∘L (star T * T) ∘L K.subtypeL =
      gramOperatorR (T ∘L K.subtypeL) := by
  rw [gramOperatorR, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
  rfl

omit [CompleteSpace E] in
/-- Admissibility of a real competitor passes to the complementary pair. -/
private theorem competitor_admissible_orthogonal_real (W : E →L[ℝ] E)
    (hWmap : W * U.starProjection = V.starProjection * W) :
    W * Uᗮ.starProjection = Vᗮ.starProjection * W := by
  show W * Uᗮ.starProjection = Vᗮ.starProjection * W
  rw [Submodule.starProjection_orthogonal' U, Submodule.starProjection_orthogonal' V,
    mul_sub, sub_mul, mul_one, one_mul, hWmap]

/-- The real nonacute rotation's squared displacement is already block diagonal. -/
private theorem diagonalPart_nonacuteDirectRotation_displacementSquare_real
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V) :
    U.diagonalPart ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) =
      (1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) := by
  let D := TauCeti.DavisKahan.nonacuteDirectRotation U V J
  let C := ContinuousLinearMap.modulus
    (TauCeti.DavisKahan.spectraCanonicalIntertwiner U V)
  let A : E →L[ℝ] E := (1 - star D) * (1 - D)
  have hunit := TauCeti.DavisKahan.star_nonacuteDirectRotation_mul_self U V J
  have hsum := TauCeti.DavisKahan.nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hAeq : A = 2 - (2 : ℝ) • C := by
    have hexp : A = 1 + star D * D - (D + star D) := by
      dsimp only [A]
      noncomm_ring
    rw [hexp]
    change 1 + star (TauCeti.DavisKahan.nonacuteDirectRotation U V J) *
      TauCeti.DavisKahan.nonacuteDirectRotation U V J -
      (TauCeti.DavisKahan.nonacuteDirectRotation U V J +
        star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) = _
    rw [hunit, hsum]
    norm_num [two_smul ℝ, C]
  have hCcomm : C * U.starProjection = U.starProjection * C :=
    (TauCeti.DavisKahan.spectraCanonicalAbsoluteValue_commute_projection U V).eq
  have hcomm : A * U.starProjection = U.starProjection * A := by
    rw [hAeq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hCcomm]
    congr 1
    rw [two_mul, mul_two]
  apply Submodule.diagonalPart_eq_self_of_reflectionConjugate
  have hAJ : A * U.reflectionOperator = U.reflectionOperator * A := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, hcomm]
    rw [show (ContinuousLinearMap.id ℝ E) = 1 from rfl, mul_one, one_mul]
  have hJJ : U.reflectionOperator * U.reflectionOperator = (1 : E →L[ℝ] E) :=
    Submodule.reflectionOperator_involutive (𝕜 := ℝ) (E := E) U
  calc
    U.reflectionOperator ∘L A ∘L U.reflectionOperator =
        U.reflectionOperator * (A * U.reflectionOperator) := rfl
    _ = U.reflectionOperator * (U.reflectionOperator * A) := by rw [hAJ]
    _ = (U.reflectionOperator * U.reflectionOperator) * A := by rw [mul_assoc]
    _ = A := by rw [hJJ, one_mul]

/-- **Proposition 4.3 over `ℝ` at the exact matched-defect, nonacute scope.** -/
theorem proposition4_3_nonacute_real
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) := by
  let : CompleteSpace (U : Type v) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  let : CompleteSpace ((U.orthogonal : Submodule ℝ E) : Type v) :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U.orthogonal).completeSpace_coe
  have hL : ‖(U.orthogonalDecomposition : E →L[ℝ] WithLp 2 (U × U.orthogonal))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.norm_map x)
  have hR : ‖(U.orthogonalDecomposition.symm : WithLp 2 (U × U.orthogonal) →L[ℝ] E)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (U.orthogonalDecomposition.symm.norm_map x)
  have hRL : (U.orthogonalDecomposition.symm : WithLp 2 (U × U.orthogonal) →L[ℝ] E) ∘L
      (U.orthogonalDecomposition : E →L[ℝ] WithLp 2 (U × U.orthogonal)) =
      ContinuousLinearMap.id ℝ E := by
    ext x
    simp
  have hchart : ∀ T : E →L[ℝ] E,
      kyFanApproximationGauge k (U.diagonalPart ((1 - star T) * (1 - T))) =
        kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperatorR ((1 - T) ∘L U.subtypeL))
          (gramOperatorR ((1 - T) ∘L U.orthogonal.subtypeL))) := by
    intro T
    have hst : (1 - star T) * (1 - T) = star (1 - T) * (1 - T) := by
      rw [star_sub, star_one]
    rw [hst,
      ← kyFanApproximationGauge_conj_eq_real hL hR hRL
        (U.diagonalPart (star (1 - T) * (1 - T))) k,
      orthogonalDecomposition_conj_diagonalPart U (star (1 - T) * (1 - T)),
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_real,
      orthogonalProjectionOnto_comp_gram_comp_subtypeL_real]
  have hU : ∀ n,
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.subtypeL).approximationNumber n ≤
      ((1 - W) ∘L U.subtypeL).approximationNumber n :=
    proposition4_1_nonacute_real U V J W hWunitary hWmap
  have hUperp : ∀ n,
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.orthogonal.subtypeL).approximationNumber n ≤
      ((1 - W) ∘L U.orthogonal.subtypeL).approximationNumber n := by
    intro n
    have h := proposition4_1_nonacute_real U.orthogonal V.orthogonal
      (TauCeti.DavisKahan.orthogonalCrossedDefectEquiv U V J) W hWunitary
      (competitor_admissible_orthogonal_real U V W hWmap) n
    rwa [TauCeti.DavisKahan.nonacuteDirectRotation_orthogonal U V J] at h
  have hblock := kyFanApproximationGauge_blockSum_le
    (fun j => kyFanApproximationGauge_gramOperator_mono_real _ _ hU j)
    (fun j => kyFanApproximationGauge_gramOperator_mono_real _ _ hUperp j) k
  calc
    kyFanApproximationGauge k
        ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) =
      kyFanApproximationGauge k (U.diagonalPart
        ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J))) := by
        rw [diagonalPart_nonacuteDirectRotation_displacementSquare_real U V J]
    _ = kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperatorR ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L U.subtypeL))
          (gramOperatorR ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
            U.orthogonal.subtypeL))) := hchart _
    _ ≤ kyFanApproximationGauge k (continuousOrthogonalBlockSum
          (gramOperatorR ((1 - W) ∘L U.subtypeL))
          (gramOperatorR ((1 - W) ∘L U.orthogonal.subtypeL))) := hblock
    _ = kyFanApproximationGauge k
          (U.diagonalPart ((1 - star W) * (1 - W))) := (hchart W).symm
    _ ≤ kyFanApproximationGauge k ((1 - star W) * (1 - W)) :=
      kyFanApproximationGauge_diagonalPart_le_real U _ k

/-- Proposition 4.3 over `ℝ`, promoted to every real unitarily invariant ideal gauge at the
matched-defect nonacute scope. -/
theorem proposition4_3_nonacute_real_idealGauge
    (N : FanDominantIdealFamily (𝕜 := ℝ))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  N.majorization_mem_and_gauge_le hWmem
    (proposition4_3_nonacute_real U V J W hWunitary hWmap)

/-- **Davis--Kahan 1970, Proposition 4.1, first formulation over `ℝ`.**

At the compact source scope, an arbitrary real orthogonal competitor carrying `U` onto `V`
admits an orthonormal family of source vectors whose displacement angles dominate every
nonzero principal angle.  This is the real counterpart of
`proposition4_1_compact_orthonormalVectors_complex`; zero angles have a vacuous lower bound. -/
theorem proposition4_1_compact_orthonormalVectors_real
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
      Orthonormal ℝ v ∧
        ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
          TauCeti.principalAngleSequence U V (n : ℕ) ≤
            TauCeti.vectorAngle ℝ (v n : E) (W (v n : E)) := by
  let T : U →L[ℝ] E := TauCeti.principalSineOperator U V
  let A : U →L[ℝ] U := gramOperatorR T
  have hAc : IsCompactOperator A := hcompact.clm_comp T.adjoint
  have hAs : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self T).isSymmetric
  have hApos : ∀ x, 0 ≤ inner ℝ (A x) x :=
    fun x => (ContinuousLinearMap.isPositive_adjoint_comp_self T).inner_nonneg_left x
  have hseq (n : ℕ) : A.approximationNumber n =
      TauCeti.principalSineSequence U V n ^ 2 := by
    simpa only [A, T, TauCeti.principalSineSequence] using
      approximationNumber_gramOperator_real T n
  let e : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} ≃
      {n : ℕ // 0 < A.approximationNumber n} :=
    { toFun := fun n => ⟨n, by rw [hseq]; nlinarith [n.2]⟩
      invFun := fun n => ⟨n, by
        have hn := n.2
        rw [hseq] at hn
        nlinarith [TauCeti.principalSineSequence_nonneg U V n]⟩
      left_inv := fun n => Subtype.ext rfl
      right_inv := fun n => Subtype.ext rfl }
  let v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U := fun n =>
    TauCeti.positiveApproximationEigenvector hAc hAs hApos (e n) (e n).2
  have hvon : Orthonormal ℝ v := by
    change Orthonormal ℝ
      ((fun n : {n : ℕ // 0 < A.approximationNumber n} =>
        TauCeti.positiveApproximationEigenvector hAc hAs hApos n n.2) ∘ e)
    exact (TauCeti.orthonormal_positiveApproximationEigenvector hAc hAs hApos).comp
      e e.injective
  refine ⟨v, hvon, fun n => ?_⟩
  let x : U := v n
  let s : ℝ := TauCeti.principalSineSequence U V n
  have hxnorm : ‖x‖ = 1 := hvon.1 n
  have hAx := TauCeti.apply_positiveApproximationEigenvector hAc hAs hApos
    (e n) (e n).2
  have hTx : ‖T x‖ = s := by
    have hen : ((e n : {n : ℕ // 0 < A.approximationNumber n}) : ℕ) = (n : ℕ) := rfl
    have hnormsq : ‖T x‖ ^ 2 = s ^ 2 := by
      calc
        ‖T x‖ ^ 2 = inner ℝ (A x) x := by
          simpa only [A, gramOperatorR, RCLike.re_to_real] using
            ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T x
        _ = s ^ 2 := by
          change inner ℝ
            (A (TauCeti.positiveApproximationEigenvector hAc hAs hApos (e n) (e n).2))
            (TauCeti.positiveApproximationEigenvector hAc hAs hApos (e n) (e n).2) = _
          rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hxnorm, one_pow,
            hseq, hen]
          change s ^ 2 * 1 = s ^ 2
          ring
    nlinarith [norm_nonneg (T x), n.2]
  have hproj : ‖sourceCosineR U V x‖ =
      Real.cos (TauCeti.principalAngleSequence U V n) := by
    have hpy := V.norm_sq_eq_add_norm_sq_starProjection (x : E)
    have hC := norm_sourceCosineR_eq_norm_targetProjection U V x
    have hsin := TauCeti.sin_principalAngleSequence U V n
    have htrig := Real.sin_sq_add_cos_sq (TauCeti.principalAngleSequence U V n)
    have hcos0 : 0 ≤ Real.cos (TauCeti.principalAngleSequence U V n) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        ((neg_nonpos_of_nonneg Real.pi_div_two_pos.le).trans
          (TauCeti.principalAngleSequence_nonneg U V n))
        (TauCeti.principalAngleSequence_le_pi_div_two U V n)
    have hTdef : ‖T x‖ = ‖Vᗮ.starProjection (x : E)‖ := by
      dsimp only [T]
      rw [TauCeti.principalSineOperator_apply]
    have hxnormE : ‖(x : E)‖ = 1 := hxnorm
    rw [hxnormE, one_pow, ← hTdef, hTx] at hpy
    change 1 = ‖V.starProjection (x : E)‖ ^ 2 + s ^ 2 at hpy
    dsimp only [s] at hpy
    rw [hC]
    rw [hsin] at htrig
    rw [← sq_eq_sq₀ (norm_nonneg _) hcos0]
    nlinarith [hpy, htrig]
  have hWxV : W (x : E) ∈ V := by
    apply V.starProjection_eq_self_iff.mp
    have happ := congrArg (fun R : E →L[ℝ] E => R (x : E)) hWmap
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr x.property] at happ
    exact happ.symm
  have hinner : inner ℝ (W (x : E)) (x : E) ≤ ‖sourceCosineR U V x‖ := by
    calc
      inner ℝ (W (x : E)) (x : E) =
          inner ℝ (W (x : E)) (V.starProjection (x : E)) := by
        rw [← V.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hWxV]
      _ ≤ ‖W (x : E)‖ * ‖V.starProjection (x : E)‖ := real_inner_le_norm _ _
      _ = ‖sourceCosineR U V x‖ := by
        have hxnormE : ‖(x : E)‖ = 1 := hxnorm
        rw [Unitary.norm_map (⟨W, hWunitary⟩ : unitary (E →L[ℝ] E)), hxnormE,
          one_mul, norm_sourceCosineR_eq_norm_targetProjection]
  rw [hproj] at hinner
  apply TauCeti.le_vectorAngle_of_unit_norm_of_re_inner_le_cos
  · exact hxnorm
  · exact Unitary.norm_map (⟨W, hWunitary⟩ : unitary (E →L[ℝ] E)) (x : E) |>.trans hxnorm
  · exact TauCeti.principalAngleSequence_nonneg U V n
  · exact (TauCeti.principalAngleSequence_le_pi_div_two U V n).trans
      (by linarith [Real.pi_pos])
  · simpa only [RCLike.re_to_real] using hinner


/-- The real directed sine and positive source cosine satisfy the source
Pythagorean identity. -/
theorem principalSineOperator_norm_sq_eq_one_sub_sourceCosineR_norm_sq
    (x : U) :
    ‖TauCeti.principalSineOperator U V x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖sourceCosineR U V x‖ ^ 2 := by
  have hpy := V.norm_sq_eq_add_norm_sq_starProjection (x : E)
  have hC := norm_sourceCosineR_eq_norm_targetProjection U V x
  rw [TauCeti.principalSineOperator_apply, hC]
  have hxnorm : ‖(x : E)‖ = ‖x‖ := rfl
  rw [hxnorm] at hpy
  nlinarith

/-- **The exact real singular-value value in Proposition 4.1 at the inherited
compact, matched-defect scope.** -/
theorem proposition4_1_compact_nonacute_directRotationValues_real
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (n : ℕ) :
    (ContinuousLinearMap.approximationNumber
        ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) n : Real) =
      2 * Real.sin (TauCeti.principalAngleSequence U V n / 2) := by
  let A : U →L[ℝ] E := sourceRestrictedDisplacementR U
    (TauCeti.DavisKahan.nonacuteDirectRotation U V J)
  let B : U →L[ℝ] E := sourceRestrictedDisplacementR U W
  let S : U →L[ℝ] E := TauCeti.principalSineOperator U V
  have hAnorm : ‖A‖ <= Real.sqrt 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun x => ?_
    have hsq := sourceRestrictedDisplacementR_nonacute_norm_sq U V J x
    have hpos := sourceCosineR_nonnegative U V x
    have hroot : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hleft := norm_nonneg
      (sourceRestrictedDisplacementR U
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J) x)
    have hright : 0 <= Real.sqrt 2 * ‖x‖ := by positivity
    apply (sq_le_sq₀ hleft hright).1
    rw [hsq, mul_pow, hroot]
    nlinarith
  have hcut := real_approximationNumber_direct_cosineCutoff_eq_sine
    (sourceCosineR U V) A B S
    (sourceCosineR_selfAdjoint U V) (sourceCosineR_nonnegative U V)
    hAnorm (sourceRestrictedDisplacementR_nonacute_norm_sq U V J)
    (sourceRestrictedDisplacementR_competitor_norm_sq_lower U V W hWunitary hWmap)
    (principalSineOperator_norm_sq_eq_one_sub_sourceCosineR_norm_sq U V) n
  have hDseq := sourceRestrictedDisplacementR_sameApproximationSingularSequence U
    (TauCeti.DavisKahan.nonacuteDirectRotation U V J) n
  let a : Real := (A.approximationNumber n : Real)
  let theta : Real := TauCeti.principalAngleSequence U V n
  let shalf : Real := Real.sin (theta / 2)
  have hcos : Real.cos theta =
      Real.sqrt (1 - (TauCeti.principalSineSequence U V n) ^ 2) := by
    dsimp only [theta, TauCeti.principalAngleSequence]
    rw [Real.cos_arcsin]
  have hcosApprox : Real.cos theta =
      Real.sqrt (1 - ((TauCeti.principalSineOperator U V).approximationNumber n : Real) ^ 2) := by
    simpa only [TauCeti.principalSineSequence] using hcos
  have hcutCos : 1 - a ^ 2 / 2 = Real.cos theta := by
    simpa only [a, A, S] using hcut.trans hcosApprox.symm
  have hdouble : Real.cos theta = 1 - 2 * shalf ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq (theta / 2)
    dsimp only [shalf]
    calc
      Real.cos theta = Real.cos (theta / 2 + theta / 2) := by congr 1; ring
      _ = Real.cos (theta / 2) * Real.cos (theta / 2) -
          Real.sin (theta / 2) * Real.sin (theta / 2) := by rw [Real.cos_add]
      _ = 1 - 2 * Real.sin (theta / 2) ^ 2 := by nlinarith
  have haSq : a ^ 2 = (2 * shalf) ^ 2 := by
    rw [hdouble] at hcutCos
    nlinarith
  have htheta0 : 0 <= theta := TauCeti.principalAngleSequence_nonneg U V n
  have hshalf0 : 0 <= shalf := by
    dsimp only [shalf]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [TauCeti.principalAngleSequence_le_pi_div_two U V n, Real.pi_pos])
  have ha0 : 0 <= a := by
    dsimp only [a]
    exact A.approximationNumber_nonneg n
  have ha : a = 2 * shalf := (sq_eq_sq₀ ha0 (mul_nonneg (by norm_num) hshalf0)).1 haSq
  change (ContinuousLinearMap.approximationNumber
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection) n : Real) = _
  have hD : ContinuousLinearMap.approximationNumber
      ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection) n = A.approximationNumber n := by
    simpa only [A] using hDseq
  rw [hD]
  simpa only [a, shalf, theta] using ha

/-- **Proposition 4.1 over `ℝ` with both printed formulations and the inherited
compact, matched-defect scope in one declaration.** -/
theorem proposition4_1_compact_nonacute_real
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
      Orthonormal ℝ v ∧
        ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
          TauCeti.principalAngleSequence U V (n : ℕ) ≤
            TauCeti.vectorAngle ℝ (v n : E) (W (v n : E))) ∧
      (∀ n : ℕ,
        (ContinuousLinearMap.approximationNumber
            ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
              U.starProjection) n : Real) =
          2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
      ∀ n : ℕ,
        ContinuousLinearMap.approximationNumber
            ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
              U.starProjection) n ≤
          ContinuousLinearMap.approximationNumber
            ((1 - W) ∘L U.starProjection) n :=
  ⟨proposition4_1_compact_orthonormalVectors_real U V hcompact W hWunitary hWmap,
    proposition4_1_compact_nonacute_directRotationValues_real
      U V hcompact J W hWunitary hWmap,
    Proposition4_1_nonacute_real U V J W hWunitary hWmap⟩

/-- **Corollary 4.1 over `ℝ` at the inherited compact, matched-defect scope.** -/
theorem corollary4_1_compact_nonacute_real
    (N : FanDominantIdealFamily (𝕜 := ℝ))
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
        U.starProjection) ∧
      N.gauge ((1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  Corollary4_1_nonacute_real U V N J W hWunitary hWmap hWmem

/-- **Proposition 4.3 over `ℝ` at the inherited compact, matched-defect scope.** -/
theorem proposition4_3_compact_nonacute_real_idealGauge
    (N : FanDominantIdealFamily (𝕜 := ℝ))
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (TauCeti.DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  proposition4_3_nonacute_real_idealGauge U V N J W hWunitary hWmap hWmem

/-- **Davis--Kahan 1970, Proposition 4.3, over a real Hilbert space of arbitrary
dimension.**

Every Ky Fan sum of the approximation numbers of the squared full displacement
`(1 - Wᵀ)(1 - W)` is minimized by the real direct rotation.  Ky Fan level is the
honest scope: the individual approximation numbers are *not* dominated, which is
what the repository's refutation of Proposition 4.4 records. -/
theorem proposition4_3_real (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (TauCeti.DavisKahan.directRotationR U V hacute)) *
          (1 - TauCeti.DavisKahan.directRotationR U V hacute)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) := by
  rw [← kyFanApproximationGauge_complexify, ← kyFanApproximationGauge_complexify,
    complexify_displacementSquare, complexify_displacementSquare,
    TauCeti.DavisKahan.complexify_directRotationR]
  exact TauCeti.DavisKahan.Section4.proposition4_3_squaredDisplacement_kyFan
    (complexifySubmodule U) (complexifySubmodule V)
    (TauCeti.DavisKahan.isUniformlyAcute_complexifySubmodule U V hacute) (complexify W)
    (TauCeti.DavisKahan.complexify_mem_unitary hWunitary)
    (complexify_intertwines U V hWmap) k

/-- **Davis--Kahan 1970, Proposition 4.3 over a real Hilbert space of arbitrary
dimension, for every unitarily invariant norm.**

For every Ky-Fan-dominant symmetric ideal family of operators on real Hilbert
spaces, the squared full displacement `(1 − W)ᵀ(1 − W)` of the real direct
rotation lies in the ideal and its gauge is least among all real orthogonal `W`
carrying `U` onto `V`.  Membership of the minimizer is **concluded**, not
assumed, matching `corollary4_1_real`.

The family is real, not a transported complex one, for the reason given in the
module docstring.  The promotion consumes Ky Fan prefix sums only: the
individual approximation numbers are *not* dominated, which is what the
repository's refutation of Proposition 4.4 records. -/
theorem proposition4_3_real_idealGauge (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (TauCeti.DavisKahan.directRotationR U V hacute)) *
        (1 - TauCeti.DavisKahan.directRotationR U V hacute)) ∧
      N.gauge ((1 - star (TauCeti.DavisKahan.directRotationR U V hacute)) *
          (1 - TauCeti.DavisKahan.directRotationR U V hacute)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  N.majorization_mem_and_gauge_le hWmem
    (proposition4_3_real U V hacute W hWunitary hWmap)

/-! ### The two full-displacement consequences over `ℝ`

Davis and Kahan work on a real *or* complex Hilbert space, and the two consequences they draw
immediately after Proposition 4.3 — that the operator norm and the Hilbert--Schmidt norm of
`1 - V` itself are minimized by the direct rotation — inherit that scope.  The complex
endpoints are `Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_opNorm` and
`..._hilbertSchmidt` in `Section4.lean`; these are their real twins, at the same nonacute
matched-crossed-defect scope.

The one ingredient that is not scalar-generic is `aₙ(X⋆X) = aₙ(X)²`, whose proof runs through
complex spectral theory.  `approximationNumber_gramOperator_real` above already descends it to
`ℝ` through canonical complexification, so both consequences follow from the real Ky Fan
Proposition 4.3 exactly as they do over `ℂ`. -/

/-- The squared full displacement is the real Gram operator of the full displacement. -/
private theorem displacementSquare_eq_gramOperatorR (W : E →L[ℝ] E) :
    (1 - star W) * (1 - W) = gramOperatorR (1 - W) := by
  rw [show (1 : E →L[ℝ] E) - star W = star (1 - W) by rw [star_sub, star_one]]
  rfl

/-- `‖X⋆X‖₁ = ‖X‖_HS²` over `ℝ`, the real twin of
`TauCeti.ApproximationNumber.nuclearENorm_gramOperator`. -/
private theorem nuclearENorm_gramOperatorR {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) :
    (gramOperatorR A).nuclearENorm = A.hilbertSchmidtENorm ^ 2 := by
  have hsum : (gramOperatorR A).nuclearENorm =
      ∑' n : ℕ, ENNReal.ofReal (A.approximationNumber n) ^ (2 : ℝ) := by
    rw [ContinuousLinearMap.nuclearENorm]
    refine tsum_congr fun n => ?_
    rw [approximationNumber_gramOperator_real A n,
      ← Real.rpow_natCast (A.approximationNumber n) 2,
      ← ENNReal.ofReal_rpow_of_nonneg (A.approximationNumber_nonneg n) (by norm_num)]
    norm_num
  rw [hsum, ← ContinuousLinearMap.schattenENorm_two A, ContinuousLinearMap.schattenENorm,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Davis--Kahan 1970, the operator-norm consequence of Proposition 4.3, over `ℝ`**, at the
matched-crossed-defect scope Section 4 inherits.

`‖1 − U‖ ≤ ‖1 − W‖` for every real orthogonal `W` carrying `U` onto `V`.  The real twin of
`Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_opNorm`. -/
theorem Proposition4_3_nonacute_real_fullDisplacement_opNorm
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ‖1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J‖ ≤ ‖1 - W‖ := by
  have hk := proposition4_3_nonacute_real U V J W hWunitary hWmap 1
  rw [displacementSquare_eq_gramOperatorR, displacementSquare_eq_gramOperatorR] at hk
  simp only [TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge,
    ContinuousLinearMap.kyFanGauge_one, gramOperatorR,
    ContinuousLinearMap.norm_adjoint_comp_self] at hk
  nlinarith [norm_nonneg (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J),
    norm_nonneg (1 - W)]

/-- **Davis--Kahan 1970, the Hilbert--Schmidt consequence of Proposition 4.3, over `ℝ`**, at
the matched-crossed-defect scope Section 4 inherits.

`‖1 − U‖_HS ≤ ‖1 − W‖_HS`, in `ℝ≥0∞`, so no Hilbert--Schmidt hypothesis on the competitor.
The real twin of `Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_hilbertSchmidt`. -/
theorem Proposition4_3_nonacute_real_fullDisplacement_hilbertSchmidt
    (J : halmosSourceDefect U V ≃ₗᵢ[ℝ] halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J).hilbertSchmidtENorm ≤
      (1 - W).hilbertSchmidtENorm := by
  have hnuc :
      (gramOperatorR (1 - TauCeti.DavisKahan.nonacuteDirectRotation U V J)).nuclearENorm ≤
        (gramOperatorR (1 - W)).nuclearENorm := by
    rw [ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge]
    refine iSup_mono fun k => ENNReal.ofReal_le_ofReal ?_
    have hk := proposition4_3_nonacute_real U V J W hWunitary hWmap k
    rw [displacementSquare_eq_gramOperatorR, displacementSquare_eq_gramOperatorR] at hk
    simpa only [TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge] using hk
  rw [nuclearENorm_gramOperatorR, nuclearENorm_gramOperatorR] at hnuc
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast _ 2] at hnuc
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).mp hnuc

end

end DavisKahan1970
end TauCeti
