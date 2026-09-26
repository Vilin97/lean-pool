/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
-- supplies `halmosCosineSq`, `projection`, `complementaryProjection`, `projection_sq` and the
-- two-projection calculus these block estimates run on.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericRotationPredicates
-- supplies `IsDirectRotation`, the five-field predicate the norm bounds are read against.
-- It lives in `TauCeti.DavisKahan`.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Elementary
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
-- supplies `reflectedSubspace` and `starProjection_reflectedSubspace`, the mirror image of
-- one subspace in another.  That module imports only `SinTheta`/`SpectralTheory` material
-- so the dependency is acyclic.
-- supplies `directRotation_conjugates_projection` and its complement form, the
-- intertwining identities a `IsDirectRotation` gives on the two projections.
-- supplies `spectraDirectRotation_crossed_blocks`, the crossed-block identity of the
-- canonical direct rotation.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.PrincipalSquareRoot
-- supplies the `U`-block calculus (`star_blocks_eq`, `eq_sum_blocks`) promoted out of the
-- frontier alongside Proposition 3.3.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.FixedCosineSubspace

/-! # Direct Rotation Blocks -/

@[expose] public section

open TauCeti.DavisKahan.Angle

-- supplies `inner_starProjection_self_eq`.
-- supplies `spectraDirectRotation`, `IsUniformlyAcute` and the reflection/projection algebra
-- (`reflectionOperator_eq_projection_add_projection_sub_one`).  That module and everything
-- beneath it are `Geometry`/`BoundedOperator` leaves, so this
-- module is acyclic.

/-!
# Diagonal blocks and the half-angle estimate for a direct rotation

Davis--Kahan 1970, Proposition 3.4, squares a direct rotation `W` and asks when `W²` is again
a direct rotation, for the reflected pair.  The printed hypothesis is the half-angle condition
`C₀² ≥ ½` on the source subspace, and the work of getting from it to the conclusion is a chain
of estimates about the *diagonal blocks* of `W`.

This module owns that chain.  It was extracted from the Section 3 frontier module; the
mathematics is unchanged.  The source-facing statements that consume it -- the printed
Proposition 3.4 and its acute specialisations -- stay downstream.

## What is here

* the two diagonal blocks of the canonical direct rotation are self-adjoint, which the
  `star`-block calculus needs and which `IsDirectRotation` does not give, because that
  predicate records the compressions only through their numerical range;
* the operator-norm bound `‖P_V w‖ ≤ (√2/2)‖w‖` on the source subspace, in a
  hypothesis-light form and in the `IsDirectRotation` form;
* the numerical range of the Halmos cosine square, and the half-angle inequality
  `re ⟪x, (cos²Θ - ½) x⟫ ≥ 0` in both the paper-direct-rotation and the source form;
* two reflection/projection identities and a numerical-range positivity criterion, all three
  of which are generic bounded-operator algebra with no Section 3 content.

## Scope

Complex scalars and a complete space throughout, matching the source; the two reflection
identities need neither and carry an `omit`.

## Main results

* `isSelfAdjoint_source_block_spectraDirectRotation`,
  `isSelfAdjoint_complement_block_spectraDirectRotation`
* `norm_projection_apply_le_of_forall_mem_source`,
  `norm_projection_apply_le_of_directRotation`
* `re_inner_halmosCosineSq_self`,
  `re_inner_halmosCosineSq_sub_half_nonneg_of_directRotation`,
  `re_inner_halmosCosineSq_sub_half_nonneg_of_source`
* `reflectionOperator_mul_projection_self`, `projection_mul_reflectionOperator_self`
* `nonneg_add_star_of_re_inner_nonneg`
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahanExt (reflectedSubspace starProjection_reflectedSubspace)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The source diagonal block of the canonical direct rotation is self-adjoint.

`IsDirectRotation` records the diagonal compressions only through their numerical range,
so their self-adjointness -- which the `star`-block calculus needs -- has to be read off the
canonical construction, where the block *is* the positive Halmos cosine. -/
theorem isSelfAdjoint_source_block_spectraDirectRotation
    (hacute : IsUniformlyAcute U V) :
    IsSelfAdjoint (U.starProjection * spectraDirectRotation U V hacute * U.starProjection) := by
  have hC : IsSelfAdjoint
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp
      (ContinuousLinearMap.modulus_nonneg _)).isSelfAdjoint
  have hcomm : Commute
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) (U.starProjection) :=
    spectraCanonicalAbsoluteValue_commute_projection U V
  rw [projection_mul_spectraDirectRotation_mul_projection U V hacute]
  rw [IsSelfAdjoint, star_mul, (isSelfAdjoint_starProjection U).star_eq, hC.star_eq]
  exact hcomm.eq.symm

/-- The complementary diagonal block of the canonical direct rotation is self-adjoint. -/
theorem isSelfAdjoint_complement_block_spectraDirectRotation
    (hacute : IsUniformlyAcute U V) :
    IsSelfAdjoint ((Uᗮ).starProjection * spectraDirectRotation U V hacute *
      (Uᗮ).starProjection) := by
  have hC : IsSelfAdjoint
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp
      (ContinuousLinearMap.modulus_nonneg _)).isSelfAdjoint
  have hcomm : Commute
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V))
      ((Uᗮ).starProjection) := by
    have hcomp : (Uᗮ).starProjection = 1 - U.starProjection :=
      Submodule.starProjection_orthogonal' U
    rw [commute_iff_eq, hcomp, mul_sub, mul_one, sub_mul, one_mul,
      (spectraCanonicalAbsoluteValue_commute_projection U V).eq]
  rw [complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection
    U V hacute]
  rw [IsSelfAdjoint, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, hC.star_eq]
  exact hcomm.eq.symm

/-- **In the acute case a bound on one directed gap transfers to the other.**

The paper's `S₀` and `S₁` are the two crossed blocks of the direct rotation, and Definition
3.1(ii) says `S₁ = S₀⋆`; so they have the same norm, and each of the two directed gaps
`‖P_{Vᗮ} P_U‖`, `‖P_V P_{Uᗮ}‖` equals it.  This is what makes the printed hypothesis
`C₀² ≥ ½`, which constrains only the `Pℋ` block, force the companion bound `C₁² ≥ ½` on
`Ptildeℋ` -- an implication that is **false** without a unitary intertwiner: `U ⊆ V` with
`dim V > dim U` has `C₀² = 1` and `C₁²` with `0` in its numerical range.  Equality of the two
directed gaps needs acuteness (`Submodule.projectionGap_eq_max_directedProjectionGap` gives
only the maximum), and this is the acute half of it. -/
theorem norm_projection_apply_le_of_forall_mem_source
    (hacute : IsUniformlyAcute U V) {r : ℝ} (hr : 0 ≤ r)
    (hsrc : ∀ x ∈ U, ‖(Vᗮ).starProjection x‖ ≤ r * ‖x‖)
    (w : H) (hw : w ∈ Uᗮ) : ‖V.starProjection w‖ ≤ r * ‖w‖ := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hcross : (Uᗮ).starProjection * W * U.starProjection =
      -star (U.starProjection * W * (Uᗮ).starProjection) :=
    TauCeti.DavisKahan.spectraDirectRotation_crossed_blocks U V hacute
  obtain ⟨-, -, h12, h21⟩ :=
    star_blocks_eq U W (isSelfAdjoint_source_block_spectraDirectRotation U V hacute)
      (isSelfAdjoint_complement_block_spectraDirectRotation U V hacute) hcross
  set L : H →L[ℂ] H := U.starProjection * W * (Uᗮ).starProjection with hLdef
  -- the crossed block of the adjoint is the adjoint of the crossed block
  have hstarL : (Uᗮ).starProjection * star W * U.starProjection = star L := by
    rw [h21, hcross, neg_neg]
  have hisom : ∀ z : H, ‖W z‖ = ‖z‖ := norm_spectraDirectRotation_apply U V hacute
  have hconjc : ∀ z : H,
      (Vᗮ).starProjection z = W ((Uᗮ).starProjection (star W z)) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z)
      (spectraDirectRotation_conjugates_complementaryProjection U V hacute)
    simpa only [mul_apply_eq_comp] using h.symm
  have hconj : ∀ z : H, V.starProjection z = W (U.starProjection (star W z)) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z)
      (spectraDirectRotation_conjugates_projection U V hacute)
    simpa only [mul_apply_eq_comp] using h.symm
  -- the hypothesis bounds the adjoint crossed block
  have hstarLbound : ∀ y : H, ‖star L y‖ ≤ r * ‖y‖ := by
    intro y
    have hy : star L y = (Uᗮ).starProjection (star W (U.starProjection y)) := by
      rw [← hstarL]
      simp only [mul_apply_eq_comp]
    have hval : ‖star L y‖ = ‖(Vᗮ).starProjection (U.starProjection y)‖ := by
      rw [hy, hconjc (U.starProjection y), hisom]
    rw [hval]
    refine le_trans (hsrc _ (U.starProjection_apply_mem y)) ?_
    exact mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le y) hr
  have hLnorm : ‖L‖ ≤ r := by
    rw [← norm_star L]
    exact ContinuousLinearMap.opNorm_le_bound _ hr hstarLbound
  -- and the other directed gap is read off the same block
  have hwc : (Uᗮ).starProjection w = w :=
    Submodule.starProjection_eq_self_iff.mpr hw
  have hval : V.starProjection w = W (-(L w)) := by
    rw [hconj w]
    have hy : U.starProjection (star W w) =
        (U.starProjection * star W * (Uᗮ).starProjection) w := by
      simp only [mul_apply_eq_comp, hwc]
    rw [hy, h12]
    simp only [neg_apply]
  rw [hval, hisom, norm_neg]
  exact le_trans (L.le_opNorm w) (mul_le_mul_of_nonneg_right hLnorm (norm_nonneg w))

/-- A bound on one directed gap transfers to the other for an arbitrary paper direct
rotation whose two diagonal compressions are self-adjoint.

This is the direct-rotation form of `norm_projection_apply_le_of_forall_mem_source`.
Definition 3.1 supplies the equality of the two crossed-block norms directly, so the result
applies to the full nonacute direct-rotation scope. -/
theorem norm_projection_apply_le_of_directRotation
    (T : H →L[ℂ] H) (hT : IsDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    {r : ℝ} (hr : 0 ≤ r)
    (hsrc : ∀ x ∈ U, ‖(Vᗮ).starProjection x‖ ≤ r * ‖x‖)
    (w : H) (hw : w ∈ Uᗮ) : ‖V.starProjection w‖ ≤ r * ‖w‖ := by
  obtain ⟨-, -, h12, h21⟩ :=
    star_blocks_eq U T hsource_sa hcomplement_sa hT.crossed_blocks
  set L : H →L[ℂ] H := U.starProjection * T * (Uᗮ).starProjection with hLdef
  have hstarL : (Uᗮ).starProjection * star T * U.starProjection = star L := by
    rw [h21, hT.crossed_blocks, neg_neg]
  have hisom : ∀ z : H, ‖T z‖ = ‖z‖ := fun z =>
    Unitary.norm_map ⟨T, hT.unitary_mem⟩ z
  have hconjc : ∀ z : H,
      (Vᗮ).starProjection z = T ((Uᗮ).starProjection (star T z)) := by
    intro z
    have h := congrArg (fun A : H →L[ℂ] H => A z)
      (TauCeti.DavisKahan.directRotation_conjugates_complementaryProjection
        U V T hT)
    simpa only [mul_apply_eq_comp] using h.symm
  have hconj : ∀ z : H, V.starProjection z = T (U.starProjection (star T z)) := by
    intro z
    have h := congrArg (fun A : H →L[ℂ] H => A z)
      (TauCeti.DavisKahan.directRotation_conjugates_projection U V T hT)
    simpa only [mul_apply_eq_comp] using h.symm
  have hstarLbound : ∀ y : H, ‖star L y‖ ≤ r * ‖y‖ := by
    intro y
    have hy : star L y = (Uᗮ).starProjection (star T (U.starProjection y)) := by
      rw [← hstarL]
      simp only [mul_apply_eq_comp]
    have hval : ‖star L y‖ = ‖(Vᗮ).starProjection (U.starProjection y)‖ := by
      rw [hy, hconjc (U.starProjection y), hisom]
    rw [hval]
    refine le_trans (hsrc _ (U.starProjection_apply_mem y)) ?_
    exact mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le y) hr
  have hLnorm : ‖L‖ ≤ r := by
    rw [← norm_star L]
    exact ContinuousLinearMap.opNorm_le_bound _ hr hstarLbound
  have hwc : (Uᗮ).starProjection w = w :=
    Submodule.starProjection_eq_self_iff.mpr hw
  have hval : V.starProjection w = T (-(L w)) := by
    rw [hconj w]
    have hy : U.starProjection (star T w) =
        (U.starProjection * star T * (Uᗮ).starProjection) w := by
      simp only [mul_apply_eq_comp, hwc]
    rw [hy, h12]
    simp only [neg_apply]
  rw [hval, hisom, norm_neg]
  exact le_trans (L.le_opNorm w) (mul_le_mul_of_nonneg_right hLnorm (norm_nonneg w))

omit [CompleteSpace H] in
/-- The cosine-square quadratic form, block by block: `⟪x, cos²Θ x⟫` is
`‖P_V P_U x‖² + ‖P_{Vᗮ} P_{Uᗮ} x‖²`. -/
theorem re_inner_halmosCosineSq_self (x : H) :
    RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ =
      ‖V.starProjection (U.starProjection x)‖ ^ 2 +
        ‖(Vᗮ).starProjection ((Uᗮ).starProjection x)‖ ^ 2 := by
  have hval : halmosCosineSq U V x =
      U.starProjection (V.starProjection (U.starProjection x)) +
        (Uᗮ).starProjection
          ((Vᗮ).starProjection ((Uᗮ).starProjection x)) := by
    change (U.starProjection * V.starProjection * U.starProjection +
      (Uᗮ).starProjection * (Vᗮ).starProjection *
        (Uᗮ).starProjection) x = _
    simp only [add_apply, mul_apply_eq_comp]
  have hblock : ∀ (K : Submodule ℂ H) [K.HasOrthogonalProjection]
      (M : Submodule ℂ H) [M.HasOrthogonalProjection],
      RCLike.re ⟪x, K.starProjection (M.starProjection (K.starProjection x))⟫_ℂ =
        ‖M.starProjection (K.starProjection x)‖ ^ 2 := by
    intro K _ M _
    have hsym : ⟪x, K.starProjection (M.starProjection (K.starProjection x))⟫_ℂ =
        ⟪K.starProjection x, M.starProjection (K.starProjection x)⟫_ℂ :=
      (K.starProjection_isSymmetric x (M.starProjection (K.starProjection x))).symm
    have hself : ⟪M.starProjection (K.starProjection x), K.starProjection x⟫_ℂ =
        ((‖M.starProjection (K.starProjection x)‖ : ℝ) : ℂ) ^ 2 :=
      inner_starProjection_self_eq M (K.starProjection x)
    rw [hsym, inner_re_symm, hself]
    norm_cast
  rw [hval, inner_add_right, map_add, hblock U V, hblock Uᗮ Vᗮ]

/-- The printed source-block half-angle bound yields the whole-space cosine-square bound for
an arbitrary paper direct rotation with self-adjoint diagonal compressions. -/
theorem re_inner_halmosCosineSq_sub_half_nonneg_of_directRotation
    (T : H →L[ℂ] H) (hT : IsDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) (x : H) :
    0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2 := by
  have hroot : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hrootsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h2]
    norm_num
  have hsrc : ∀ y ∈ U,
      ‖(Vᗮ).starProjection y‖ ≤ (Real.sqrt 2 / 2) * ‖y‖ := by
    intro y hy
    have hpy : ‖y‖ ^ 2 =
        ‖V.starProjection y‖ ^ 2 + ‖(Vᗮ).starProjection y‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection y V
    have h1 := hcos y hy
    have hsq : ‖(Vᗮ).starProjection y‖ ^ 2 ≤
        ((Real.sqrt 2 / 2) * ‖y‖) ^ 2 := by
      rw [mul_pow, hrootsq]
      linarith
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Real.sqrt 2 / 2) * ‖y‖)] at hle
  have htgt : ∀ w ∈ Uᗮ, ‖V.starProjection w‖ ≤ (Real.sqrt 2 / 2) * ‖w‖ := fun w hw =>
    norm_projection_apply_le_of_directRotation U V T hT hsource_sa hcomplement_sa
      hroot hsrc w hw
  have hx : ‖x‖ ^ 2 =
      ‖U.starProjection x‖ ^ 2 + ‖(Uᗮ).starProjection x‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection x U
  have hU : ‖U.starProjection x‖ ^ 2 / 2 ≤ ‖V.starProjection (U.starProjection x)‖ ^ 2 :=
    hcos _ (U.starProjection_apply_mem x)
  have hUc : ‖(Uᗮ).starProjection x‖ ^ 2 / 2 ≤
      ‖(Vᗮ).starProjection ((Uᗮ).starProjection x)‖ ^ 2 := by
    have hw := htgt _ (Uᗮ.starProjection_apply_mem x)
    have hpy : ‖(Uᗮ).starProjection x‖ ^ 2 =
        ‖V.starProjection ((Uᗮ).starProjection x)‖ ^ 2 +
          ‖(Vᗮ).starProjection ((Uᗮ).starProjection x)‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection _ V
    have hsq : ‖V.starProjection ((Uᗮ).starProjection x)‖ ^ 2 ≤
        1 / 2 * ‖(Uᗮ).starProjection x‖ ^ 2 := by
      have h := mul_self_le_mul_self
        (norm_nonneg (V.starProjection ((Uᗮ).starProjection x))) hw
      rw [← pow_two, ← pow_two, mul_pow, hrootsq] at h
      exact h
    linarith
  rw [re_inner_halmosCosineSq_self U V x]
  linarith


/-- **The printed half-angle hypothesis implies the whole-space form bound.**

Davis and Kahan write `C₀² ≥ ½`, an inequality between operators on `X(E₀) = Pℋ` -- by
equation (3.7), `C₀² = E₀⋆ Q E₀`, so its quadratic form at `x ∈ Pℋ` is `‖Qx‖²`, and the
printed inequality is exactly `hcos`.  What the accretivity argument needs is the same bound
for `cos²Θ` on all of `ℋ`, which adds the companion `C₁² ≥ ½` on `Ptildeℋ`; that companion is
*not* a consequence of `hcos` for an arbitrary pair, and is one here because the acute case
supplies a unitary intertwiner whose two crossed blocks are adjoint
(`norm_projection_apply_le_of_forall_mem_source`). -/
theorem re_inner_halmosCosineSq_sub_half_nonneg_of_source
    (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) (x : H) :
    0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2 := by
  have hroot : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hrootsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h2]
    norm_num
  have hsrc : ∀ y ∈ U, ‖(Vᗮ).starProjection y‖ ≤ (Real.sqrt 2 / 2) * ‖y‖ := by
    intro y hy
    have hpy : ‖y‖ ^ 2 =
        ‖V.starProjection y‖ ^ 2 + ‖(Vᗮ).starProjection y‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection y V
    have h1 := hcos y hy
    have hsq : ‖(Vᗮ).starProjection y‖ ^ 2 ≤ ((Real.sqrt 2 / 2) * ‖y‖) ^ 2 := by
      rw [mul_pow, hrootsq]
      linarith
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (Real.sqrt 2 / 2) * ‖y‖)] at hle
  have htgt : ∀ w ∈ Uᗮ, ‖V.starProjection w‖ ≤ (Real.sqrt 2 / 2) * ‖w‖ := fun w hw =>
    norm_projection_apply_le_of_forall_mem_source U V hacute hroot hsrc w hw
  have hx : ‖x‖ ^ 2 =
      ‖U.starProjection x‖ ^ 2 + ‖(Uᗮ).starProjection x‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection x U
  have hU : ‖U.starProjection x‖ ^ 2 / 2 ≤ ‖V.starProjection (U.starProjection x)‖ ^ 2 :=
    hcos _ (U.starProjection_apply_mem x)
  have hUc : ‖(Uᗮ).starProjection x‖ ^ 2 / 2 ≤
      ‖(Vᗮ).starProjection ((Uᗮ).starProjection x)‖ ^ 2 := by
    have hw := htgt _ (Uᗮ.starProjection_apply_mem x)
    have hpy : ‖(Uᗮ).starProjection x‖ ^ 2 =
        ‖V.starProjection ((Uᗮ).starProjection x)‖ ^ 2 +
          ‖(Vᗮ).starProjection ((Uᗮ).starProjection x)‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection _ V
    have hsq : ‖V.starProjection ((Uᗮ).starProjection x)‖ ^ 2 ≤
        1 / 2 * ‖(Uᗮ).starProjection x‖ ^ 2 := by
      have h := mul_self_le_mul_self (norm_nonneg
        (V.starProjection ((Uᗮ).starProjection x))) hw
      rw [← pow_two, ← pow_two, mul_pow, hrootsq] at h
      exact h
    linarith
  rw [re_inner_halmosCosineSq_self U V x]
  linarith

omit [CompleteSpace H] in
/-- The reflection through a subspace fixes its own projection, on the left. -/
theorem reflectionOperator_mul_projection_self :
    V.reflectionOperator * V.starProjection = V.starProjection := by
  rw [reflectionOperator_eq_projection_add_projection_sub_one V]
  have hPV2 := projection_sq V
  noncomm_ring [hPV2]

omit [CompleteSpace H] in
/-- The reflection through a subspace fixes its own projection, on the right. -/
theorem projection_mul_reflectionOperator_self :
    V.starProjection * V.reflectionOperator = V.starProjection := by
  rw [reflectionOperator_eq_projection_add_projection_sub_one V]
  have hPV2 := projection_sq V
  noncomm_ring [hPV2]

/-- An operator whose numerical range is nonnegative has positive Hermitian part. -/
theorem nonneg_add_star_of_re_inner_nonneg (T : H →L[ℂ] H)
    (hre : ∀ x : H, 0 ≤ RCLike.re ⟪T x, x⟫_ℂ) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  refine (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ?_
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun x => ?_⟩
  · rw [IsSelfAdjoint, star_add, star_star, add_comm]
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have hstar : RCLike.re ⟪star T x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      exact inner_re_symm x (T x)
    have hsplit : RCLike.re ⟪(T + star T) x, x⟫_ℂ =
        RCLike.re ⟪T x, x⟫_ℂ + RCLike.re ⟪star T x, x⟫_ℂ := by
      rw [add_apply, inner_add_left, map_add]
    rw [hsplit, hstar]
    have := hre x
    linarith

/-- Reflection through the mirror image `reflectedSubspace V U` is the
conjugate of the reflection through `U` by the reflection through `V`.
Since the mirror image has projection `R_V P_U R_V`, its reflection
`2 P - 1` equals `R_V (2 P_U - 1) R_V = R_V R_U R_V`. -/
theorem reflectionOperator_reflectedSubspace :
    Submodule.reflectionOperator (reflectedSubspace V U)
      = V.reflectionOperator * U.reflectionOperator * V.reflectionOperator := by
  have hRR : V.reflectionOperator * V.reflectionOperator = 1 :=
    reflectionOperator_mul_self_complex V
  have hPVref : Submodule.starProjection (reflectedSubspace V U)
      = V.reflectionOperator * U.starProjection * V.reflectionOperator :=
    starProjection_reflectedSubspace V U
  rw [reflectionOperator_eq_projection_add_projection_sub_one (reflectedSubspace V U),
      reflectionOperator_eq_projection_add_projection_sub_one U, hPVref]
  have expand : V.reflectionOperator * (U.starProjection + U.starProjection - 1)
      * V.reflectionOperator
      = V.reflectionOperator * U.starProjection * V.reflectionOperator
        + V.reflectionOperator * U.starProjection * V.reflectionOperator
        - V.reflectionOperator * V.reflectionOperator := by noncomm_ring
  rw [expand, hRR]

/-- The canonical intertwiner and the Halmos cosine square carry the same
numerical real part.  The Hermitian part of `S` is `S⋆ S = |S| ^ 2`, which is
exactly `halmosCosineSq U V`, so `re ⟪S x, x⟫ = re ⟪halmosCosineSq x, x⟫`. -/
theorem re_inner_intertwiner_eq_cosineSq (x : H) :
    RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ
      = RCLike.re ⟪halmosCosineSq U V x, x⟫_ℂ := by
  have hSstar : spectraCanonicalIntertwiner U V
        + star (spectraCanonicalIntertwiner U V)
      = halmosCosineSq U V + halmosCosineSq U V := by
    rw [spectraCanonicalIntertwiner_add_star U V,
      ← ContinuousLinearMap.modulus_mul_self_eq_star_mul_self,
      spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq]
  have h := congrArg (fun T : H →L[ℂ] H => RCLike.re ⟪T x, x⟫_ℂ) hSstar
  have hstar : RCLike.re ⟪star (spectraCanonicalIntertwiner U V) x, x⟫_ℂ
      = RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
    exact inner_re_symm x (spectraCanonicalIntertwiner U V x)
  simp only [add_apply, inner_add_left, map_add, hstar] at h
  linarith

/-- Under the corrected half-angle bound (cosine *square* at least `1/2`), the
ordered reflection product `R_V R_U` is accretive.  Using `2 S = 1 + R_V R_U`
one has `re ⟪(R_V R_U) x, x⟫ = 2 * re ⟪halmosCosineSq x, x⟫ - ‖x‖ ^ 2`, which is
nonnegative precisely when `re ⟪halmosCosineSq x, x⟫ ≥ ‖x‖ ^ 2 / 2`. -/
theorem re_inner_reflectionProduct_nonneg
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2)
    (x : H) :
    0 ≤ RCLike.re ⟪spectraReflectionProduct U V x, x⟫_ℂ := by
  have hG : spectraReflectionProduct U V
      = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V - 1 := by
    have h1 : spectraReflectionProduct U V + 1
        = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [add_comm]
      exact (spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V).symm
    exact eq_sub_of_add_eq h1
  have hcos : RCLike.re ⟪spectraCanonicalIntertwiner U V x, x⟫_ℂ
      = RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ := by
    rw [re_inner_intertwiner_eq_cosineSq U V x]
    exact (inner_re_symm _ _).symm
  have hself : RCLike.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq]
  rw [hG]
  simp only [sub_apply, add_apply,
    one_apply_eq_self, inner_sub_left, inner_add_left, map_sub, map_add,
    hself, hcos]
  have := hhalf x
  linarith

end DavisKahan
end TauCeti
