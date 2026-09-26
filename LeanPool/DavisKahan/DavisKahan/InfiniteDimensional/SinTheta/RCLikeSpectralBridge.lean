/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.SpectralBridge
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Restriction
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! # RCLike Spectral Bridge -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# `RCLike` spectral-bridge lemmas

The affine-shift estimates in
`DavisKahan.InfiniteDimensional.SinTheta.SpectralBridge` were written
against a `RCLikeSpectralBridge.*` namespace (plus `centered_sylvester_equation`
and `boundedInverseDataOfIsUnit`) that had no definitions anywhere in the tree,
so that file could not elaborate and neither could `SinTheta/General.lean`
downstream.  This file supplies that machinery — now with **no leaf
obligations**:

* the Sylvester recentering identity and the `IsUnit`→bounded-inverse
  constructor (algebra);
* the self-adjoint operator-norm/spectral-radius bound, via the `RCLike`
  Rayleigh theorem;
* `isUnit_sub_smul_one_of_im_ne_zero`: a symmetric pencil at a non-real
  spectral parameter is invertible.  The numerical range of a symmetric
  operator is real, so `A - z` and its star are bounded below by `|im z|`;
  bounded below gives a closed range with trivial orthogonal complement, and
  the open mapping theorem upgrades the bijection to a unit.  This yields
  `mem_spectrum_sub_real_scalar_iff` directly over `RCLike` — no
  complexification;
* `spectrum_inverse_of_isUnit`, from `spectrum.map_inv` (any scalar field);
* symmetry of the inverse of a symmetric unit, hence its norm bound through
  the Rayleigh estimate.

A previously stated leaf `norm_le_of_normal_spectrum_norm_le` (normal-operator
norm/spectral-radius bound over `RCLike`) was **removed as false**: over `ℝ`
the rotation by `π/2` of the plane is star-normal with empty real spectrum, so
the claimed bound would force it to vanish.  Its only consumer needed the
self-adjoint case, which is `norm_le_of_selfAdjoint_spectrum_subset_closedBall`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Recentering a Sylvester equation by a real scalar leaves the right-hand side
unchanged: `(A - c)X - X(B - c) = AX - XB`. -/
theorem centered_sylvester_equation
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (X C : F →L[𝕜] E) (c : ℝ)
    (hEq : A ∘L X - X ∘L B = C) :
    (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ∘L X -
      X ∘L (B - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F) = C := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, ← hEq]
  abel

/-- A unit of the bounded-operator ring carries two-sided bounded-inverse data. -/
noncomputable def boundedInverseDataOfIsUnit {T : E →L[𝕜] E} (hunit : IsUnit T) :
    BoundedInverseData T where
  inv := ↑hunit.unit⁻¹
  left_inv := by have h := hunit.unit.inv_mul; rw [hunit.unit_spec] at h; exact h
  right_inv := by have h := hunit.unit.mul_inv; rw [hunit.unit_spec] at h; exact h

omit [CompleteSpace E] in
/-- A real scalar multiple of the identity is a symmetric operator. -/
theorem isSymmetric_real_smul_id (c : ℝ) :
    (((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E).IsSymmetric := fun x y => by
  simp [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]

namespace RCLikeSpectralBridge

omit [CompleteSpace E] in
/-- The numerical range of a symmetric operator is real. -/
theorem im_inner_map_self_eq_zero
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (x : E) :
    RCLike.im ⟪A x, x⟫_𝕜 = 0 := by
  rw [← RCLike.conj_eq_iff_im, inner_conj_symm]
  exact (hA x x).symm

omit [CompleteSpace E] in
/-- A symmetric pencil at a spectral parameter with nonzero imaginary part is
bounded below by `|im z|`. -/
theorem abs_im_mul_norm_le_norm_sub_smul_apply
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (z : 𝕜) (x : E) :
    |RCLike.im z| * ‖x‖ ≤ ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hinner : ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 =
      ⟪A x, x⟫_𝕜 - (starRingEnd 𝕜) z * ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left]
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  have him : RCLike.im ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 =
      RCLike.im z * ‖x‖ ^ 2 := by
    rw [hinner, map_sub, im_inner_map_self_eq_zero hA, zero_sub, RCLike.mul_im]
    simp only [RCLike.ofReal_im, RCLike.ofReal_re, RCLike.conj_im,
      RCLike.conj_re, mul_zero, zero_add]
    ring
  have habs : |RCLike.im z| * ‖x‖ ^ 2 ≤
      ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ * ‖x‖ := by
    calc |RCLike.im z| * ‖x‖ ^ 2
        = |RCLike.im z * ‖x‖ ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2)]
      _ = |RCLike.im ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜| := by
          rw [him]
      _ ≤ ‖⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜‖ :=
          RCLike.abs_im_le_norm _
      _ ≤ ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ * ‖x‖ :=
          norm_inner_le_norm _ _
  nlinarith [habs, hxpos, norm_nonneg ((A - z • ContinuousLinearMap.id 𝕜 E) x)]

/-- The star of the pencil is the pencil at the conjugate parameter. -/
theorem star_sub_smul
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (z : 𝕜) :
    star (A - z • ContinuousLinearMap.id 𝕜 E) =
      A - (starRingEnd 𝕜) z • ContinuousLinearMap.id 𝕜 E := by
  have hASA : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hid : star (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E := by
    change star (1 : E →L[𝕜] E) = (1 : E →L[𝕜] E)
    exact star_one _
  rw [star_sub, star_smul, hASA.star_eq, hid]
  rfl

/-- **A symmetric pencil at a non-real parameter is invertible.**  Both the
pencil and its star are bounded below, so the pencil is injective with closed
range whose orthogonal complement is trivial; the open mapping theorem then
provides a bounded two-sided inverse. -/
theorem isUnit_sub_smul_one_of_im_ne_zero
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    IsUnit (A - z • ContinuousLinearMap.id 𝕜 E) := by
  set T : E →L[𝕜] E := A - z • ContinuousLinearMap.id 𝕜 E with hT
  have himpos : (0 : ℝ) < |RCLike.im z| := abs_pos.mpr hz
  have hTlow : ∀ x, |RCLike.im z| * ‖x‖ ≤ ‖T x‖ :=
    abs_im_mul_norm_le_norm_sub_smul_apply hA z
  have hstarlow : ∀ x, |RCLike.im z| * ‖x‖ ≤ ‖star T x‖ := by
    intro x
    have h := abs_im_mul_norm_le_norm_sub_smul_apply hA ((starRingEnd 𝕜) z) x
    rw [RCLike.conj_im, abs_neg] at h
    rw [hT, star_sub_smul hA]
    exact h
  have hanti : AntilipschitzWith (|RCLike.im z|⁻¹).toNNReal T := by
    apply T.antilipschitz_of_bound
    intro x
    rw [Real.coe_toNNReal _ (by positivity)]
    calc ‖x‖ = |RCLike.im z|⁻¹ * (|RCLike.im z| * ‖x‖) := by
          field_simp
      _ ≤ |RCLike.im z|⁻¹ * ‖T x‖ := by
          gcongr
          exact hTlow x
  have hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hxk
    have hx0 : T x = 0 := LinearMap.mem_ker.mp hxk
    have h := hTlow x
    rw [hx0, norm_zero] at h
    have hle : ‖x‖ ≤ 0 := by nlinarith
    exact norm_le_zero_iff.mp hle
  have hclosed : IsClosed ((LinearMap.range (T : E →ₗ[𝕜] E)) : Set E) := by
    have h := hanti.isClosed_range T.uniformContinuous
    have hset : ((LinearMap.range (T : E →ₗ[𝕜] E)) : Set E) = Set.range ⇑T := by
      ext y
      simp [LinearMap.mem_range]
    rw [hset]
    exact h
  have hbot : (LinearMap.range (T : E →ₗ[𝕜] E))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hstary : star T y = 0 := by
      have hall : ∀ x, ⟪x, star T y⟫_𝕜 = 0 := by
        intro x
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
        exact hy (T x) ⟨x, rfl⟩
      have h := hall (star T y)
      rwa [inner_self_eq_zero] at h
    have h := hstarlow y
    rw [hstary, norm_zero] at h
    have : ‖y‖ ≤ 0 := by
      by_contra hpos
      push Not at hpos
      nlinarith
    exact norm_le_zero_iff.mp this
  have hrange : LinearMap.range (T : E →ₗ[𝕜] E) = ⊤ := by
    have : (LinearMap.range (T : E →ₗ[𝕜] E)).HasOrthogonalProjection := by
      have : CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] E)) :=
        hclosed.completeSpace_coe
      infer_instance
    exact (Submodule.orthogonal_eq_bot_iff).mp hbot
  let e := ContinuousLinearEquiv.ofBijective T hker hrange
  have hcoe : (e : E →L[𝕜] E) = T := ContinuousLinearEquiv.coe_ofBijective T hker hrange
  refine ⟨⟨T, (e.symm : E →L[𝕜] E), ?_, ?_⟩, rfl⟩
  · ext x
    have h1 : T ((e.symm : E →L[𝕜] E) x) = e (e.symm x) := by
      rw [← hcoe]; rfl
    calc (T * (e.symm : E →L[𝕜] E)) x
        = T ((e.symm : E →L[𝕜] E) x) := rfl
      _ = e (e.symm x) := h1
      _ = x := e.apply_symm_apply x
      _ = (1 : E →L[𝕜] E) x := rfl
  · ext x
    have h1 : (e.symm : E →L[𝕜] E) (T x) = e.symm (e x) := by
      rw [← hcoe]; rfl
    calc ((e.symm : E →L[𝕜] E) * T) x
        = (e.symm : E →L[𝕜] E) (T x) := rfl
      _ = e.symm (e x) := h1
      _ = x := e.symm_apply_apply x
      _ = (1 : E →L[𝕜] E) x := rfl

/-- For self-adjoint `A`, every point of `σ(A - c·1)` is real and comes from
`σ(A)`: non-real spectral parameters are excluded by
`isUnit_sub_smul_one_of_im_ne_zero`, and the affine spectral mapping is
`spectrum.sub_singleton_eq`.

This is the forward half; `mem_spectrum_sub_real_scalar_iff` below packages it
with the converse, which needs no self-adjointness. -/
theorem exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {c : ℝ} {z : 𝕜}
    (hz : z ∈ spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)) :
    ∃ r : ℝ, r ∈ boundedRealSpectrum A ∧ z = (((r - c : ℝ)) : 𝕜) := by
  have hpencil : A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E =
      A - algebraMap 𝕜 (E →L[𝕜] E) ((c : ℝ) : 𝕜) := by
    congr 1
  rw [hpencil, ← spectrum.sub_singleton_eq] at hz
  obtain ⟨w, hw, v, hv, hzw⟩ := Set.mem_sub.mp hz
  rw [Set.mem_singleton_iff] at hv
  subst hv
  have him : RCLike.im w = 0 := by
    by_contra hne
    have hunit := isUnit_sub_smul_one_of_im_ne_zero hA hne
    have hnot : w ∉ spectrum 𝕜 A := by
      rw [spectrum.notMem_iff]
      have h := hunit.neg
      rw [neg_sub] at h
      have hpen2 : algebraMap 𝕜 (E →L[𝕜] E) w =
          w • ContinuousLinearMap.id 𝕜 E :=
        @Algebra.algebraMap_eq_smul_one 𝕜 (E →L[𝕜] E) _ _ _ w
      rw [hpen2]
      exact h
    exact hnot hw
  have hw_real : w = ((RCLike.re w : ℝ) : 𝕜) := by
    conv_lhs => rw [← RCLike.re_add_im w]
    rw [him]
    simp
  refine ⟨RCLike.re w, ?_, ?_⟩
  · rw [DavisKahanExt.boundedRealSpectrum_eq_realSpectrum]
    change ((RCLike.re w : ℝ) : 𝕜) ∈ spectrum 𝕜 A
    rw [← hw_real]
    exact hw
  · rw [← hzw, hw_real]
    push_cast
    ring

omit [CompleteSpace E] in
/-- The converse inclusion, which holds for **any** bounded operator: shifting a
real spectral point by `c` lands in the spectrum of the shifted pencil.

Self-adjointness is what makes the *forward* direction true — it is what forces
the spectrum of the pencil to be real — and it is not needed here.  Keeping the
two halves separate records that asymmetry instead of burying it in a hypothesis
the `iff` carries for only one of its directions. -/
theorem mem_spectrum_sub_real_scalar_of_mem_boundedRealSpectrum
    {A : E →L[𝕜] E} {c r : ℝ} (hr : r ∈ boundedRealSpectrum A) :
    (((r - c : ℝ)) : 𝕜) ∈
      spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) := by
  have hpencil : A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E =
      A - algebraMap 𝕜 (E →L[𝕜] E) ((c : ℝ) : 𝕜) := by
    congr 1
  rw [hpencil, ← spectrum.sub_singleton_eq]
  refine Set.mem_sub.mpr ⟨((r : ℝ) : 𝕜), ?_, ((c : ℝ) : 𝕜), rfl, ?_⟩
  · rw [DavisKahanExt.boundedRealSpectrum_eq_realSpectrum] at hr
    exact hr
  · push_cast
    ring

/-- **The spectrum of the real pencil, as an actual `Iff`.**

`σ(A - c·1) = σ(A) - c`, in membership form.  The name previously sat on the
forward implication alone, which the naming rubric forbids: `_iff` asserts an
`Iff`.  The fix was to supply the converse rather than to weaken the name, since
the original docstring already claimed the equality. -/
theorem mem_spectrum_sub_real_scalar_iff
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {c : ℝ} {z : 𝕜} :
    z ∈ spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ↔
      ∃ r : ℝ, r ∈ boundedRealSpectrum A ∧ z = (((r - c : ℝ)) : 𝕜) :=
  ⟨fun hz => exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar hA hz,
   fun ⟨_r, hr, hz⟩ => hz ▸ mem_spectrum_sub_real_scalar_of_mem_boundedRealSpectrum hr⟩

/-- A self-adjoint operator whose spectrum sits in the closed ball of radius `ρ`
has operator norm at most `ρ`.  Proof: its norm equals its spectral radius
(`RCLike` Rayleigh theorem), which is bounded by `ρ`. -/
theorem norm_le_of_selfAdjoint_spectrum_subset_closedBall
    {T : E →L[𝕜] E} (hSelf : T.IsSymmetric) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hspec : spectrum 𝕜 T ⊆ Metric.closedBall 0 ρ) : ‖T‖ ≤ ρ := by
  have hSA : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hSelf
  have hrad : spectralRadius 𝕜 T = ‖T‖₊ := ContinuousLinearMap.spectralRadius_eq_nnnorm T hSA
  have hbound : spectralRadius 𝕜 T ≤ (ρ.toNNReal : ENNReal) := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun z hz => ?_
    have hzρ : ‖z‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hspec hz
    have : ‖z‖₊ ≤ ρ.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal ρ hρ]; exact hzρ
    exact_mod_cast this
  rw [hrad] at hbound
  have hnn : ‖T‖₊ ≤ ρ.toNNReal := by exact_mod_cast hbound
  calc ‖T‖ = (‖T‖₊ : ℝ) := rfl
    _ ≤ (ρ.toNNReal : ℝ) := by exact_mod_cast hnn
    _ = ρ := Real.coe_toNNReal ρ hρ

omit [CompleteSpace E] in
/-- The spectral-mapping identity `σ(T⁻¹) = σ(T)⁻¹` for a bounded unit,
from `spectrum.map_inv` (any scalar field). -/
theorem spectrum_inverse_of_isUnit {T : E →L[𝕜] E} (hunit : IsUnit T) :
    spectrum 𝕜 (boundedInverseDataOfIsUnit hunit).inv =
      (fun z : 𝕜 => z⁻¹) '' spectrum 𝕜 T := by
  have h := spectrum.map_inv (𝕜 := 𝕜) hunit.unit
  rw [hunit.unit_spec] at h
  have hinv : (boundedInverseDataOfIsUnit hunit).inv =
      ((hunit.unit⁻¹ : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) := rfl
  rw [hinv, ← h, Set.image_inv_eq_inv]

/-- The inverse of a symmetric unit is symmetric: its star is a left inverse
of `T`, so by uniqueness it is the inverse. -/
theorem inverse_isSymmetric {T : E →L[𝕜] E} (hTself : T.IsSymmetric)
    (hunit : IsUnit T) :
    ((boundedInverseDataOfIsUnit hunit).inv).IsSymmetric := by
  set D := boundedInverseDataOfIsUnit hunit with hD
  have hTSA : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTself
  have hleft : (star D.inv) ∘L T = ContinuousLinearMap.id 𝕜 E := by
    have h := congrArg (fun S : E →L[𝕜] E => star S) D.right_inv
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id] at h
    rwa [hTSA.adjoint_eq] at h
  have hself : IsSelfAdjoint D.inv := D.inv_eq hleft
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself

/-- The inverse of a symmetric unit is star-normal. -/
theorem inverse_isNormal {T : E →L[𝕜] E} (hTself : T.IsSymmetric) (hunit : IsUnit T) :
    IsStarNormal (boundedInverseDataOfIsUnit hunit).inv :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (inverse_isSymmetric hTself hunit)).isStarNormal

end RCLikeSpectralBridge
end ExactSinTheta
end DavisKahan
end TauCeti
