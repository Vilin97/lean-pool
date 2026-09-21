/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.BoundedBorelProjectionComplex
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedReduction

/-! # Spectral Gap Form Bounds -/

open TauCeti.DavisKahan.Sylvester

/-!
# Sharp form bounds on the spectral subspaces of an operator with a gap

If a bounded self-adjoint `B` has no spectrum in the open interval
`(alpha, alpha + delta)`, then its canonical spectral subspace for `Iic alpha`
carries the *sharp* form bound `re <B x, x> <= alpha ||x||^2`, and the
orthogonal complement carries `(alpha + delta) ||x||^2 <= re <B x, x>`.

Sharpness is the whole point.  The band estimate already in the Borel-calculus
layer (`norm_comp_boundedPVM_proj_sub_smul_le`) loses a factor of two, which is
fatal here: Davis--Kahan Section 8 feeds these two bounds straight into the
ordered-gap hypotheses of the quarter-angle theorem, and a lossy bound would
not close the gap at all.

The proof is the continuous functional calculus, made available by the gap
itself.  On the spectrum the indicator of `Iic alpha` *is* continuous, because
the gap makes `{t <= alpha}` relatively clopen there; concretely the affine
cutoff `spectralGapCutoff` agrees with the indicator on the spectrum.  So the
spectral projection is `cfcHom` of a continuous symbol, and each form bound is
the statement that a nonnegative continuous symbol has a nonnegative
functional-calculus image -- `(alpha - t) * chi(t)` for the low block and
`(t - alpha - delta) * (1 - chi(t))` for the high block.  Both are nonnegative
*on the spectrum* precisely because the open gap is empty.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open DavisKahan
open DavisKahan
open DavisKahan.Foundation

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### The cutoff symbol -/

/-- The affine cutoff that is `1` on `Iic alpha`, `0` on `Ici (alpha+delta)`,
and interpolates linearly in between. -/
def spectralGapCutoff (alpha delta t : ℝ) : ℝ :=
  max 0 (min 1 ((alpha + delta - t) / delta))

/-- The one-sided gap cutoff is continuous. -/
theorem continuous_spectralGapCutoff (alpha delta : ℝ) :
    Continuous (spectralGapCutoff alpha delta) := by
  unfold spectralGapCutoff
  fun_prop

/-- The one-sided gap cutoff is `1` below the gap. -/
theorem spectralGapCutoff_eq_one {alpha delta t : ℝ} (hdelta : 0 < delta)
    (ht : t ≤ alpha) : spectralGapCutoff alpha delta t = 1 := by
  have h1 : (1 : ℝ) ≤ (alpha + delta - t) / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  unfold spectralGapCutoff
  rw [min_eq_left h1, max_eq_right zero_le_one]

/-- The one-sided gap cutoff vanishes above the gap. -/
theorem spectralGapCutoff_eq_zero {alpha delta t : ℝ} (hdelta : 0 < delta)
    (ht : alpha + delta ≤ t) : spectralGapCutoff alpha delta t = 0 := by
  have h1 : (alpha + delta - t) / delta ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hdelta.le
  unfold spectralGapCutoff
  rw [max_eq_left (le_trans (min_le_right _ _) h1)]

/-! ### The symbol on the spectrum -/

variable (B : H →L[ℂ] H) (hB : B.IsSymmetric)

/-- The cutoff pulled back to the spectrum along the real-part coordinate. -/
def spectralGapSymbol (alpha delta : ℝ) : C(spectrum ℂ B, ℝ) :=
  ⟨fun w => spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w),
    (continuous_spectralGapCutoff alpha delta).comp
      (Complex.continuous_re.comp continuous_subtype_val)⟩

omit [CompleteSpace H] in
/-- Evaluating the gap symbol is evaluating the cutoff at the real part. -/
@[simp] theorem spectralGapSymbol_apply (alpha delta : ℝ) (w : spectrum ℂ B) :
    spectralGapSymbol B alpha delta w =
      spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w) := rfl

/-- The real-part coordinate of a spectral point is a point of the real
spectrum. -/
theorem reCoord_mem_realSpectrum (hB : B.IsSymmetric)
    (w : spectrum ℂ B) :
    TauCeti.BorelCalculus.reCoord w ∈ realSpectrum B := by
  have h := coe_reCoord B hB w
  change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ B
  rw [h]
  exact w.2

/-- **With a gap, the spectral projection is a continuous functional
calculus.**  The affine cutoff agrees with the indicator of `Iic alpha` at
every point of the spectrum, so it computes the same projection. -/
theorem boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic =
      cfcHom ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB).isStarNormal
        (TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta)) := by
  have h := boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees B hB
    (Set.Iic alpha) measurableSet_Iic
    (TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta)) ?_
  · rw [h]
    rfl
  · intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    by_cases hw : w ∈ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' Set.Iic alpha
    · have hle : TauCeti.BorelCalculus.reCoord w ≤ alpha := hw
      rw [Set.indicator_of_mem hw]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, spectralGapSymbol_apply,
        spectralGapCutoff_eq_one hdelta hle]
      norm_num
    · have hgt : alpha < TauCeti.BorelCalculus.reCoord w := lt_of_not_ge hw
      have hhigh : alpha + delta ≤ TauCeti.BorelCalculus.reCoord w := by
        rcases hmem with hlow | hhigh
        · exact absurd (Set.mem_Iic.mp hlow) (not_le_of_gt hgt)
        · exact Set.mem_Ici.mp hhigh
      rw [Set.indicator_of_notMem hw]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, spectralGapSymbol_apply,
        spectralGapCutoff_eq_zero hdelta hhigh]
      norm_num

/-! ### The two sharp form bounds -/

/-- **Sharp upper form bound on the low spectral subspace.** -/
theorem re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta))
    {x : H}
    (hx : x ∈ boundedSelfAdjointSpectralSubspace B hB (Set.Iic alpha)
      measurableSet_Iic) :
    RCLike.re ⟪B x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2 := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set E : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic
    with hEdef
  have hEx : E x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  -- the nonnegative symbol
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (alpha - TauCeti.BorelCalculus.reCoord w) *
        spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w),
      ((continuous_const.sub
        (Complex.continuous_re.comp continuous_subtype_val)).mul
        ((continuous_spectralGapCutoff alpha delta).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (alpha - TauCeti.BorelCalculus.reCoord w) *
      spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hlow | hhigh
    · rw [spectralGapCutoff_eq_one hdelta (Set.mem_Iic.mp hlow), mul_one]
      linarith [Set.mem_Iic.mp hlow]
    · rw [spectralGapCutoff_eq_zero hdelta (Set.mem_Ici.mp hhigh), mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((alpha : ℝ) : ℂ) •
            TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta) -
          ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its *value* equation rather than through `hgdef`: rewriting to the
    -- bundled structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no
    -- longer reduces, and `push_cast` then cannot reach the real-valued arithmetic inside.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (alpha - TauCeti.BorelCalculus.reCoord v) *
          spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord v) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      spectralGapSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom B hB hdelta hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (((alpha : ℝ) : ℂ) • E - B * E) x⟫_ℂ at hpos
  have happly : (((alpha : ℝ) : ℂ) • E - B * E) x =
      ((alpha : ℝ) : ℂ) • x - B x := by
    simp only [sub_apply, smul_apply, mul_apply_eq_comp,
      hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((alpha : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = alpha * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- **Sharp lower form bound on the complementary spectral subspace.** -/
theorem le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta))
    {x : H}
    (hx : x ∈ (boundedSelfAdjointSpectralSubspace B hB (Set.Iic alpha)
      measurableSet_Iic)ᗮ) :
    (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set E : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic
    with hEdef
  have hEx : E x = 0 := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (TauCeti.BorelCalculus.reCoord w - (alpha + delta)) *
        (1 - spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w)),
      (((Complex.continuous_re.comp continuous_subtype_val).sub
        continuous_const).mul
        (continuous_const.sub
          ((continuous_spectralGapCutoff alpha delta).comp
            (Complex.continuous_re.comp continuous_subtype_val))))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (TauCeti.BorelCalculus.reCoord w - (alpha + delta)) *
      (1 - spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w))
    rcases hmem with hlow | hhigh
    · rw [spectralGapCutoff_eq_one hdelta (Set.mem_Iic.mp hlow), sub_self, mul_zero]
    · rw [spectralGapCutoff_eq_zero hdelta (Set.mem_Ici.mp hhigh), sub_zero, mul_one]
      linarith [Set.mem_Ici.mp hhigh]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        (((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) -
            (((alpha + delta : ℝ) : ℂ)) • 1) *
          (1 - TauCeti.BorelCalculus.ofRealLM
            (spectralGapSymbol B alpha delta)) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Value equation rather than `hgdef`; see the same step in `re_inner_le_...` above.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (TauCeti.BorelCalculus.reCoord v - (alpha + delta)) *
          (1 - spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord v)) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.one_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, smul_eq_mul, spectralGapSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_mul, map_sub, map_sub, map_smul, map_one, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom B hB hdelta hgap] at hpos
  change 0 ≤ RCLike.re
    ⟪x, ((B - ((alpha + delta : ℝ) : ℂ) • 1) * (1 - E)) x⟫_ℂ at hpos
  have happly : ((B - ((alpha + delta : ℝ) : ℂ) • 1) * (1 - E)) x =
      B x - ((alpha + delta : ℝ) : ℂ) • x := by
    simp only [mul_apply_eq_comp, sub_apply,
      smul_apply, one_apply_eq_self, hEx, sub_zero]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((alpha + delta : ℝ) : ℂ) * ⟪x, x⟫_ℂ) =
      (alpha + delta) * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-! ## Form bounds and spectral confinement

The four bridges below turn a quadratic-form bound on a reducing subspace into
a `SpectrumIn` containment and back.  They are generic: no perturbation, no
angle and no Davis--Kahan content.  Both directions are used by the Section 8
band identification and by the source Theorem 8.1 statements.
-/

section FormBounds

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-! ### Form bounds give restricted-spectrum containments -/

omit [CompleteSpace F] in
/-- Over `ℂ` the real Banach-algebra spectrum and the pulled-back complex
spectrum are the same set. -/
theorem realSpectrum_eq_spectrum_real (T : F →L[ℂ] F) :
    realSpectrum T = spectrum ℝ T := by
  ext r
  show ((r : ℂ) ∈ spectrum ℂ T) ↔ r ∈ spectrum ℝ T
  rw [spectrum.mem_iff, spectrum.mem_iff, not_iff_not,
    IsScalarTower.algebraMap_apply ℝ ℂ (F →L[ℂ] F) r]
  rfl

/-- **A global upper form bound bounds the real spectrum above.**

No functional calculus: `r - T` is uniformly coercive for `r > c`, hence a unit
by operator Lax--Milgram, hence `r` is a resolvent point. -/
theorem realSpectrum_subset_Iic_of_re_inner_le
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : F →L[ℂ] F} {c : ℝ}
    (hform : ∀ z : F, RCLike.re ⟪T z, z⟫_ℂ ≤ c * ‖z‖ ^ 2) :
    realSpectrum T ⊆ Set.Iic c := by
  intro r hr
  by_contra hnot
  have hlt : c < r := lt_of_not_ge hnot
  have hsmul : ∀ z : F, RCLike.re ⟪((r : ℝ) : ℂ) • z, z⟫_ℂ = r * ‖z‖ ^ 2 := by
    intro z
    rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      show (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z]
    ring
  have hcoer : ∀ z : F, (r - c) * ‖z‖ ^ 2 ≤
      RCLike.re ⟪(((r : ℝ) : ℂ) • (1 : F →L[ℂ] F) - T) z, z⟫_ℂ := by
    intro z
    have h1 := hform z
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, map_sub]
    rw [hsmul z]
    linarith
  have hunit : IsUnit (((r : ℝ) : ℂ) • (1 : F →L[ℂ] F) - T) :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive (by linarith) hcoer
  have hspec : ((r : ℝ) : ℂ) ∈ spectrum ℂ T := hr
  rw [spectrum.mem_iff] at hspec
  apply hspec
  rw [Algebra.algebraMap_eq_smul_one]
  exact hunit

/-- **A global lower form bound bounds the real spectrum below.** -/
theorem realSpectrum_subset_Ici_of_le_re_inner
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : F →L[ℂ] F} {c : ℝ}
    (hform : ∀ z : F, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪T z, z⟫_ℂ) :
    realSpectrum T ⊆ Set.Ici c := by
  intro r hr
  by_contra hnot
  have hlt : r < c := lt_of_not_ge hnot
  have hsmul : ∀ z : F, RCLike.re ⟪((r : ℝ) : ℂ) • z, z⟫_ℂ = r * ‖z‖ ^ 2 := by
    intro z
    rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      show (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z]
    ring
  have hcoer : ∀ z : F, (c - r) * ‖z‖ ^ 2 ≤
      RCLike.re ⟪(T - ((r : ℝ) : ℂ) • (1 : F →L[ℂ] F)) z, z⟫_ℂ := by
    intro z
    have h1 := hform z
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, map_sub]
    rw [hsmul z]
    linarith
  have hunit : IsUnit (T - ((r : ℝ) : ℂ) • (1 : F →L[ℂ] F)) :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive (by linarith) hcoer
  have hspec : ((r : ℝ) : ℂ) ∈ spectrum ℂ T := hr
  rw [spectrum.mem_iff] at hspec
  apply hspec
  rw [Algebra.algebraMap_eq_smul_one]
  have hneg : ((r : ℝ) : ℂ) • (1 : F →L[ℂ] F) - T =
      -(T - ((r : ℝ) : ℂ) • (1 : F →L[ℂ] F)) := by module
  rw [hneg]
  exact hunit.neg

/-- `SpectrumIn` from an upper form bound on a reducing subspace. -/
theorem spectrumIn_Iic_of_re_inner_le
    {T : F →L[ℂ] F} {U : Submodule ℂ F}
    [U.HasOrthogonalProjection] (hU : ∀ x ∈ U, T x ∈ U) {c : ℝ}
    (hform : ∀ x ∈ U, RCLike.re ⟪T x, x⟫_ℂ ≤ c * ‖x‖ ^ 2) :
    SpectrumIn T U (Set.Iic c) := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  refine ⟨hU, ?_⟩
  rw [restrictedSpectrum_eq_restrictionSpectrum T U hU]
  intro r hr
  refine realSpectrum_subset_Iic_of_re_inner_le (T := T.restrict hU) ?_ hr
  intro z
  exact hform (z : F) z.2

/-- `SpectrumIn` from a lower form bound on a reducing subspace. -/
theorem spectrumIn_Ici_of_le_re_inner
    {T : F →L[ℂ] F} {U : Submodule ℂ F}
    [U.HasOrthogonalProjection] (hU : ∀ x ∈ U, T x ∈ U) {c : ℝ}
    (hform : ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ) :
    SpectrumIn T U (Set.Ici c) := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  refine ⟨hU, ?_⟩
  rw [restrictedSpectrum_eq_restrictionSpectrum T U hU]
  intro r hr
  refine realSpectrum_subset_Ici_of_le_re_inner (T := T.restrict hU) ?_ hr
  intro z
  exact hform (z : F) z.2

/-- A `SpectrumIn` upper half-line for a symmetric operator gives the
quadratic-form upper bound on the branch, through the restriction-spectrum
spectral-order bridge. -/
theorem re_inner_le_of_spectrumIn_Iic
    {T : F →L[ℂ] F} (hT : T.IsSymmetric) {W : Submodule ℂ F}
    [W.HasOrthogonalProjection] {a : ℝ}
    (h : SpectrumIn T W (Set.Iic a)) {y : F} (hy : y ∈ W) :
    RCLike.re ⟪y, T y⟫_ℂ ≤ a * ‖y‖ ^ 2 := by
  have hσ : spectrum ℝ (T.restrict h.invariant) ⊆ Set.Iic a := by
    intro r hr
    exact h.subset
      ⟨h.invariant, by simpa using (spectrum.algebraMap_mem_iff (S := ℂ)).mpr hr⟩
  have hb :=
    SpectralOrder.upperFormBoundOn_of_restriction_spectrum_subset_Iic
      hT h.invariant hσ y hy
  calc RCLike.re ⟪y, T y⟫_ℂ = RCLike.re ⟪T y, y⟫_ℂ :=
      (congrArg RCLike.re (hT y y)).symm
    _ ≤ a * ‖y‖ ^ 2 := hb

/-- A `SpectrumIn` lower half-line for a symmetric operator gives the
quadratic-form lower bound on the branch. -/
theorem le_re_inner_of_spectrumIn_Ici
    {T : F →L[ℂ] F} (hT : T.IsSymmetric) {W : Submodule ℂ F}
    [W.HasOrthogonalProjection] {b : ℝ}
    (h : SpectrumIn T W (Set.Ici b)) {y : F} (hy : y ∈ W) :
    b * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, T y⟫_ℂ := by
  have hσ : spectrum ℝ (T.restrict h.invariant) ⊆ Set.Ici b := by
    intro r hr
    exact h.subset
      ⟨h.invariant, by simpa using (spectrum.algebraMap_mem_iff (S := ℂ)).mpr hr⟩
  have hb :=
    SpectralOrder.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
      hT h.invariant hσ y hy
  calc b * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := hb
    _ = RCLike.re ⟪y, T y⟫_ℂ := congrArg RCLike.re (hT y y)


end FormBounds

end



end DavisKahanExt
end TauCeti
