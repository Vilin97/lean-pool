/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralGapFormBounds
-- supplies the one-sided `spectralGapCutoff`, `reCoord_mem_realSpectrum`, and the
-- bounded self-adjoint spectral projection this module makes two-sided.
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ResolventOperator
-- supplies `resolventOperator` and the sharp self-adjoint
-- distance-to-spectrum resolvent bound used by the exterior lower bound.
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
-- supplies `compressOperator` and its self-adjointness.
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.ContinuationWitnessOrientedBlocks

/-! # Central Band -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester
-- supplies `realSpectrum_compressOperator_eq_restrictedSpectrum`.

/-!
# The central spectral band of a two-sided gap configuration

A bounded self-adjoint operator `B` is in the *two-sided gap configuration*
`(l, r, d)` when its real spectrum misses both open gaps `(l - d, l)` and
`(r, r + d)`:

```
realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d
```

This module owns the spectral subspace that configuration selects -- the
`centralBandSubspace`, the spectral subspace for the open band
`centralBand l r d = Ioo (l - d/2) (r + d/2)` sitting strictly inside the
canonical gap circle -- together with the estimates that pin it down:

* `boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom`: with a gap on
  both sides the band projection is a *continuous* functional calculus, since
  the two-sided cutoff `bandCutoff` agrees with the indicator of the band at
  every point of the spectrum.  This is the two-sided companion of the
  one-sided statement in `SpectralGapFormBounds`.
* `re_inner_le_of_mem_centralBandSubspace` and
  `le_re_inner_of_mem_centralBandSubspace`: the sharp form bounds `l ≤ ⟪Bx,x⟫ ≤ r`
  on the band subspace.
* `norm_shiftedOperator_ge_of_mem_centralBandSubspace_orthogonal` and
  `norm_shiftedOperator_ge_of_spectrumIn_gapExterior`: the complement of the
  band, and any reducing subspace spectrally outside the two gaps, are bounded
  away from the centre `gapCenter l r` by `(r - l)/2 + d` after the shift.
* `commute_starProjection_centralBandSubspace`: because the band projection is
  a continuous functional calculus, it commutes with the projection onto any
  reducing subspace.

Nothing here mentions Davis--Kahan, a perturbation, or a homotopy: it is the
generic band-selection layer.  It was extracted verbatim from
`Sources/DavisKahan1970/Section8/Theorem82Branch.lean`, where Theorem 8.2 uses it to
follow a moving spectral band along an operator path.

## Scope

Complex scalars and a complete space, matching the bounded self-adjoint Borel
calculus it is built on.  `opNorm_le_of_abs_re_inner_le` is scalar-generic in
substance but is stated here at the same carrier as its consumers.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan


open DavisKahanExt
open TauCeti.DavisKahan.Foundation

universe u

/-! ## An operator helper

An ambient statement about a bounded self-adjoint operator; it mentions no
restriction, which keeps the subspace bookkeeping out of the analytic steps. -/

section Helpers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The numerical radius controls the norm.**  For a self-adjoint operator a
two-sided form bound is a norm bound, with no loss.  This is Mathlib's
Rayleigh-quotient description of the norm of a symmetric operator. -/
theorem opNorm_le_of_abs_re_inner_le {S : H →L[ℂ] H} (hS : S.IsSymmetric)
    {M : ℝ} (hM : 0 ≤ M)
    (hform : ∀ x : H, |RCLike.re ⟪S x, x⟫_ℂ| ≤ M * ‖x‖ ^ 2) : ‖S‖ ≤ M := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hS]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.rayleighQuotient] using hM
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    have h := hform x
    rw [ContinuousLinearMap.rayleighQuotient, abs_div,
      abs_of_nonneg hx2.le, div_le_iff₀ hx2]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact h

end Helpers

/-! ## The central band and its spectral projection

The band is `(l - d/2, r + d/2)`, the inside of the canonical gap circle for
the configuration `[l, r]` with gaps of width `d` on both sides.  When the
real spectrum misses both open gaps, the indicator of the band is continuous
*on the spectrum*, so the band spectral projection is a continuous functional
calculus, exactly as in the one-sided `SpectralGapFormBounds`. -/

section Band

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The exterior of a two-sided gap configuration. -/
def gapExterior (l r d : ℝ) : Set ℝ := {x : ℝ | x ≤ l - d ∨ r + d ≤ x}

/-- The central band strictly inside the canonical gap circle. -/
def centralBand (l r d : ℝ) : Set ℝ := Set.Ioo (l - d / 2) (r + d / 2)

/-- The central band is an open interval, hence measurable. -/
theorem measurableSet_centralBand (l r d : ℝ) :
    MeasurableSet (centralBand l r d) := measurableSet_Ioo

/-- The two-sided cutoff: the product of an upper and a lower one-sided
cutoff, written as a minimum since both take values in `[0,1]`. -/
def bandCutoff (l r d t : ℝ) : ℝ :=
  min (spectralGapCutoff r d t) (1 - spectralGapCutoff (l - d) d t)

/-- The one-sided cutoff is nonnegative. -/
theorem spectralGapCutoff_nonneg (a d t : ℝ) : 0 ≤ spectralGapCutoff a d t :=
  le_max_left _ _

/-- The one-sided cutoff is bounded by one. -/
theorem spectralGapCutoff_le_one (a d t : ℝ) : spectralGapCutoff a d t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The two-sided cutoff is continuous, being a minimum of continuous
functions. -/
theorem continuous_bandCutoff (l r d : ℝ) : Continuous (bandCutoff l r d) :=
  (continuous_spectralGapCutoff r d).min
    (continuous_const.sub (continuous_spectralGapCutoff (l - d) d))

/-- The two-sided cutoff is nonnegative. -/
theorem bandCutoff_nonneg (l r d t : ℝ) : 0 ≤ bandCutoff l r d t :=
  le_min (spectralGapCutoff_nonneg _ _ _)
    (by linarith [spectralGapCutoff_le_one (l - d) d t])

/-- The two-sided cutoff is bounded by one. -/
theorem bandCutoff_le_one (l r d t : ℝ) : bandCutoff l r d t ≤ 1 :=
  (min_le_left _ _).trans (spectralGapCutoff_le_one _ _ _)

/-- The two-sided cutoff is `1` on the selected interval `[l, r]`. -/
theorem bandCutoff_eq_one {l r d t : ℝ} (hd : 0 < d) (ht : t ∈ Set.Icc l r) :
    bandCutoff l r d t = 1 := by
  have h1 : spectralGapCutoff r d t = 1 := spectralGapCutoff_eq_one hd ht.2
  have h2 : spectralGapCutoff (l - d) d t = 0 :=
    spectralGapCutoff_eq_zero hd (by linarith [ht.1])
  rw [bandCutoff, h1, h2]
  norm_num

/-- The two-sided cutoff vanishes on the gap exterior. -/
theorem bandCutoff_eq_zero {l r d t : ℝ} (hd : 0 < d) (ht : t ∈ gapExterior l r d) :
    bandCutoff l r d t = 0 := by
  rcases ht with hlow | hhigh
  · have h2 : spectralGapCutoff (l - d) d t = 1 :=
      spectralGapCutoff_eq_one hd hlow
    rw [bandCutoff, h2, sub_self]
    exact min_eq_right (spectralGapCutoff_nonneg _ _ _)
  · have h1 : spectralGapCutoff r d t = 0 :=
      spectralGapCutoff_eq_zero hd hhigh
    rw [bandCutoff, h1]
    exact min_eq_left (by linarith [spectralGapCutoff_le_one (l - d) d t])

/-- The two-sided cutoff pulled back to the spectrum along the real part. -/
def bandSymbol (B : H →L[ℂ] H) (l r d : ℝ) : C(spectrum ℂ B, ℝ) :=
  ⟨fun w => bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
    (continuous_bandCutoff l r d).comp
      (Complex.continuous_re.comp continuous_subtype_val)⟩

omit [CompleteSpace H] in
/-- Evaluating the band symbol is evaluating the cutoff at the real part. -/
@[simp] theorem bandSymbol_apply (B : H →L[ℂ] H) (l r d : ℝ) (w : spectrum ℂ B) :
    bandSymbol B l r d w = bandCutoff l r d (TauCeti.BorelCalculus.reCoord w) := rfl

variable (B : H →L[ℂ] H) (hB : B.IsSymmetric)

/-- **With a two-sided gap, the band spectral projection is a continuous
functional calculus.**  The two-sided cutoff agrees with the indicator of the
band at every point of the spectrum. -/
theorem boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d) :
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
        (measurableSet_centralBand l r d) =
      cfcHom ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB).isStarNormal
        (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) := by
  have h := boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees B hB
    (centralBand l r d) (measurableSet_centralBand l r d)
    (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) ?_
  · rw [h]; rfl
  · intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    rcases hmem with hin | hout
    · have hband : w ∈ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' centralBand l r d := by
        refine ⟨by linarith [hin.1], by linarith [hin.2]⟩
      rw [Set.indicator_of_mem hband]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, bandSymbol_apply,
        bandCutoff_eq_one hd hin]
      norm_num
    · have hband : w ∉ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' centralBand l r d := by
        intro hmem'
        rcases hout with hlow | hhigh
        · exact absurd hmem'.1 (by simp; linarith)
        · exact absurd hmem'.2 (by simp; linarith)
      rw [Set.indicator_of_notMem hband]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, bandSymbol_apply,
        bandCutoff_eq_zero hd hout]
      norm_num

/-- The spectral subspace of the central band. -/
def centralBandSubspace {l r d : ℝ} : Submodule ℂ H :=
  boundedSelfAdjointSpectralSubspace B hB (centralBand l r d)
    (measurableSet_centralBand l r d)

/-- The band subspace is a spectral subspace, so it is orthogonally
complemented. -/
instance centralBandSubspace_hasOrthogonalProjection {l r d : ℝ} :
    (centralBandSubspace B hB (l := l) (r := r) (d := d)).HasOrthogonalProjection :=
  boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection B hB _ _

/-- The band subspace reduces the operator it is cut from. -/
theorem centralBandSubspace_reduces {l r d : ℝ} :
    B.Reduces (centralBandSubspace B hB (l := l) (r := r) (d := d)) :=
  boundedSelfAdjointSpectralSubspace_reduces B hB _ _

/-- The orthogonal projection onto the band subspace is the band spectral
projection. -/
theorem starProjection_centralBandSubspace {l r d : ℝ} :
    (centralBandSubspace B hB (l := l) (r := r) (d := d)).starProjection =
      boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
        (measurableSet_centralBand l r d) :=
  (boundedSelfAdjointSpectralProjection_eq_starProjection B hB _ _).symm

/-- **Sharp upper form bound on the band spectral subspace.** -/
theorem re_inner_le_of_mem_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d)) :
    RCLike.re ⟪B x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (r - TauCeti.BorelCalculus.reCoord w) *
        bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
      ((continuous_const.sub
        (Complex.continuous_re.comp continuous_subtype_val)).mul
        ((continuous_bandCutoff l r d).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (r - TauCeti.BorelCalculus.reCoord w) *
      bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, mul_one]
      linarith [hin.2]
    · rw [bandCutoff_eq_zero hd hout, mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((r : ℝ) : ℂ) • TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) -
          ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (r - TauCeti.BorelCalculus.reCoord v) *
          bandCutoff l r d (TauCeti.BorelCalculus.reCoord v) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (((r : ℝ) : ℂ) • Epr - B * Epr) x⟫_ℂ at hpos
  have happly : (((r : ℝ) : ℂ) • Epr - B * Epr) x = ((r : ℝ) : ℂ) • x - B x := by
    simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp, hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((r : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = r * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- **Sharp lower form bound on the band spectral subspace.** -/
theorem le_re_inner_of_mem_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d)) :
    l * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (TauCeti.BorelCalculus.reCoord w - l) *
        bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
      (((Complex.continuous_re.comp continuous_subtype_val).sub
        continuous_const).mul
        ((continuous_bandCutoff l r d).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (TauCeti.BorelCalculus.reCoord w - l) *
      bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, mul_one]
      linarith [hin.1]
    · rw [bandCutoff_eq_zero hd hout, mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) -
          ((l : ℝ) : ℂ) • TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (TauCeti.BorelCalculus.reCoord v - l) *
          bandCutoff l r d (TauCeti.BorelCalculus.reCoord v) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (B * Epr - ((l : ℝ) : ℂ) • Epr) x⟫_ℂ at hpos
  have happly : (B * Epr - ((l : ℝ) : ℂ) • Epr) x = B x - ((l : ℝ) : ℂ) • x := by
    simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp, hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((l : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = l * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- The centre and the half-width of the configuration `[l, r]`. -/
def gapCenter (l r : ℝ) : ℝ := (l + r) / 2

/-- The shifted operator `B - centre`. -/
def shiftedOperator (l r : ℝ) : H →L[ℂ] H :=
  B - ((gapCenter l r : ℝ) : ℂ) • (1 : H →L[ℂ] H)

omit [CompleteSpace H] in
/-- Evaluating the shifted operator subtracts the gap centre. -/
theorem shiftedOperator_apply (l r : ℝ) (x : H) :
    shiftedOperator B l r x = B x - ((gapCenter l r : ℝ) : ℂ) • x := by
  simp [shiftedOperator]

omit [CompleteSpace H] hB in
/-- Shifting by a real scalar preserves symmetry of the quadratic form. -/
theorem inner_shiftedOperator_symm (hB' : B.IsSymmetric) (l r : ℝ) (u v : H) :
    ⟪u, shiftedOperator B l r v⟫_ℂ = ⟪shiftedOperator B l r u, v⟫_ℂ := by
  have h : ⟪B u, v⟫_ℂ = ⟪u, B v⟫_ℂ := hB' u v
  rw [shiftedOperator_apply, shiftedOperator_apply, inner_sub_right, inner_sub_left,
    inner_smul_right, inner_smul_left, Complex.conj_ofReal, h]

/-- **The complement of the band spectral subspace is bounded away from the
band.**  For `x` orthogonal to the band subspace,
`‖(B - centre) x‖ ≥ ((r - l)/2 + d) ‖x‖`: the symbol
`((t - c)² - K²)(1 - χ)` is nonnegative on the spectrum, because `1 - χ`
vanishes on `[l, r]` while `|t - c| ≥ K` on the exterior. -/
theorem norm_shiftedOperator_ge_of_mem_centralBandSubspace_orthogonal
    {l r d : ℝ} (hd : 0 < d) (hlr : l ≤ r)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ (centralBandSubspace B hB (l := l) (r := r) (d := d))ᗮ) :
    ((r - l) / 2 + d) * ‖x‖ ≤ ‖shiftedOperator B l r x‖ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set c : ℝ := gapCenter l r with hc
  set K : ℝ := (r - l) / 2 + d with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = 0 := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => ((TauCeti.BorelCalculus.reCoord w - c) ^ 2 - K ^ 2) *
        (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)),
      ((((Complex.continuous_re.comp continuous_subtype_val).sub
          continuous_const).pow 2).sub continuous_const).mul
        (continuous_const.sub
          ((continuous_bandCutoff l r d).comp
            (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ ((TauCeti.BorelCalculus.reCoord w - c) ^ 2 - K ^ 2) *
      (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord w))
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, sub_self, mul_zero]
    · rw [bandCutoff_eq_zero hd hout, sub_zero, mul_one]
      set t : ℝ := TauCeti.BorelCalculus.reCoord w with ht
      rcases hout with hlow | hhigh
      · have h1 : c - t ≥ K := by rw [hc, hK, gapCenter]; linarith
        nlinarith [hKpos]
      · have h1 : t - c ≥ K := by rw [hc, hK, gapCenter]; linarith
        nlinarith [hKpos]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((((ContinuousMap.id ℂ).restrict (spectrum ℂ B) - ((c : ℝ) : ℂ) • 1) *
            ((ContinuousMap.id ℂ).restrict (spectrum ℂ B) - ((c : ℝ) : ℂ) • 1)) -
              ((K ^ 2 : ℝ) : ℂ) • 1) *
          (1 - TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        ((TauCeti.BorelCalculus.reCoord v - c) ^ 2 - K ^ 2) *
          (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord v)) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.one_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, smul_eq_mul, bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_mul, map_sub, map_sub, map_mul, map_sub, map_smul, map_smul,
    map_one, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x,
    (((B - ((c : ℝ) : ℂ) • 1) * (B - ((c : ℝ) : ℂ) • 1) -
      ((K ^ 2 : ℝ) : ℂ) • 1) * (1 - Epr)) x⟫_ℂ at hpos
  set S : H →L[ℂ] H := shiftedOperator B l r with hSdef
  have hSeq : B - ((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) = S := by
    rw [hSdef, shiftedOperator, hc]
  have happly : (((B - ((c : ℝ) : ℂ) • 1) * (B - ((c : ℝ) : ℂ) • 1) -
      ((K ^ 2 : ℝ) : ℂ) • 1) * (1 - Epr)) x = S (S x) - ((K ^ 2 : ℝ) : ℂ) • x := by
    simp only [mul_apply_eq_comp, _root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self, hEx, sub_zero, hSeq]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hquad : RCLike.re ⟪x, S (S x)⟫_ℂ = ‖S x‖ ^ 2 := by
    rw [hSdef, inner_shiftedOperator_symm B hB l r x (shiftedOperator B l r x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hxx : RCLike.re (((K ^ 2 : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = K ^ 2 * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  rw [hquad, hxx] at hpos
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [norm_nonneg (S x), norm_nonneg x, hKpos]

/-! ### The same bounds for an arbitrary reducing subspace

The spectral hypotheses of a source theorem are `SpectrumIn` statements about
reducing subspaces, not statements about band spectral subspaces.  These
lemmas convert them into the same shifted-operator bounds. -/

omit [CompleteSpace H] hB in
/-- The real part of the shifted quadratic form. -/
theorem re_inner_shiftedOperator (l r : ℝ) (y : H) :
    RCLike.re ⟪shiftedOperator B l r y, y⟫_ℂ =
      RCLike.re ⟪B y, y⟫_ℂ - gapCenter l r * ‖y‖ ^ 2 := by
  have hc : RCLike.re ((((gapCenter l r) : ℝ) : ℂ) * ⟪y, y⟫_ℂ) =
      gapCenter l r * ‖y‖ ^ 2 := by
    have hre : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  rw [shiftedOperator_apply, inner_sub_left, inner_smul_left,
    Complex.conj_ofReal, map_sub, hc]

include hB in
/-- **A reducing subspace with spectrum outside the two gaps is bounded below
after the shift.**  The compression is invertible at the centre with resolvent
norm at most `((r-l)/2 + d)⁻¹`, by the sharp self-adjoint distance-to-spectrum
bound. -/
theorem norm_shiftedOperator_ge_of_spectrumIn_gapExterior
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] {l r d : ℝ}
    (hd : 0 < d) (hlr : l ≤ r)
    (hspec : SpectrumIn B U (gapExterior l r d))
    {x : H} (hx : x ∈ U) :
    ((r - l) / 2 + d) * ‖x‖ ≤ ‖shiftedOperator B l r x‖ := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  set c : ℝ := gapCenter l r with hc
  set K : ℝ := (r - l) / 2 + d with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set S1 : U →L[ℂ] U := compressOperator U B with hS1def
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hS1 : S1.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_compressOperator hBsa U)
  have hspecS1 : realSpectrum S1 ⊆ gapExterior l r d := by
    rw [hS1def, realSpectrum_compressOperator_eq_restrictedSpectrum B U hspec.invariant]
    exact hspec.subset
  have hsep : ∀ lam ∈ realSpectrum S1, K ≤ ‖((c : ℝ) : ℂ) - (lam : ℂ)‖ := by
    intro lam hlam
    have hmem := hspecS1 hlam
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rcases hmem with hlow | hhigh
    · rw [abs_of_nonneg (by rw [hc, gapCenter]; linarith)]
      rw [hc, hK, gapCenter]; linarith
    · rw [abs_of_nonpos (by rw [hc, gapCenter]; linarith)]
      rw [hc, hK, gapCenter]; linarith
  obtain ⟨hres, hbound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance S1 hS1
      ((c : ℝ) : ℂ) K hKpos hsep
  have hcancel := resolventOperator_mul_cancel S1 hres
  set u : U := ⟨x, hx⟩ with hu
  have hcoe : ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u : H) =
      shiftedOperator B l r x := by
    have hrestr : S1 = B.restrict hspec.invariant := by
      rw [hS1def]; exact compressOperator_eq_restrict_of_invariant B U hspec.invariant
    rw [hrestr]
    show B x - ((c : ℝ) : ℂ) • x = _
    rw [shiftedOperator_apply, hc]
  have happly : (resolventOperator S1 ((c : ℝ) : ℂ))
      ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u) = u := by
    have h := congrArg (fun T : U →L[ℂ] U => T u) hcancel
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hnorm : ‖u‖ ≤ K⁻¹ * ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ := by
    calc ‖u‖ = ‖(resolventOperator S1 ((c : ℝ) : ℂ))
          ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u)‖ := by rw [happly]
      _ ≤ ‖resolventOperator S1 ((c : ℝ) : ℂ)‖ *
            ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K⁻¹ * ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ := by
          have := norm_nonneg ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u)
          nlinarith [hbound]
  have hux : ‖u‖ = ‖x‖ := rfl
  have hSu : ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ =
      ‖shiftedOperator B l r x‖ := by
    rw [← hcoe]; rfl
  rw [hux, hSu] at hnorm
  rw [inv_mul_eq_div, le_div_iff₀ hKpos] at hnorm
  linarith

omit [CompleteSpace H] hB in
/-- The shifted operator depends on the interval only through its centre. -/
theorem shiftedOperator_congr {l r l' r' : ℝ} (h : gapCenter l' r' = gapCenter l r) :
    shiftedOperator B l' r' = shiftedOperator B l r := by
  rw [shiftedOperator, shiftedOperator, h]

/-! ### Identifying the band subspace

`Π` is a continuous functional calculus of `B`, so it commutes with every
orthogonal projection onto a reducing subspace. -/

include hB in
/-- The band spectral projection commutes with the projection onto any
reducing subspace. -/
theorem commute_starProjection_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : B.Reduces U) :
    Commute (centralBandSubspace B hB (l := l) (r := r) (d := d)).starProjection
      U.starProjection := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hBU : Commute B U.starProjection :=
    (ContinuousLinearMap.starProjection_comp_comm_of_reduces B U hU).symm
  have hstar : Commute (star B) U.starProjection := by rwa [hBsa.star_eq]
  have h := Commute.cfcHom (a := B) hBsa.isStarNormal hBU hstar
    (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d))
  rwa [← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap,
    ← starProjection_centralBandSubspace B hB] at h

end

/-! ## Identifying the band from source spectral hypotheses
`DavisKahan/SpectralTheory/CentralBand.lean` owns the band itself: the
configuration `realSpectrum B ⊆ Icc l r ∪ gapExterior l r d`, the band spectral
subspace `centralBandSubspace`, its form bounds, and the shifted-operator
estimates.  What stays here are the statements that need the Section 8
spectral-order bridges of `SpectralTheory/SpectralGapFormBounds.lean` and the `SpectrumIn`
constructors of `Sources/DavisKahan1970/Section8`: the remaining
reducing-subspace bound, and the two-sided identification of the band.
-/

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable (B : H →L[ℂ] H) (hB : B.IsSymmetric)

/-! ### The upper bound for an arbitrary reducing subspace

The spectral hypotheses of the source theorem are `SpectrumIn` statements about
`Q`, `Qᗮ` and `P`, not statements about band spectral subspaces.  This lemma and
`norm_shiftedOperator_ge_of_spectrumIn_gapExterior` convert them into the same
shifted-operator bounds. -/

include hB in
/-- **A reducing subspace with spectrum in `[l, r]` is a contraction after the
shift.**  The two-sided form bound of the restricted spectrum becomes a norm
bound by the Rayleigh description of the norm of a symmetric operator; the
ambient carrier is `(B - c) P_U`, so no restriction appears. -/
theorem norm_shiftedOperator_le_of_spectrumIn_Icc
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] {l r : ℝ} (hlr : l ≤ r)
    (hU : B.Reduces U) (hspec : SpectrumIn B U (Set.Icc l r))
    {x : H} (hx : x ∈ U) :
    ‖shiftedOperator B l r x‖ ≤ ((r - l) / 2) * ‖x‖ := by
  set S : H →L[ℂ] H := shiftedOperator B l r with hSdef
  set Pu : H →L[ℂ] H := U.starProjection with hPu
  have hrl : (0 : ℝ) ≤ (r - l) / 2 := by linarith
  have hcomm : Pu ∘L B = B ∘L Pu :=
    ContinuousLinearMap.starProjection_comp_comm_of_reduces B U hU
  have hScomm : ∀ y : H, Pu (S y) = S (Pu y) := by
    intro y
    have h := congrArg (fun T : H →L[ℂ] H => T y) hcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hSdef, shiftedOperator_apply, shiftedOperator_apply, map_sub, h,
      ContinuousLinearMap.map_smul]
  have hUform : ∀ y ∈ U, |RCLike.re ⟪S y, y⟫_ℂ| ≤ ((r - l) / 2) * ‖y‖ ^ 2 := by
    intro y hy
    have hup : RCLike.re ⟪y, B y⟫_ℂ ≤ r * ‖y‖ ^ 2 :=
      re_inner_le_of_spectrumIn_Iic hB (hspec.mono Set.Icc_subset_Iic_self) hy
    have hlo : l * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, B y⟫_ℂ :=
      le_re_inner_of_spectrumIn_Ici hB (hspec.mono Set.Icc_subset_Ici_self) hy
    have hswap : RCLike.re ⟪B y, y⟫_ℂ = RCLike.re ⟪y, B y⟫_ℂ :=
      (inner_re_symm y (B y)).symm
    rw [hSdef, re_inner_shiftedOperator B l r y, hswap, abs_le, gapCenter]
    constructor <;> linarith
  have hmemS : ∀ y : H, S (Pu y) ∈ U := by
    intro y
    rw [← hScomm]
    exact U.starProjection_apply_mem _
  have hsym : (S ∘L Pu).IsSymmetric := by
    intro u v
    show ⟪S (Pu u), v⟫_ℂ = ⟪u, S (Pu v)⟫_ℂ
    have h1 : ⟪S (Pu u), v⟫_ℂ = ⟪Pu u, S v⟫_ℂ :=
      (inner_shiftedOperator_symm B hB l r (Pu u) v).symm
    have h2 : ⟪Pu u, S v⟫_ℂ = ⟪u, Pu (S v)⟫_ℂ := by
      rw [hPu]
      exact Submodule.inner_starProjection_left_eq_right U u (S v)
    rw [h1, h2, hScomm v]
  have hbound : ‖S ∘L Pu‖ ≤ (r - l) / 2 := by
    refine opNorm_le_of_abs_re_inner_le hsym hrl fun y => ?_
    have hzero : ⟪S (Pu y), Uᗮ.starProjection y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal U (Uᗮ.starProjection y)).mp
        (Uᗮ.starProjection_apply_mem y) (S (Pu y)) (hmemS y)
    have hsplit : Pu y + Uᗮ.starProjection y = y := by
      rw [hPu, Submodule.starProjection_orthogonal_apply]; abel
    have hval : ⟪(S ∘L Pu) y, y⟫_ℂ = ⟪S (Pu y), Pu y⟫_ℂ := by
      show ⟪S (Pu y), y⟫_ℂ = _
      calc ⟪S (Pu y), y⟫_ℂ
          = ⟪S (Pu y), Pu y + Uᗮ.starProjection y⟫_ℂ := by rw [hsplit]
        _ = ⟪S (Pu y), Pu y⟫_ℂ + ⟪S (Pu y), Uᗮ.starProjection y⟫_ℂ :=
            inner_add_right _ _ _
        _ = ⟪S (Pu y), Pu y⟫_ℂ := by rw [hzero, add_zero]
    rw [hval]
    calc |RCLike.re ⟪S (Pu y), Pu y⟫_ℂ| ≤ ((r - l) / 2) * ‖Pu y‖ ^ 2 :=
        hUform _ (U.starProjection_apply_mem y)
      _ ≤ ((r - l) / 2) * ‖y‖ ^ 2 := by
          have h1 : ‖Pu y‖ ≤ ‖y‖ := by
            rw [hPu]; exact U.norm_starProjection_apply_le y
          have hsq : ‖Pu y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
            nlinarith [norm_nonneg (Pu y), norm_nonneg y]
          exact mul_le_mul_of_nonneg_left hsq hrl
  have hPx : Pu x = x := by
    rw [hPu]; exact Submodule.starProjection_eq_self_iff.mpr hx
  calc ‖S x‖ = ‖(S ∘L Pu) x‖ := by
        rw [ContinuousLinearMap.comp_apply, hPx]
    _ ≤ ‖S ∘L Pu‖ * ‖x‖ := (S ∘L Pu).le_opNorm x
    _ ≤ ((r - l) / 2) * ‖x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg x)

/-! ### Identifying the band subspace

`Π` is a continuous functional calculus of `B`, so it commutes with every
orthogonal projection onto a reducing subspace
(`commute_starProjection_centralBandSubspace`).  Together with the two
shifted-operator bounds that pins `Π` down. -/

include hB in
/-- The band spectral subspace carries spectrum inside `[l, r]`. -/
theorem spectrumIn_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d) :
    SpectrumIn B (centralBandSubspace B hB (l := l) (r := r) (d := d))
      (Set.Icc l r) := by
  have hinv : ∀ x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d),
      B x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d) :=
    (centralBandSubspace_reduces B hB).1
  have hup := spectrumIn_Iic_of_re_inner_le
    (T := B) hinv (c := r)
    (fun x hx => re_inner_le_of_mem_centralBandSubspace B hB hd hgap hx)
  have hlo := spectrumIn_Ici_of_le_re_inner
    (T := B) hinv (c := l)
    (fun x hx => le_re_inner_of_mem_centralBandSubspace B hB hd hgap hx)
  exact ⟨hinv, fun t ht => ⟨hlo.subset ht, hup.subset ht⟩⟩

include hB in
/-- **One half of the identification.**  A reducing subspace whose complement
is spectrally outside the two gaps contains the band spectral subspace. -/
theorem centralBandSubspace_le_of_spectrumIn_gapExterior
    {l r d : ℝ} (hd : 0 < d) (hlr : l ≤ r)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : B.Reduces U)
    (hperp : SpectrumIn B Uᗮ (gapExterior l r d)) :
    centralBandSubspace B hB (l := l) (r := r) (d := d) ≤ U := by
  set R := centralBandSubspace B hB (l := l) (r := r) (d := d) with hR
  have hcomm := commute_starProjection_centralBandSubspace B hB hd hgap hU
  intro x hx
  set y : H := Uᗮ.starProjection x with hy
  have hyU : y ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hRx : R.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hyR : y ∈ R := by
    have hperpcomm : R.starProjection ∘L Uᗮ.starProjection =
        Uᗮ.starProjection ∘L R.starProjection := by
      have hsplit : Uᗮ.starProjection =
          (1 : H →L[ℂ] H) - U.starProjection := by
        ext z
        rw [Submodule.starProjection_orthogonal_apply]
        simp
      rw [hsplit]
      show R.starProjection * ((1 : H →L[ℂ] H) - U.starProjection) =
        ((1 : H →L[ℂ] H) - U.starProjection) * R.starProjection
      rw [mul_sub, sub_mul, mul_one, one_mul, hcomm.eq]
    have h := congrArg (fun T : H →L[ℂ] H => T x) hperpcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hy, ← Submodule.starProjection_eq_self_iff, h, hRx]
  have hupper : ‖shiftedOperator B l r y‖ ≤ ((r - l) / 2) * ‖y‖ :=
    norm_shiftedOperator_le_of_spectrumIn_Icc B hB hlr
      (centralBandSubspace_reduces B hB) (spectrumIn_centralBandSubspace B hB hd hgap)
      hyR
  have hlower : ((r - l) / 2 + d) * ‖y‖ ≤ ‖shiftedOperator B l r y‖ :=
    norm_shiftedOperator_ge_of_spectrumIn_gapExterior B hB hd hlr hperp hyU
  have hy0 : y = 0 := by
    by_contra hne
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hne
    nlinarith
  have hfix : U.starProjection x = x := by
    have hsum := U.starProjection_add_starProjection_orthogonal x
    rw [hy] at hy0
    rw [hy0, add_zero] at hsum
    exact hsum
  rw [← hfix]
  exact U.starProjection_apply_mem x

include hB in
/-- **The other half.**  A reducing subspace whose spectrum sits in a shorter
interval with the same centre is contained in the band spectral subspace. -/
theorem le_centralBandSubspace_of_spectrumIn_Icc
    {l r d l' r' : ℝ} (hd : 0 < d) (hlr : l ≤ r) (hlr' : l' ≤ r')
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : B.Reduces U)
    (hspec : SpectrumIn B U (Set.Icc l' r'))
    (hcen : gapCenter l' r' = gapCenter l r)
    (hsmall : (r' - l') / 2 < (r - l) / 2 + d) :
    U ≤ centralBandSubspace B hB (l := l) (r := r) (d := d) := by
  set R := centralBandSubspace B hB (l := l) (r := r) (d := d) with hR
  have hcomm := commute_starProjection_centralBandSubspace B hB hd hgap hU
  intro x hx
  set y : H := Rᗮ.starProjection x with hy
  have hyR : y ∈ Rᗮ := Rᗮ.starProjection_apply_mem x
  have hUx : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hyU : y ∈ U := by
    have hperpcomm : U.starProjection ∘L Rᗮ.starProjection =
        Rᗮ.starProjection ∘L U.starProjection := by
      have hsplit : Rᗮ.starProjection = (1 : H →L[ℂ] H) - R.starProjection := by
        ext z
        rw [Submodule.starProjection_orthogonal_apply]
        simp
      rw [hsplit]
      show U.starProjection * ((1 : H →L[ℂ] H) - R.starProjection) =
        ((1 : H →L[ℂ] H) - R.starProjection) * U.starProjection
      rw [mul_sub, sub_mul, mul_one, one_mul, hcomm.eq]
    have h := congrArg (fun T : H →L[ℂ] H => T x) hperpcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hy, ← Submodule.starProjection_eq_self_iff, h, hUx]
  have hupper : ‖shiftedOperator B l r y‖ ≤ ((r' - l') / 2) * ‖y‖ := by
    have h := norm_shiftedOperator_le_of_spectrumIn_Icc B hB hlr' hU hspec hyU
    rwa [shiftedOperator_congr B hcen] at h
  have hlower : ((r - l) / 2 + d) * ‖y‖ ≤ ‖shiftedOperator B l r y‖ :=
    norm_shiftedOperator_ge_of_mem_centralBandSubspace_orthogonal B hB hd hlr hgap hyR
  have hy0 : y = 0 := by
    by_contra hne
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hne
    nlinarith
  have hfix : R.starProjection x = x := by
    have hsum := R.starProjection_add_starProjection_orthogonal x
    rw [hy] at hy0
    rw [hy0, add_zero] at hsum
    exact hsum
  rw [← hfix]
  exact R.starProjection_apply_mem x

end

end Band

end DavisKahan
end TauCeti
