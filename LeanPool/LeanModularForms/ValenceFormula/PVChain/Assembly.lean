/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.PVChain.OnCurveCapture
import LeanPool.LeanModularForms.ValenceFormula.PVChain.Seg5CuspIntegral
import LeanPool.LeanModularForms.ValenceFormula.PVChain.ArcContribution
import LeanPool.LeanModularForms.ValenceFormula.PVChain.ResidueSideInfra
import LeanPool.LeanModularForms.ValenceFormula.ModularInvariance

/-!
# PV Chain Assembly

Assembles the residue side and modular side of the PV chain
using `Tendsto` statements for the ε-truncated integrals.

## Main Results

* `cpv_residue_side_tendsto` — the ε-truncated integral of `f'/f` around
    `fdBoundaryH H` tends to `2πi · Σ gWN · ord`.
* `cpv_modular_side_tendsto` — the ε-truncated integral of `f'/f` around
    `fdBoundaryH H` tends to `-(2πi · (k/12 - ord_∞(f)))`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Modular side sub-lemmas

The modular side decomposes into:
1. Vertical seg1+seg4 integrands cancel pointwise for each ε (T-invariance)
2. Arc seg2+seg3 integral tends to -(2πi·k/12) (S-transformation)
3. Horizontal seg5 integral tends to 2πi·ord_∞ (q-expansion)
4. Combine via `Tendsto.add`
-/

omit f hf in
private lemma norm_sub_one_le {z s : ℂ} (hz : z.re = 1 / 2) (hs : s.re = -1 / 2) :
    ‖(z - 1) - s‖ ≤ ‖z - s‖ := by
  have hre1 : ((z - 1) - s).re = 0 := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have him1 : ((z - 1) - s).im = z.im - s.im := by
    simp only [Complex.sub_im, Complex.one_im]; ring
  have hre2 : (z - s).re = 1 := by
    simp only [Complex.sub_re]; linarith
  have him2 : (z - s).im = z.im - s.im := by
    simp only [Complex.sub_im]
  have h1 : ‖(z - 1) - s‖ ^ 2 = (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]; ring
  have h2 : ‖z - s‖ ^ 2 = 1 + (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre2, him2]; ring
  have h_sq : ‖(z - 1) - s‖ ^ 2 ≤ ‖z - s‖ ^ 2 := by linarith
  have h_le := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_le

omit f hf in
private lemma norm_sub_le_sub_one {z s : ℂ} (hz : z.re = 1 / 2) (hs : s.re = 1 / 2) :
    ‖z - s‖ ≤ ‖(z - 1) - s‖ := by
  have hre1 : (z - s).re = 0 := by
    simp only [Complex.sub_re]; linarith
  have him1 : (z - s).im = z.im - s.im := by
    simp only [Complex.sub_im]
  have hre2 : ((z - 1) - s).re = -1 := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have him2 : ((z - 1) - s).im = z.im - s.im := by
    simp only [Complex.sub_im, Complex.one_im]; ring
  have h1 : ‖z - s‖ ^ 2 = (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre1, him1]; ring
  have h2 : ‖(z - 1) - s‖ ^ 2 = 1 + (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre2, him2]; ring
  have h_sq : ‖z - s‖ ^ 2 ≤ ‖(z - 1) - s‖ ^ 2 := by linarith
  have h_le := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_le

omit f hf in
private lemma truncation_iff_shift
    (S : Finset UpperHalfPlane) (z : ℂ) (hz_re : z.re = 1 / 2) (ε : ℝ) :
    (∃ s ∈ sVertOfS S, ‖z - s‖ ≤ ε) ↔
    (∃ s ∈ sVertOfS S, ‖(z - 1) - s‖ ≤ ε) := by
  constructor
  · rintro ⟨s, hs, h_near⟩
    rcases sVertOfS_re S s hs with hre | hre
    · exact ⟨s - 1, sVertOfS_pair_left S s hs hre,
        by rwa [show (z - 1) - (s - 1) = z - s from by ring]⟩
    · exact ⟨s, hs, le_trans (norm_sub_one_le hz_re hre) h_near⟩
  · rintro ⟨s, hs, h_near⟩
    rcases sVertOfS_re S s hs with hre | hre
    · exact ⟨s, hs, le_trans (norm_sub_le_sub_one hz_re hre) h_near⟩
    · exact ⟨s + 1, sVertOfS_pair_right S s hs hre,
        by rwa [show z - (s + 1) = (z - 1) - s from by ring]⟩

omit f hf in
private lemma norm_shift_neg_inv_eq {z s : ℂ} (hz_re : z.re = 1 / 2) (hs_unit : ‖s‖ = 1) :
    ‖(z - 1) - (-(1 : ℂ) / s)‖ = ‖z - s‖ := by
  have hs_ne : s ≠ 0 := by intro h; rw [h, norm_zero] at hs_unit; norm_num at hs_unit
  have h_normSq : s.re ^ 2 + s.im ^ 2 = 1 := by
    have h := Complex.sq_norm s; rw [hs_unit, one_pow] at h
    rw [Complex.normSq_apply] at h
    nlinarith [sq s.re, sq s.im]
  have h_mul : s.re * s.re + s.im * s.im = 1 := by nlinarith [sq s.re, sq s.im]
  have h_neg_inv_re : (-(1 : ℂ) / s).re = -s.re := by
    rw [neg_div, Complex.neg_re, Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, h_mul, div_one]; ring
  have h_neg_inv_im : (-(1 : ℂ) / s).im = s.im := by
    rw [neg_div, Complex.neg_im, Complex.div_im, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, h_mul, div_one]; ring
  have h1_re : ((z - 1) - (-(1 : ℂ) / s)).re = z.re - 1 + s.re := by
    simp only [Complex.sub_re, Complex.one_re, h_neg_inv_re]; ring
  have h1_im : ((z - 1) - (-(1 : ℂ) / s)).im = z.im - s.im := by
    simp only [Complex.sub_im, Complex.one_im, h_neg_inv_im]; ring
  have h_sq1 : ‖(z - 1) - (-(1 : ℂ) / s)‖ ^ 2 =
      (z.re - 1 + s.re) ^ 2 + (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h1_re, h1_im]; ring
  have h_sq2 : ‖z - s‖ ^ 2 = (z.re - s.re) ^ 2 + (z.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re z s, Complex.sub_im z s]; ring
  have h_eq : ‖(z - 1) - (-(1 : ℂ) / s)‖ ^ 2 = ‖z - s‖ ^ 2 := by
    rw [h_sq1, h_sq2, hz_re]; ring
  nlinarith [sq_nonneg (‖(z - 1) - (-(1 : ℂ) / s)‖ - ‖z - s‖),
    norm_nonneg ((z - 1) - (-(1 : ℂ) / s)), norm_nonneg (z - s)]

omit f hf in
private lemma neg_inv_involution {s : ℂ} (hs_unit : ‖s‖ = 1) :
    -(1 : ℂ) / (-(1 : ℂ) / s) = s := by
  have hs_ne : s ≠ 0 := by intro h; rw [h, norm_zero] at hs_unit; norm_num at hs_unit
  field_simp

omit f hf in
private lemma norm_neg_inv_of_norm_one {s : ℂ} (hs : ‖s‖ = 1) :
    ‖-(1 : ℂ) / s‖ = 1 := by
  rw [norm_div, norm_neg, norm_one, hs, div_one]

omit f hf in
private lemma truncation_iff_shift_union
    (S : Finset UpperHalfPlane) (z : ℂ) (hz_re : z.re = 1 / 2) (ε : ℝ) :
    (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖z - s‖ ≤ ε) ↔
    (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖(z - 1) - s‖ ≤ ε) := by
  constructor
  · rintro ⟨s, hs, h_le⟩
    rcases Finset.mem_union.mp hs with h_arc | h_vert
    · exact ⟨-(1 : ℂ) / s, Finset.mem_union_left _ (sArcOfS_closed S s h_arc),
        by linarith [norm_shift_neg_inv_eq hz_re (sArcOfS_unit S s h_arc)]⟩
    · obtain ⟨s', hs', h_le'⟩ := (truncation_iff_shift S z hz_re ε).mp ⟨s, h_vert, h_le⟩
      exact ⟨s', Finset.mem_union_right _ hs', h_le'⟩
  · rintro ⟨s, hs, h_le⟩
    rcases Finset.mem_union.mp hs with h_arc | h_vert
    · have h_unit := sArcOfS_unit S s h_arc
      refine ⟨-(1 : ℂ) / s, Finset.mem_union_left _ (sArcOfS_closed S s h_arc), ?_⟩
      have h_eq := norm_shift_neg_inv_eq hz_re (norm_neg_inv_of_norm_one h_unit)
      rw [neg_inv_involution h_unit] at h_eq
      linarith
    · obtain ⟨s', hs', h_le'⟩ := (truncation_iff_shift S z hz_re ε).mpr ⟨s, h_vert, h_le⟩
      exact ⟨s', Finset.mem_union_right _ hs', h_le'⟩

omit hf in
private lemma logDeriv_modFormComp_periodic :
    Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) := by
  have h_per : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex f
      (by simp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictPeriods)
    simpa only [Complex.ofReal_one] using this
  intro z
  simp only [logDeriv, Pi.div_apply]
  have h2 : deriv (modularFormCompOfComplex f) (z + 1) =
      deriv (modularFormCompOfComplex f) z := by
    rw [← deriv_comp_add_const (modularFormCompOfComplex f) 1 z]
    exact congr_arg (· z) (congr_arg deriv (funext h_per))
  rw [h2, h_per z]

omit f hf in
private lemma deriv_fdBoundary_H_on_seg1 (H : ℝ) (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fdBoundaryH H) u = -(↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
  have h_eq : fdBoundaryH H =ᶠ[𝓝 u] fdBoundarySeg1H H := by
    have : Iio (1 : ℝ) ∈ 𝓝 u := Iio_mem_nhds hu.2
    filter_upwards [this] with t ht
    exact fdBoundary_H_eq_seg1_H (le_of_lt ht)
  erw [h_eq.deriv_eq, (hasDerivAt_fdBoundary_seg1_H H u).deriv]

omit f hf in
private lemma deriv_fdBoundary_H_on_seg4 (H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (3 : ℝ) 4) :
    deriv (fdBoundaryH H) t = (↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
  have h_eq : fdBoundaryH H =ᶠ[𝓝 t] fdBoundarySeg4H H := by
    filter_upwards [Ioi_mem_nhds ht.1, Iio_mem_nhds ht.2] with s hs1 hs2
    exact fdBoundary_H_eq_seg4_H hs1 (le_of_lt hs2)
  erw [h_eq.deriv_eq, (hasDerivAt_fdBoundary_seg4_H H t).deriv]

omit f hf in
private lemma integral_seg4_cov (G : ℝ → ℂ) :
    ∫ t in (3 : ℝ)..4, G t = ∫ u in (0 : ℝ)..1, G (4 - u) := by
  have h := @intervalIntegral.integral_comp_sub_left
    ℂ _ _ (a := 0) (b := 1) G 4
  simp only [sub_zero, show (4 : ℝ) - 1 = 3 from by norm_num] at h
  exact h.symm

omit hf in
private lemma pvIntegrand_seg4_eq_neg_seg1 (_S : Finset UpperHalfPlane) (Sx : Finset ℂ)
    {H : ℝ} {ε : ℝ}
    (h_trunc_iff : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∃ s ∈ Sx, ‖fdBoundaryH H (4 - u) - s‖ ≤ ε) ↔
      (∃ s ∈ Sx, ‖fdBoundaryH H u - s‖ ≤ ε))
    (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    pvIntegrand f (fdBoundaryH H) Sx ε (4 - u) =
      -(pvIntegrand f (fdBoundaryH H) Sx ε u) := by
  have hu_le1 : u ≤ 1 := le_of_lt hu.2
  have h4u_gt3 : (3 : ℝ) < 4 - u := by linarith [hu.2]
  have h4u_lt4 : 4 - u < 4 := by linarith [hu.1]
  have h_trunc := h_trunc_iff u hu
  simp only [pvIntegrand, cauchyPrincipalValueIntegrandOn]
  by_cases h_trunc_u : ∃ s ∈ Sx, ‖fdBoundaryH H u - s‖ ≤ ε
  · rw [if_pos h_trunc_u, if_pos (h_trunc.mpr h_trunc_u)]; simp only [neg_zero]
  · rw [if_neg h_trunc_u, if_neg (mt h_trunc.mp h_trunc_u)]
    have h_shift : fdBoundaryH H (4 - u) = fdBoundaryH H u - 1 := by
      rw [fdBoundary_H_eq_seg4_H h4u_gt3 (by linarith [hu.1]),
        seg4_eq_seg1_minus_one_H H u ⟨le_of_lt hu.1, hu_le1⟩,
        fdBoundary_H_eq_seg1_H hu_le1]
    have h_logDeriv : logDeriv (modularFormCompOfComplex f) (fdBoundaryH H (4 - u)) =
        logDeriv (modularFormCompOfComplex f) (fdBoundaryH H u) := by
      rw [h_shift]
      have h_per := logDeriv_modFormComp_periodic f
      have := h_per (fdBoundaryH H u - 1)
      simp only [Function.Periodic] at h_per
      rw [show fdBoundaryH H u - 1 + 1 = fdBoundaryH H u from by ring] at this
      exact this.symm
    erw [h_logDeriv, deriv_fdBoundary_H_on_seg4 H (4 - u) ⟨h4u_gt3, h4u_lt4⟩,
        deriv_fdBoundary_H_on_seg1 H u hu]
    ring

omit hf in
private lemma integral_neg_of_pw_neg (g : ℝ → ℂ)
    (h_pw : ∀ u ∈ Set.Ioo (0 : ℝ) 1, g (4 - u) = -(g u)) :
    ∫ u in (0 : ℝ)..1, g (4 - u) = ∫ u in (0 : ℝ)..1, -(g u) := by
  apply intervalIntegral.integral_congr_ae
  rw [Filter.Eventually, MeasureTheory.mem_ae_iff]
  apply measure_mono_null (t := {(1 : ℝ)})
  · intro u hu
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hu
    obtain ⟨hu_mem, hu_ne⟩ := hu
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 from by norm_num)] at hu_mem
    rw [Set.mem_singleton_iff]
    by_contra h
    exact hu_ne (h_pw u ⟨hu_mem.1, lt_of_le_of_ne hu_mem.2 h⟩)
  · exact MeasureTheory.measure_singleton _

omit hf in
private theorem pvIntegral_vertical_cancel (S : Finset UpperHalfPlane)
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (_h_oncurve_vert : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      (fdBoundaryH H t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ)) :
    ∀ ε > 0,
      (∫ t in (0 : ℝ)..1, pvIntegrand f (fdBoundaryH H) (sVertOfS S) ε t) +
      (∫ t in (3 : ℝ)..4, pvIntegrand f (fdBoundaryH H) (sVertOfS S) ε t) = 0 := by
  intro ε hε
  rw [integral_seg4_cov]
  have h_trunc_iff : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∃ s ∈ sVertOfS S, ‖fdBoundaryH H (4 - u) - s‖ ≤ ε) ↔
      (∃ s ∈ sVertOfS S, ‖fdBoundaryH H u - s‖ ≤ ε) := by
    intro u hu
    have h_seg1 := fdBoundary_H_eq_seg1_H (H := H) (show u ≤ 1 from le_of_lt hu.2)
    have h_shift : fdBoundaryH H (4 - u) = fdBoundaryH H u - 1 := by
      rw [fdBoundary_H_eq_seg4_H (H := H) (show (3 : ℝ) < 4 - u from by linarith [hu.2])
        (show 4 - u ≤ 4 from by linarith [hu.1]),
        seg4_eq_seg1_minus_one_H H u ⟨le_of_lt hu.1, le_of_lt hu.2⟩, h_seg1]
    have h_re_u : (fdBoundaryH H u).re = 1/2 := by
      rw [h_seg1]; simp [fdBoundarySeg1H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    rw [h_shift]; exact (truncation_iff_shift S (fdBoundaryH H u) h_re_u ε).symm
  rw [integral_neg_of_pw_neg _ (fun u hu =>
      pvIntegrand_seg4_eq_neg_seg1 f S (sVertOfS S) h_trunc_iff u hu),
    intervalIntegral.integral_neg]; ring

omit hf in
private theorem pvIntegral_vertical_cancel_union (S : Finset UpperHalfPlane)
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (_h_oncurve_vert : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      (fdBoundaryH H t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ)) :
    ∀ ε > 0,
      (∫ t in (0 : ℝ)..1,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) +
      (∫ t in (3 : ℝ)..4,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) = 0 := by
  intro ε hε
  rw [integral_seg4_cov]
  have h_trunc_iff : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖fdBoundaryH H (4 - u) - s‖ ≤ ε) ↔
      (∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖fdBoundaryH H u - s‖ ≤ ε) := by
    intro u hu
    have h_seg1 := fdBoundary_H_eq_seg1_H (H := H) (show u ≤ 1 from le_of_lt hu.2)
    have h_shift : fdBoundaryH H (4 - u) = fdBoundaryH H u - 1 := by
      rw [fdBoundary_H_eq_seg4_H (H := H) (show (3 : ℝ) < 4 - u from by linarith [hu.2])
        (show 4 - u ≤ 4 from by linarith [hu.1]),
        seg4_eq_seg1_minus_one_H H u ⟨le_of_lt hu.1, le_of_lt hu.2⟩, h_seg1]
    have h_re_u : (fdBoundaryH H u).re = 1/2 := by
      rw [h_seg1]; simp [fdBoundarySeg1H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    rw [h_shift]; exact (truncation_iff_shift_union S (fdBoundaryH H u) h_re_u ε).symm
  rw [integral_neg_of_pw_neg _ (fun u hu =>
    pvIntegrand_seg4_eq_neg_seg1 f S (sArcOfS S ∪ sVertOfS S) h_trunc_iff u hu),
    intervalIntegral.integral_neg]; ring

omit hf in
private theorem tendsto_pvIntegral_arc (S : Finset UpperHalfPlane)
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (_h_oncurve_arc : ∀ t ∈ Set.Ioo (1 : ℝ) 3,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S) : Set ℂ)) :
    Tendsto (fun ε => ∫ t in (1 : ℝ)..3,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t)
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * ((k : ℂ) / 12)))) :=
  tendsto_pvIntegral_arc_bridge f S _hH _h_oncurve_arc

include hf in
/-- The non-truncated integral of `f'/f` along seg5 equals `2πi · ord_∞(f)`. -/
private theorem seg5_logDeriv_integral_value
    {H : ℝ} (_hH : Real.sqrt 3 / 2 < H)
    (_hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5QRadiusH H),
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0) :
    ∫ t in (4 : ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundaryH H t) *
        deriv (fdBoundaryH H) t =
      2 * ↑Real.pi * I * (orderAtCusp' f : ℂ) := by
  exact seg5_logDeriv_integral_value_bridge f hf _hH _hcusp_nonvan

include hf in
private theorem tendsto_pvIntegral_seg5
    (S : Finset UpperHalfPlane)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5QRadiusH H),
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0)
    (h_vert_below_H : ∀ s ∈ sVertOfS S, s.im < H)
    (h_arc_below_H : ∀ s ∈ sArcOfS S, s.im < H) :
    Tendsto (fun ε =>
      ∫ t in (4 : ℝ)..5,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t)
      (𝓝[>] 0)
      (𝓝 (2 * ↑Real.pi * I * (orderAtCusp' f : ℂ))) := by
  set L := 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)
  have h_below : ∀ s ∈ (sArcOfS S ∪ sVertOfS S : Finset ℂ), s.im < H := by
    intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact h_arc_below_H s h
    · exact h_vert_below_H s h
  have h_seg5_im : ∀ t, 4 < t → (fdBoundaryH H t).im = H := by
    intro t ht
    rw [fdBoundary_H_eq_seg5_H ht]
    simp [fdBoundarySeg5H, add_im, ofReal_im, mul_im, I_re, I_im]
  have h_no_trunc : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t, 4 < t → t ≤ 5 →
        ¬∃ s ∈ sArcOfS S ∪ sVertOfS S, ‖fdBoundaryH H t - s‖ ≤ ε := by
    rcases (sArcOfS S ∪ sVertOfS S).eq_empty_or_nonempty with h_empty | h_ne
    · filter_upwards [self_mem_nhdsWithin] with ε _
      intro t _ _; simp [h_empty]
    · set δ := (sArcOfS S ∪ sVertOfS S).inf' h_ne (fun s => H - s.im)
      have hδ_pos : 0 < δ :=
        (Finset.lt_inf'_iff h_ne).mpr (fun s hs => by linarith [h_below s hs])
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      intro t ht4 _; push Not; intro s hs
      calc ε < δ := hε.2
        _ ≤ H - s.im := Finset.inf'_le _ hs
        _ = |(fdBoundaryH H t - s).im| := by
            rw [Complex.sub_im, h_seg5_im t ht4, abs_of_pos]
            linarith [h_below s hs]
        _ ≤ ‖fdBoundaryH H t - s‖ := Complex.abs_im_le_norm _
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (4 : ℝ)..5,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) = L := by
    filter_upwards [h_no_trunc] with ε hε
    calc ∫ t in (4 : ℝ)..5,
          pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t
        = ∫ t in (4 : ℝ)..5,
          logDeriv (modularFormCompOfComplex f) (fdBoundaryH H t) *
            deriv (fdBoundaryH H) t := by
          apply intervalIntegral.integral_congr_ae'
          · exact Filter.Eventually.of_forall fun t ht => by
              rw [Set.mem_Ioc] at ht
              simp only [pvIntegrand, cauchyPrincipalValueIntegrandOn,
                if_neg (hε t ht.1 ht.2)]
          · exact Filter.Eventually.of_forall fun t ht => by
              rw [Set.mem_Ioc] at ht; exact absurd ht.1 (by linarith [ht.2])
      _ = L := seg5_logDeriv_integral_value f hf hH hcusp_nonvan
  exact tendsto_const_nhds.congr' (h_ev.mono fun ε h => h.symm)

omit f hf in
private lemma norm_deriv_fdBoundary_H_le
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (_ht : t ∈ Icc (0 : ℝ) 5)
    (ht_ne1 : t ≠ 1) (ht_ne3 : t ≠ 3) (ht_ne4 : t ≠ 4) :
    ‖deriv (fdBoundaryH H) t‖ ≤ max H 1 := by
  have h_norm_cast : ‖(↑H - ↑(Real.sqrt 3) / 2 : ℂ)‖ = H - Real.sqrt 3 / 2 := by
    have hcast : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑(H - Real.sqrt 3 / 2) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by
      linarith [Real.sqrt_pos_of_pos (by norm_num : (3 : ℝ) > 0)])]
  by_cases h1 : t < 1
  · erw [(fdBoundary_H_hasDerivAt_seg1 H h1).deriv]
    rw [neg_mul, norm_neg, norm_mul, Complex.norm_I, mul_one,
        h_norm_cast]
    exact le_trans (by linarith [Real.sqrt_nonneg 3]) (le_max_left H 1)
  · push Not at h1
    have h1' : 1 < t := lt_of_le_of_ne h1 (Ne.symm ht_ne1)
    by_cases h3 : t < 3
    · erw [(fdBoundary_H_hasDerivAt_arc H h1' h3).deriv]
      simp only [norm_mul, Complex.norm_I, mul_one]
      have hexp : ‖exp ((↑Real.pi * (↑t + 1) / 6 : ℂ) * I)‖ = 1 := by
        rw [show (↑Real.pi * (↑t + 1) / 6 : ℂ) * I =
          ↑(Real.pi * (t + 1) / 6) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hexp, one_mul]
      have hpi : ‖(↑Real.pi / 6 : ℂ)‖ = Real.pi / 6 := by
        rw [show (↑Real.pi / 6 : ℂ) = ↑(Real.pi / 6) from by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hpi]
      exact le_max_of_le_right (by linarith [Real.pi_le_four])
    · push Not at h3
      have h3' : 3 < t := lt_of_le_of_ne h3 (Ne.symm ht_ne3)
      by_cases h4 : t < 4
      · erw [(fdBoundary_H_hasDerivAt_seg4 H h3' h4).deriv]
        rw [norm_mul, Complex.norm_I, mul_one, h_norm_cast]
        exact le_trans (by linarith [Real.sqrt_nonneg 3]) (le_max_left H 1)
      · push Not at h4
        have h4' : 4 < t := lt_of_le_of_ne h4 (Ne.symm ht_ne4)
        erw [(fdBoundary_H_hasDerivAt_seg5 H h4').deriv]; rw [norm_one]
        exact le_max_right H 1

omit hf in
private lemma integrableOn_logDeriv_mul_deriv_farSet
    (S : Finset UpperHalfPlane)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_capture : ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    let γ := fdBoundaryH H
    let S₀ := (sArcOfS S ∪ sVertOfS S : Finset ℂ)
    let g := modularFormCompOfComplex f
    let K' := {t ∈ Icc (0 : ℝ) 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - (s : ℂ)‖}
    IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
  intro γ S₀ g K'
  have hK'_compact : IsCompact K' := by
    refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _ ⟨ht, _⟩ => ht)
    apply IsClosed.inter isClosed_Icc
    have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
      isClosed_iInter fun s => isClosed_iInter fun _ =>
        isClosed_le continuous_const
          (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
    convert this using 1; ext t; simp only [mem_iInter, mem_setOf_eq]; exact Iff.rfl
  have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
  have h_ne : ∀ t ∈ K', g (γ t) ≠ 0 := by
    intro t ⟨ht_Icc, h_far⟩ h_zero
    have h_in := h_capture t ht_Icc h_zero
    rw [Finset.mem_coe] at h_in
    have := h_far _ h_in; rw [sub_self, norm_zero] at this; linarith
  have h_cont : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp
    · have h_im : 0 < (γ t).im := fdBoundary_H_im_pos H hH t ht.1
      have h_analytic : AnalyticAt ℂ g (γ t) :=
        (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
          (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds h_im)
      exact (h_analytic.deriv.fun_div h_analytic (h_ne t ht)).continuousAt
    · exact (fdBoundary_H_continuous H).continuousAt
  have h_asm : AEStronglyMeasurable (fun t => logDeriv g (γ t) * deriv γ t)
      (volume.restrict K') :=
    (h_cont.aestronglyMeasurable hK'_meas).mul
      ((aestronglyMeasurable_deriv γ volume).mono_measure
        (Measure.restrict_le_self))
  by_cases hK'_ne : K'.Nonempty
  · obtain ⟨t_max, ht_max_mem, ht_max⟩ := hK'_compact.exists_isMaxOn hK'_ne
      (continuous_norm.comp_continuousOn h_cont)
    set M := ‖logDeriv g (γ t_max)‖ * max H 1
    refine IntegrableOn.of_bound
      ((measure_mono (inter_subset_left (s := Icc 0 5))).trans_lt measure_Icc_lt_top)
      h_asm M ?_
    have h_compl_ae : ({(1 : ℝ), 3, 4} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
      rw [mem_ae_iff, compl_compl]
      exact (Set.Finite.insert 1 (Set.Finite.insert 3
        (Set.finite_singleton 4))).measure_zero _
    refine (ae_restrict_iff' hK'_meas).mpr ?_
    filter_upwards [h_compl_ae] with t ht_excl
    intro ht
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at ht_excl
    obtain ⟨ht_ne1, ht_ne3, ht_ne4⟩ := ht_excl
    rw [norm_mul]
    exact mul_le_mul (ht_max ht) (norm_deriv_fdBoundary_H_le hH ht.1 ht_ne1 ht_ne3 ht_ne4)
      (norm_nonneg _) (norm_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty.mp hK'_ne]; exact integrableOn_empty

omit hf in
private lemma pvIntegrand_intervalIntegrable
    (S : Finset UpperHalfPlane)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {ε : ℝ} (hε : 0 < ε)
    (h_capture : ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5) (hb : b ∈ Icc (0 : ℝ) 5) :
    IntervalIntegrable
      (pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε)
      MeasureTheory.volume a b := by
  set γ := fdBoundaryH H with hγ_def
  set S₀ := (sArcOfS S ∪ sVertOfS S : Finset ℂ) with hS₀_def
  set g := modularFormCompOfComplex f with hg_def
  set F := pvIntegrand f γ S₀ ε with hF_def
  set K' := {t ∈ Icc (0 : ℝ) 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - (s : ℂ)‖} with hK'_def
  set K := {t ∈ uIoc a b | ¬∃ s ∈ (S₀ : Set ℂ), ‖γ t - s‖ ≤ ε} with hK_def
  have hK_subset_K' : K ⊆ K' := by
    intro t ⟨ht_uioc, h_not_near⟩
    have ht_Icc : t ∈ Icc (0 : ℝ) 5 :=
      uIcc_subset_Icc ha hb (uIoc_subset_uIcc ht_uioc)
    refine ⟨ht_Icc, fun s hs => ?_⟩
    by_contra h_contra; push Not at h_contra
    exact h_not_near ⟨s, Finset.mem_coe.mpr hs, h_contra.le⟩
  have hF_K : EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
    intro t ⟨_, h_not_near⟩
    change cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
    simp only [cauchyPrincipalValueIntegrandOn]
    simp only [Finset.mem_coe] at h_not_near
    exact if_neg h_not_near
  have h_compl_zero : EqOn F 0 (uIoc a b \ K) := by
    intro t ⟨ht_uioc, h_not_K⟩
    change cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
    simp only [cauchyPrincipalValueIntegrandOn]
    have h_near : ∃ s ∈ (S₀ : Set ℂ), ‖γ t - s‖ ≤ ε := by
      by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
    simp only [Finset.mem_coe] at h_near
    exact if_pos h_near
  have h_int_K' := integrableOn_logDeriv_mul_deriv_farSet f S hH h_capture hε
  have hK_meas : MeasurableSet K := by
    apply measurableSet_uIoc.inter
    apply MeasurableSet.compl
    suffices h : IsClosed (⋃ s ∈ (S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
      convert h.measurableSet using 1
      ext t; simp only [mem_iUnion, mem_setOf_eq, Finset.mem_coe, exists_prop]; exact Iff.rfl
    exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
      isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        continuous_const
  have h_int_K : IntegrableOn F K :=
    (h_int_K'.mono_set hK_subset_K').congr_fun hF_K.symm hK_meas
  have h_int_compl : IntegrableOn F (uIoc a b \ K) :=
    integrableOn_zero.congr_fun h_compl_zero.symm (measurableSet_uIoc.diff hK_meas)
  rw [intervalIntegrable_iff]
  have := h_int_K.union h_int_compl
  rwa [union_sdiff_cancel (fun t ht => ht.1)] at this

omit hf in
private theorem tendsto_pvIntegral_split
    (S : Finset UpperHalfPlane)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_capture : ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..5,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) =
      (∫ t in (0 : ℝ)..1,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) +
      (∫ t in (1 : ℝ)..3,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) +
      (∫ t in (3 : ℝ)..4,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) +
      (∫ t in (4 : ℝ)..5,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have mem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 5 := ⟨le_refl _, by norm_num⟩
  have mem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have mem3 : (3 : ℝ) ∈ Icc (0 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have mem4 : (4 : ℝ) ∈ Icc (0 : ℝ) 5 := ⟨by norm_num, by norm_num⟩
  have hi : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 5 → b ∈ Icc (0 : ℝ) 5 →
      IntervalIntegrable
        (pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε)
        MeasureTheory.volume a b :=
    fun ha hb => pvIntegrand_intervalIntegrable f S hH (Set.mem_Ioi.mp hε) h_capture ha hb
  rw [(intervalIntegral.integral_add_adjacent_intervals
      (hi mem0 mem4) (hi mem4 ⟨by norm_num, le_refl _⟩)).symm,
    (intervalIntegral.integral_add_adjacent_intervals
      (hi mem0 mem3) (hi mem3 mem4)).symm,
    (intervalIntegral.integral_add_adjacent_intervals
      (hi mem0 mem1) (hi mem1 mem3)).symm]

omit hf in
private lemma modFormComp_ne_zero_at_height
    {H : ℝ} (hH_pos : 0 < H)
    (hcusp : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5QRadiusH H),
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0)
    {z : ℂ} (hz_im : z.im = H) :
    modularFormCompOfComplex f z ≠ 0 := by
  have hz_pos : 0 < z.im := hz_im ▸ hH_pos
  have h_bridge : modularFormCompOfComplex f z = f ⟨z, hz_pos⟩ := by
    simp only [modularFormCompOfComplex, Function.comp_apply]
    congr 1; exact UpperHalfPlane.ofComplex_apply_of_im_pos hz_pos
  intro h_zero
  have h_qmem : Function.Periodic.qParam (1 : ℝ) (↑(⟨z, hz_pos⟩ : ℍ) : ℂ) ∈
      Metric.closedBall (0 : ℂ) (seg5QRadiusH H) := by
    rw [Metric.mem_closedBall, dist_zero_right, Function.Periodic.norm_qParam]
    simp only [div_one, seg5QRadiusH, hz_im]; exact le_refl _
  have h_qne :
      Function.Periodic.qParam (1 : ℝ) (↑(⟨z, hz_pos⟩ : ℍ) : ℂ) ≠ 0 := by
    simp only [Function.Periodic.qParam, ne_eq]
    exact Complex.exp_ne_zero _
  exact absurd ((SlashInvariantFormClass.eq_cuspFunction f ⟨z, hz_pos⟩
    (by simp) one_ne_zero).trans
    (h_bridge ▸ h_zero)) (hcusp _ h_qmem h_qne)

include hf in
private lemma modular_side_h_capture
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_gt_one : 1 < H)
    (_hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    (hcusp : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5QRadiusH H),
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) f q ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ) := by
  have hH_pos : 0 < H := by linarith [hH_sqrt3, Real.sqrt_nonneg 3]
  have h_oncurve_arc : ∀ t ∈ Set.Ioo (1 : ℝ) 3,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S) : Set ℂ) := by
    intro t ht h_zero
    have h_norm : ‖fdBoundaryH H t‖ = 1 := by
      rw [fdBoundary_H_eq_arc ht.1 ht.2]
      exact Complex.norm_exp_ofReal_mul_I _
    exact oncurve_arc_capture f hf S hS_complete hH_sqrt3
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_norm h_zero
  have h_oncurve_vert : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      (fdBoundaryH H t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ) :=
    fun t ht h_zero =>
      oncurve_vert_capture f hf S hS_complete hH_sqrt3 ht h_zero
  intro t ht h_zero
  by_cases h1 : t < 1
  · by_cases h0 : 0 < t
    · exact Finset.mem_coe.mpr
        (Finset.mem_union_right _ (h_oncurve_vert t ⟨h0, h1⟩ h_zero))
    · push Not at h0
      have h_eq : t = 0 := le_antisymm h0 ht.1
      subst h_eq; exfalso
      have h_im : (fdBoundaryH H 0).im = H := by
        rw [fdBoundary_H_eq_seg1_H (show (0 : ℝ) ≤ 1 from by norm_num)]
        simp [fdBoundarySeg1H, add_im, ofReal_im, mul_im, I_re, I_im]
      exact modFormComp_ne_zero_at_height f hH_pos hcusp h_im h_zero
  · push Not at h1
    by_cases h3 : t ≤ 3
    · by_cases h1' : t = 1
      · subst h1'
        rw [fdBoundary_H_at_one_eq_rho_plus_one]
        exact Finset.mem_coe.mpr
          (Finset.mem_union_left _ (sArcOfS_rho_plus_one_in S))
      · by_cases h3' : t = 3
        · subst h3'
          rw [fdBoundary_H_at_three_eq_rho]
          exact Finset.mem_coe.mpr
            (Finset.mem_union_left _ (sArcOfS_rho_in S))
        · exact Finset.mem_coe.mpr
            (Finset.mem_union_left _
              (h_oncurve_arc t ⟨lt_of_le_of_ne h1 (Ne.symm h1'),
                lt_of_le_of_ne h3 h3'⟩ h_zero))
    · push Not at h3
      by_cases h4 : t ≤ 4
      · by_cases h4' : t = 4
        · subst h4'; exfalso
          have h_im : (fdBoundaryH H 4).im = H := by
            rw [fdBoundary_H_at_four]
            simp [add_im, ofReal_im, mul_im, I_re, I_im]
          exact modFormComp_ne_zero_at_height f hH_pos hcusp h_im h_zero
        · have h_lt4 : t < 4 := lt_of_le_of_ne h4 h4'
          have ht_seg4 : fdBoundaryH H t = fdBoundaryH H (4 - t) - 1 := by
            rw [fdBoundary_H_eq_seg4_H h3 h4]
            have h4_u := seg4_eq_seg1_minus_one_H H (4 - t)
              ⟨by linarith, by linarith⟩
            simp only [show (4 : ℝ) - (4 - t) = t from by ring] at h4_u
            rw [h4_u, fdBoundary_H_eq_seg1_H (by linarith : 4 - t ≤ 1)]
          have h_F_per : Function.Periodic
              (modularFormCompOfComplex f) (1 : ℂ) := by
            have := SlashInvariantFormClass.periodic_comp_ofComplex f
              (by simp : (1 : ℝ) ∈
                (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictPeriods)
            simpa only [Complex.ofReal_one] using this
          have h_F_zero_shifted :
              modularFormCompOfComplex f (fdBoundaryH H (4 - t)) = 0 := by
            have := h_F_per (fdBoundaryH H (4 - t) - 1)
            simp only [sub_add_cancel] at this
            rw [ht_seg4] at h_zero; rwa [this]
          have h_re : (fdBoundaryH H (4 - t)).re = 1/2 := by
            rw [fdBoundary_H_eq_seg1_H (by linarith : 4 - t ≤ 1)]
            simp [fdBoundarySeg1H, add_re, ofReal_re, mul_re, I_re, I_im,
              ofReal_im]
          rw [ht_seg4]
          exact Finset.mem_coe.mpr (Finset.mem_union_right _
            (sVertOfS_pair_left S _
              (Finset.mem_coe.mp (h_oncurve_vert (4 - t) ⟨by linarith, by linarith⟩
                h_F_zero_shifted)) h_re))
      · exfalso
        have h_im : (fdBoundaryH H t).im = H := by
          rw [fdBoundary_H_eq_seg5_H (by linarith : (4 : ℝ) < t)]
          simp [fdBoundarySeg5H, add_im, ofReal_im, mul_im, I_re, I_im]
        exact modFormComp_ne_zero_at_height f hH_pos hcusp h_im h_zero

include hf in
/-- Modular side: ε-truncated integral of `f'/f` tends to `-(2πi·(k/12 - ord_∞))`. -/
theorem cpv_modular_side_tendsto
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete :
      ∀ p, p ∈ 𝒟 →
        orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        Tendsto (fun ε =>
          ∫ t in (0 : ℝ)..5,
            pvIntegrand f (fdBoundaryH H)
              (sArcOfS S ∪ sVertOfS S) ε t)
          (𝓝[>] 0)
          (𝓝 (-(2 * ↑Real.pi * I *
            ((k : ℂ) / 12 -
              (orderAtCusp' f : ℂ))))) := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  obtain ⟨H₁, hH₁_gt, hH₁_gt_one, hH₁_bound⟩ := exists_height_bound_S S
  set H₂ := max H₀ H₁ with hH₂_def
  refine ⟨H₂, lt_of_lt_of_le hH₀_gt (le_max_left _ _), fun {H} hH => ?_⟩
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    calc Real.sqrt 3 / 2 < H₀ := hH₀_gt
      _ ≤ H₂ := le_max_left _ _
      _ ≤ H := hH
  have hH_gt_one : 1 < H := calc
    (1 : ℝ) < H₁ := hH₁_gt_one
    _ ≤ H₂ := le_max_right _ _
    _ ≤ H := hH
  have hcusp := cusp_nonvanishing_height_mono f
    (le_trans (le_max_left _ _) hH) hH₀_nonvan
  have h_vert_below : ∀ s ∈ sVertOfS S, s.im < H := by
    intro s hs
    calc s.im < H₁ := sVertOfS_im_lt_height_bound S s hs hH₁_bound
      _ ≤ H₂ := le_max_right _ _
      _ ≤ H := hH
  have h_arc_below : ∀ s ∈ sArcOfS S, s.im < H := by
    intro s hs
    have : s.im ≤ 1 := by
      nlinarith [Complex.sq_norm s, Complex.normSq_apply s, sq_nonneg s.re,
        sArcOfS_unit S s hs]
    linarith
  have h_oncurve_arc : ∀ t ∈ Set.Ioo (1 : ℝ) 3,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S) : Set ℂ) := by
    intro t ht h_zero
    have h_norm : ‖fdBoundaryH H t‖ = 1 := by
      rw [fdBoundary_H_eq_arc ht.1 ht.2]
      exact Complex.norm_exp_ofReal_mul_I _
    exact oncurve_arc_capture f hf S hS_complete hH_sqrt3
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_norm h_zero
  have h_oncurve_vert : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      (fdBoundaryH H t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ) :=
    fun t ht h_zero =>
      oncurve_vert_capture f hf S hS_complete hH_sqrt3 ht h_zero
  have hH_bound : ∀ s ∈ S, (s : ℂ).im < H :=
    fun s hs => calc (s : ℂ).im < H₁ := hH₁_bound s hs
      _ ≤ H₂ := le_max_right _ _
      _ ≤ H := hH
  have h_split := tendsto_pvIntegral_split f S hH_sqrt3
    (modular_side_h_capture f hf S _hS hS_complete hH_sqrt3 hH_gt_one hH_bound hcusp)
  have h_arc := tendsto_pvIntegral_arc f S hH_sqrt3 h_oncurve_arc
  have h_seg5 := tendsto_pvIntegral_seg5 f hf S hH_sqrt3 hcusp
    h_vert_below h_arc_below
  have h_vert_tendsto : Tendsto (fun ε =>
      (∫ t in (0 : ℝ)..1,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t) +
      (∫ t in (3 : ℝ)..4,
        pvIntegrand f (fdBoundaryH H) (sArcOfS S ∪ sVertOfS S) ε t))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (pvIntegral_vertical_cancel_union f S hH_sqrt3 h_oncurve_vert ε
        (Set.mem_Ioi.mp hε)).symm
  have h_sum : Tendsto (fun ε =>
      (((∫ t in (0 : ℝ)..1,
          pvIntegrand f (fdBoundaryH H)
            (sArcOfS S ∪ sVertOfS S) ε t) +
        (∫ t in (1 : ℝ)..3,
          pvIntegrand f (fdBoundaryH H)
            (sArcOfS S ∪ sVertOfS S) ε t)) +
       (∫ t in (3 : ℝ)..4,
          pvIntegrand f (fdBoundaryH H)
            (sArcOfS S ∪ sVertOfS S) ε t)) +
      (∫ t in (4 : ℝ)..5,
          pvIntegrand f (fdBoundaryH H)
            (sArcOfS S ∪ sVertOfS S) ε t))
      (𝓝[>] 0)
      (𝓝 (-(2 * ↑Real.pi * I * ((k : ℂ) / 12 -
        (orderAtCusp' f : ℂ))))) := by
    rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ↑(orderAtCusp' f))) =
      0 + (-(2 * ↑Real.pi * I * (↑k / 12)) +
        2 * ↑Real.pi * I * ↑(orderAtCusp' f)) from by ring]
    exact Filter.Tendsto.congr (fun ε => by ring)
      (h_vert_tendsto.add (h_arc.add h_seg5))
  exact h_sum.congr' (h_split.mono (fun ε h => h.symm))


end
