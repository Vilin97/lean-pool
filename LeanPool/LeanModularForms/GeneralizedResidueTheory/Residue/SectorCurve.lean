/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sector Curve PV Computation (Lemma 3.1)

Model sector-curve and PV integral computations for Laurent series terms.
This implements the key computation from Hungerbuhler-Wasem (arXiv:1808.00997v2)
Lemma 3.1: the principal value of `dz/z` along a sector curve equals `i * alpha`,
where `alpha` is the opening angle of the sector.

## Main Definitions

* `sectorCurve` -- the model sector-curve parameterized on [0,3]

## Main Results

* `pv_sector_dz_over_z` -- PV of `dz/z` along sector curve equals `I * alpha`

See `SectorCurveLemma.lean` for higher-order results (`pv_sector_higher_power`,
`cauchyPV_sectorCurve_simplePole`, etc.).

## Mathematical Overview

The sector curve `sigma_{r,alpha}` is a closed curve from the origin, along the
positive real axis to radius `r`, then around an arc of angle `alpha`, then back
to the origin along the ray at angle `alpha`. Specifically:

* Segment 1 (`t in [0,1]`): radial ray `t |-> t * r` (outgoing along real axis)
* Segment 2 (`t in [1,2]`): arc `t |-> r * exp(i * (t-1) * alpha)` at radius `r`
* Segment 3 (`t in [2,3]`): radial ray `t |-> (3-t) * r * exp(i * alpha)` (returning)

The PV of `dz/z` along this curve decomposes as:
* Segments 1 and 3 contribute symmetric logarithmic divergences that cancel
* Segment 2 contributes `int_0^alpha i d theta = i * alpha`

Reference: Hungerbuhler-Wasem, arXiv:1808.00997v2, Lemma 3.1.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Definition of the sector curve -/

/-- The model sector curve parameterized on [0,3].
- [0,1]: radial ray from 0 to r along the positive real axis
- [1,2]: circular arc of radius r from angle 0 to angle alpha
- [2,3]: radial ray from r*exp(i*alpha) back to 0 -/
def sectorCurve (r : ℝ) (α : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then
    ↑(t * r)
  else if t ≤ 2 then
    ↑r * exp (I * ↑((t - 1) * α))
  else
    ↑((3 - t) * r) * exp (I * ↑α)

/-! ### Basic properties of the sector curve -/

/-- The sector curve at t=0 is 0. -/
theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by
  simp [sectorCurve]

/-- The sector curve at t=3 is 0. -/
theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
  simp only [sectorCurve, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, ↓reduceIte, sub_self, zero_mul,
    Complex.ofReal_zero, zero_mul]

/-- The sector curve is a closed curve (starts and ends at 0). -/
theorem sectorCurve_closed (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = sectorCurve r α 3 := by
  rw [sectorCurve_zero, sectorCurve_three]

/-- The sector curve at t=1 is r (the transition from radial to arc). -/
theorem sectorCurve_one (r : ℝ) (α : ℝ) :
    sectorCurve r α 1 = ↑r := by
  simp [sectorCurve]

/-- The sector curve at t=2 is r * exp(i * alpha) (end of arc). -/
theorem sectorCurve_two (r : ℝ) (α : ℝ) :
    sectorCurve r α 2 = ↑r * exp (I * ↑α) := by
  simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  congr 1; congr 1; push_cast; ring

/-- Segment 1: for t in [0,1], the sector curve is `t * r`. -/
theorem sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    sectorCurve r α t = ↑(t * r) := by
  simp [sectorCurve, ht.2]

/-- Segment 2: for t in [1,2], the sector curve is `r * exp(i*(t-1)*alpha)`. -/
theorem sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) :
    sectorCurve r α t = ↑r * exp (I * ↑((t - 1) * α)) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h1
  · simp [sectorCurve, Complex.exp_zero]
  · simp only [sectorCurve, if_neg (not_le.mpr h1), if_pos ht.2]

/-- Segment 3: for t in [2,3], the sector curve is `(3-t)*r * exp(i*alpha)`. -/
theorem sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    sectorCurve r α t = ↑((3 - t) * r) * exp (I * ↑α) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h2
  · -- t = 2: second branch applies (2 ≤ 2), result matches by computation
    simp only [sectorCurve, show ¬(2 : ℝ) ≤ 1 from by norm_num,
      show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
    push_cast; ring_nf
  · simp only [sectorCurve, if_neg (not_le.mpr (lt_trans one_lt_two h2)),
      if_neg (not_le.mpr h2)]

/-- The sector curve is continuous on [0,3]. -/
theorem sectorCurve_continuousOn (r : ℝ) (α : ℝ) :
    ContinuousOn (sectorCurve r α) (Icc 0 3) := by
  have h_union : Icc (0 : ℝ) 3 = Icc 0 1 ∪ Icc 1 2 ∪ Icc 2 3 := by
    ext x; simp only [mem_Icc, mem_union]; constructor
    · intro ⟨h0, h3⟩
      by_cases h1 : x ≤ 1
      · left; left; exact ⟨h0, h1⟩
      · push Not at h1
        by_cases h2 : x ≤ 2
        · left; right; exact ⟨le_of_lt h1, h2⟩
        · push Not at h2; right; exact ⟨le_of_lt h2, h3⟩
    · rintro ((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩)
      · exact ⟨h0, le_trans h1 (by norm_num)⟩
      · exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩
      · exact ⟨le_trans (by norm_num) h2, h3⟩
  rw [h_union]
  have hc1 : ContinuousOn (sectorCurve r α) (Icc 0 1) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg1 r α t ht)
    exact (continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousOn
  have hc2 : ContinuousOn (sectorCurve r α) (Icc 1 2) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg2 r α t ht)
    apply ContinuousOn.mul continuousOn_const
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_ofReal.comp
        ((continuous_id.sub continuous_const).mul continuous_const)))).continuousOn
  have hc3 : ContinuousOn (sectorCurve r α) (Icc 2 3) := by
    apply ContinuousOn.congr _ (fun t ht => sectorCurve_seg3 r α t ht)
    apply ContinuousOn.mul _ continuousOn_const
    exact (continuous_ofReal.comp
      ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn
  exact ((hc1.union_of_isClosed hc2 isClosed_Icc isClosed_Icc).union_of_isClosed hc3
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc)

/-- The sector curve passes through the origin at t=0 and t=3. -/
theorem sectorCurve_passes_through_origin (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 ∧ sectorCurve r α 3 = 0 :=
  ⟨sectorCurve_zero r α, sectorCurve_three r α⟩

/-- On the arc segment (t in [1,2]), the sector curve has modulus r. -/
theorem sectorCurve_norm_on_arc (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ)
    (ht : t ∈ Icc 1 2) :
    ‖sectorCurve r α t‖ = r := by
  rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (le_of_lt hr)

/-! ### Derivative of the sector curve -/

/-- Derivative on segment 1 (t in (0,1)): `deriv (sectorCurve r alpha) t = r`. -/
theorem deriv_sectorCurve_seg1 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    deriv (sectorCurve r α) t = ↑r := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑(s * r) := by
    have h_nhds : Iio 1 ∈ 𝓝 t := Iio_mem_nhds ht.2
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve, if_pos (le_of_lt (mem_Iio.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have : HasDerivAt (fun s => (↑(s * r) : ℂ)) (↑r) t := by
    have h1 : HasDerivAt (fun s => s * r) r t := by
      have := (hasDerivAt_id t).mul_const r
      simpa using this
    exact h1.ofReal_comp
  exact this.deriv

/-- Derivative on segment 2 (t in (1,2)):
  `deriv (sectorCurve r alpha) t = r * (I * alpha) * exp(I * (t-1) * alpha)`. -/
theorem deriv_sectorCurve_seg2 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    deriv (sectorCurve r α) t =
      ↑r * (I * ↑α) * exp (I * ↑((t - 1) * α)) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑r * exp (I * ↑((s - 1) * α)) := by
    have h_nhds : Ioo 1 2 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    filter_upwards [h_nhds] with s hs
    rw [sectorCurve_seg2 r α s ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((s - 1) * α) : ℂ)) (↑α) t := by
    have h1 : HasDerivAt (fun s => (s - 1) * α) α t := by
      have := ((hasDerivAt_id t).sub_const 1).mul_const α
      simpa using this
    exact h1.ofReal_comp
  have h_exp : HasDerivAt (fun s => exp (I * ↑((s - 1) * α)))
      (I * ↑α * exp (I * ↑((t - 1) * α))) t := by
    have := (hasDerivAt_exp (I * ↑((t - 1) * α))).comp t
      ((hasDerivAt_const t I).mul h_inner)
    convert this using 1
    ring
  have h_full : HasDerivAt (fun s => ↑r * exp (I * ↑((s - 1) * α)))
      (↑r * (I * ↑α * exp (I * ↑((t - 1) * α)))) t := by
    have := (hasDerivAt_const t (↑r : ℂ)).mul h_exp
    convert this using 1; ring
  rw [h_full.deriv]; ring

/-- Derivative on segment 3 (t in (2,3)):
  `deriv (sectorCurve r alpha) t = -r * exp(I * alpha)`. -/
theorem deriv_sectorCurve_seg3 (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    deriv (sectorCurve r α) t = -(↑r) * exp (I * ↑α) := by
  have h_eq : sectorCurve r α =ᶠ[𝓝 t] fun s => ↑((3 - s) * r) * exp (I * ↑α) := by
    have h_nhds : Ioi 2 ∈ 𝓝 t := Ioi_mem_nhds ht.1
    filter_upwards [h_nhds] with s hs
    simp only [sectorCurve,
      if_neg (not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) (mem_Ioi.mp hs))),
      if_neg (not_le.mpr (mem_Ioi.mp hs))]
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun s => (↑((3 - s) * r) : ℂ)) (↑(-r)) t := by
    have h1 : HasDerivAt (fun s => (3 - s) * r) (-r) t := by
      have := ((hasDerivAt_const t 3).sub (hasDerivAt_id t)).mul_const r
      convert this using 1; ring
    exact h1.ofReal_comp
  have h_full : HasDerivAt (fun s => ↑((3 - s) * r) * exp (I * ↑α))
      (↑(-r) * exp (I * ↑α)) t :=
    h_inner.mul_const _
  rw [h_full.deriv]; push_cast; ring

/-! ### PV integrand analysis -/

/-- The integrand `(sectorCurve r alpha t)^(-1) * deriv (sectorCurve r alpha) t`
on segment 1 (t in (0,1)) simplifies to `1/t` (as a complex number). -/
theorem pv_integrand_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = ↑(t⁻¹) := by
  rw [sectorCurve_seg1 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg1 r α t ht]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast; field_simp

/-- The integrand on segment 2 (t in (1,2)) simplifies to `I * alpha`. -/
theorem pv_integrand_seg2 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α := by
  rw [sectorCurve_seg2 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg2 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The integrand on segment 3 (t in (2,3)) simplifies to `-1/(3-t)`. -/
theorem pv_integrand_seg3 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 2 3) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = -↑((3 - t)⁻¹) := by
  rw [sectorCurve_seg3 r α t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
      deriv_sectorCurve_seg3 r α t ht]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h_exp_ne : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
  have h3t_ne : (3 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h3t_ne' : (↑(3 - t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h3t_ne
  push_cast; field_simp

/-! ### PV computation: Lemma 3.1 -/

/-- The integral of `1/t` from `epsilon` to `1` is `-log(epsilon)`. -/
theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by
  rw [integral_inv_of_pos hε one_pos,
    Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one, zero_sub]

/-- The integral of `-1/(3-t)` from `2` to `3-epsilon` is `log(epsilon)`. -/
theorem integral_seg3_eq_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (2 : ℝ)..(3 - ε), -((3 - t)⁻¹) = Real.log ε := by
  rw [intervalIntegral.integral_neg]
  have h1 : ∫ t in (2 : ℝ)..(3 - ε), (3 - t)⁻¹ = ∫ u in ε..1, u⁻¹ := by
    have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
      (a := (2 : ℝ)) (b := 3 - ε)
    rw [this]
    congr 1 <;> ring
  rw [h1, integral_inv_of_pos hε one_pos,
    Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one, zero_sub, neg_neg]

/-- On segment 1, the norm of the sector curve is `t * r`. -/
theorem sectorCurve_norm_seg1 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖sectorCurve r α t‖ = t * r := by
  rw [sectorCurve_seg1 r α t ht]
  exact Complex.norm_of_nonneg (mul_nonneg ht.1 (le_of_lt hr))

/-- On segment 3, the norm of the sector curve is `(3 - t) * r`. -/
theorem sectorCurve_norm_seg3' (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 2 3) :
    ‖sectorCurve r α t‖ = (3 - t) * r := by
  rw [sectorCurve_seg3 r α t ht, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) (le_of_lt hr))]

/-- The logarithmic integrals from segments 1 and 3 cancel. -/
theorem log_cancellation (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    (∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ)) +
    (∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ)) = 0 := by
  have hεr_pos : 0 < ε / r := div_pos hε hr
  have hεr_lt1 : ε / r < 1 := by rwa [div_lt_one hr]
  have h1 : ∫ t in (ε / r)..(1 : ℝ), (t⁻¹ : ℝ) = -(Real.log (ε / r)) := by
    rw [integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero (ne_of_gt hεr_pos),
      Real.log_one, zero_sub]
  have h2 : ∫ t in (2 : ℝ)..(3 - ε / r), -((3 - t)⁻¹ : ℝ) = Real.log (ε / r) := by
    rw [intervalIntegral.integral_neg]
    have h_sub : ∫ t in (2 : ℝ)..(3 - ε / r), (3 - t)⁻¹ = ∫ u in (ε / r)..1, u⁻¹ := by
      have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
        (a := (2 : ℝ)) (b := 3 - ε / r)
      rw [this]; congr 1 <;> ring
    rw [h_sub, integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero
      (ne_of_gt hεr_pos), Real.log_one, zero_sub, neg_neg]
  have h1c : ∫ t in (ε / r)..(1 : ℝ), (↑(t⁻¹) : ℂ) = ↑(-(Real.log (ε / r))) := by
    rw [← h1, intervalIntegral.integral_ofReal]
  have h2c : ∫ t in (2 : ℝ)..(3 - ε / r), (-(↑((3 - t)⁻¹)) : ℂ) =
      ↑(Real.log (ε / r)) := by
    have : ∀ t : ℝ, (-(↑((3 - t)⁻¹) : ℂ)) = (↑((-((3 - t)⁻¹)) : ℝ)) := by
      intro t; push_cast; ring
    simp_rw [this, intervalIntegral.integral_ofReal, h2]
  rw [h1c, h2c, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero]

private theorem pv_cutoff_F_integrable_0_delta (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 0 (ε / r) := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  apply (intervalIntegrable_const (c := (0 : ℂ))).congr
  intro t ht; rw [Set.uIoc_of_le hδ.le] at ht
  dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
  rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
  exact le_trans (mul_le_mul_of_nonneg_right ht.2 hr.le)
    (le_of_eq (by rw [hδ_def]; field_simp))

private theorem pv_cutoff_F_integrable_3delta_3 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume (3 - ε / r) 3 := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  apply (intervalIntegrable_const (c := (0 : ℂ))).congr
  intro t ht; rw [Set.uIoc_of_le (by linarith : 3 - δ ≤ 3)] at ht
  dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
  have h2 : 2 ≤ t := by linarith [ht.1]
  rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
  have : (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le
  linarith [show δ * r = ε from by rw [hδ_def]; field_simp]

private theorem pv_cutoff_F_integrable_delta_1 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume (ε / r) 1 := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have hcont : ContinuousOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Set.uIcc δ 1) := by
    intro t ht; rw [Set.uIcc_of_le hδ1.le] at ht
    have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_inv₀ (ne_of_gt ht_pos))).continuousWithinAt
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ1.le]
  have h_eq : ∀ t ∈ Ioo δ (1 : ℝ), F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith
  have h_g_Ioo : IntegrableOn (fun t : ℝ => (↑(t⁻¹) : ℂ)) (Ioo δ 1) volume :=
    (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
      (by rw [Set.uIoc_of_le hδ1.le]; exact Ioo_subset_Ioc_self)
  have h_F_Ioo : IntegrableOn F (Ioo δ 1) volume :=
    Integrable.congr h_g_Ioo
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo

private theorem pv_cutoff_F_integrable_1_2 (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (_hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 1 2 := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have h_eq : ∀ t ∈ Ioo (1 : ℝ) 2, F t = I * ↑α := by
    intro t ⟨ht1, ht2⟩
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩,
          deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      have : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      rw [Complex.norm_of_nonneg (le_of_lt hr)]; linarith
  have h_const_Ioo : IntegrableOn (fun (_ : ℝ) => I * (↑α : ℂ)) (Ioo (1 : ℝ) 2) volume :=
    (intervalIntegrable_iff.mp (intervalIntegrable_const :
      IntervalIntegrable (fun _ => I * (↑α : ℂ)) volume 1 2)).mono_set
      (by rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; exact Ioo_subset_Ioc_self)
  have h_F_Ioo : IntegrableOn F (Ioo (1 : ℝ) 2) volume :=
    Integrable.congr h_const_Ioo
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo

private theorem pv_cutoff_F_integrable_2_3delta (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    IntervalIntegrable F volume 2 (3 - ε / r) := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  rw [intervalIntegrable_iff, Set.uIoc_of_le h3δ.le]
  have h_eq : ∀ t ∈ Ioo (2 : ℝ) (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
    intro t ⟨ht2, ht3δ⟩
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · have h3 : t < 3 := by linarith
      rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, le_of_lt h3⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
      have : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast; field_simp
    · have h3 : t < 3 := by linarith
      rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, le_of_lt h3⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < (3 - t) * r := by nlinarith
  have hcont : ContinuousOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ)) (Set.uIcc 2 (3 - δ)) := by
    rw [Set.uIcc_of_le h3δ.le]
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact continuous_neg.continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_inv₀ (ne_of_gt (show (0 : ℝ) < 3 - t by linarith [ht.2]))).comp
         (continuousAt_const.sub continuousAt_id)))
  have h_g_Ioo : IntegrableOn (fun t : ℝ => -(↑((3 - t)⁻¹) : ℂ))
      (Ioo (2 : ℝ) (3 - δ)) volume :=
    (intervalIntegrable_iff.mp hcont.intervalIntegrable).mono_set
      (by rw [Set.uIoc_of_le h3δ.le]; exact Ioo_subset_Ioc_self)
  have h_F_Ioo : IntegrableOn F (Ioo (2 : ℝ) (3 - δ)) volume :=
    Integrable.congr h_g_Ioo
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (h_eq t ht).symm)
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo

private theorem pv_sector_cutoff_base_integrabilities (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    let _ : 0 < δ := div_pos hε hr
    let _ : δ < 1 := by rwa [div_lt_one hr]
    let _ : 2 < 3 - δ := by linarith
    IntervalIntegrable F volume 0 δ ∧ IntervalIntegrable F volume (3 - δ) 3 ∧
    IntervalIntegrable F volume δ 1 ∧ IntervalIntegrable F volume 1 2 ∧
    IntervalIntegrable F volume 2 (3 - δ) :=
  ⟨pv_cutoff_F_integrable_0_delta r hr α ε hε hεr,
   pv_cutoff_F_integrable_3delta_3 r hr α ε hε hεr,
   pv_cutoff_F_integrable_delta_1 r hr α ε hε hεr,
   pv_cutoff_F_integrable_1_2 r hr α ε hε hεr,
   pv_cutoff_F_integrable_2_3delta r hr α ε hε hεr⟩

private lemma intervalIntegrable_union_adjacent {f : ℝ → ℂ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntervalIntegrable f volume a b)
    (h2 : IntervalIntegrable f volume b c) :
    IntervalIntegrable f volume a c := by
  rw [intervalIntegrable_iff]
  have h1' := h1.def'; rw [Set.uIoc_of_le hab] at h1'
  have h2' := h2.def'; rw [Set.uIoc_of_le hbc] at h2'
  rw [Set.uIoc_of_le (le_trans hab hbc)]
  exact (h1'.union h2').mono_set fun t ht =>
    (le_or_gt t b).elim (fun h => .inl ⟨ht.1, h⟩) (fun h => .inr ⟨h, ht.2⟩)

private theorem pv_sector_cutoff_composed_integrabilities (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    let _ : 0 < δ := div_pos hε hr
    let _ : δ < 1 := by rwa [div_lt_one hr]
    let _ : 2 < 3 - δ := by linarith
    IntervalIntegrable F volume 0 1 ∧ IntervalIntegrable F volume 0 2 ∧
    IntervalIntegrable F volume 0 (3 - δ) := by
  set δ := ε / r
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  obtain ⟨hFint_0δ, _, hFint_δ1, hFint_12, hFint_2_3δ⟩ :=
    pv_sector_cutoff_base_integrabilities r hr α ε hε hεr
  have hFint_01 := intervalIntegrable_union_adjacent hδ.le hδ1.le hFint_0δ hFint_δ1
  have hFint_02 := intervalIntegrable_union_adjacent (by norm_num) (by norm_num)
    hFint_01 hFint_12
  exact ⟨hFint_01, hFint_02,
    intervalIntegrable_union_adjacent (by norm_num) (by linarith) hFint_02 hFint_2_3δ⟩

private theorem pv_cutoff_integral_seg1_eq_inv (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    ∫ t in δ..(1 : ℝ), F t = ∫ t in δ..(1 : ℝ), (↑(t⁻¹) : ℂ) := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · rw [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩,
          deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ htδ, ht1⟩]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans hδ htδ))
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      push_cast; field_simp
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
  rw [Set.uIoc_of_le (le_of_lt hδ1)]
  exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)

private theorem pv_cutoff_integral_seg2_eq_Ialpha (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (_hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    ∫ t in (1 : ℝ)..2, F t = I * ↑α := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  have h_on_Ioo : ∀ t ∈ Ioo 1 2, F t = I * ↑α := by
    intro t ⟨ht1, ht2⟩
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩,
          deriv_sectorCurve_seg2 r α t ⟨ht1, ht2⟩]
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      have : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    · rw [sectorCurve_seg2 r α t ⟨le_of_lt ht1, le_of_lt ht2⟩]
      simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      rw [Complex.norm_of_nonneg (le_of_lt hr)]; linarith
  have h_ae : ∀ᵐ t, t ∈ Ι 1 2 → F t = I * ↑α := by
    filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)
  change ∫ (t : ℝ) in (1 : ℝ)..2, F t = I * ↑α
  rw [intervalIntegral.integral_congr_ae h_ae, intervalIntegral.integral_const]; norm_num

private theorem pv_cutoff_integral_seg3_eq_neg_inv (r : ℝ) (hr : 0 < r) (α : ℝ) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < r) :
    let F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
    let δ := ε / r
    ∫ t in (2 : ℝ)..(3 - δ), F t =
      ∫ t in (2 : ℝ)..(3 - δ), -(↑((3 - t)⁻¹) : ℂ) := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  have h3δ : 2 < 3 - δ := by linarith
  have h_on_Ioo : ∀ t ∈ Ioo 2 (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
    intro t ⟨ht2, ht3δ⟩
    dsimp only [F]; simp only [sub_zero]; rw [if_pos]
    · have h3 : t < 3 := by linarith
      rw [sectorCurve_seg3 r α t ⟨le_of_lt ht2, le_of_lt h3⟩,
          deriv_sectorCurve_seg3 r α t ⟨ht2, h3⟩]
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      have : exp (I * ↑α) ≠ 0 := Complex.exp_ne_zero _
      have : (3 - t : ℝ) ≠ 0 := by linarith
      push_cast; field_simp
    · have h3 : t < 3 := by linarith
      rw [sectorCurve_norm_seg3' r hr α t ⟨le_of_lt ht2, le_of_lt h3⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < (3 - t) * r := by nlinarith
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Filter.eventuallyEq_set.mp Ioo_ae_eq_Ioc)] with t ht
  rw [Set.uIoc_of_le (le_of_lt h3δ)]
  exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)

/-- For `0 < ε < r`, the PV cutoff integral of `dz/z` along the sector curve equals `I * α`.
This is the key cancellation lemma: the logarithmic divergences from segments 1 and 3 cancel. -/
theorem pv_sector_cutoff_eq (r : ℝ) (hr : 0 < r) (α : ℝ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    ∫ t in (0 : ℝ)..3,
      (if ‖sectorCurve r α t - 0‖ > ε
        then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
        else 0) = I * ↑α := by
  set F : ℝ → ℂ := fun t => if ‖sectorCurve r α t - 0‖ > ε
      then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0
  set δ := ε / r with hδ_def
  have hδ : 0 < δ := div_pos hε hr
  have hδ1 : δ < 1 := by rwa [div_lt_one hr]
  obtain ⟨hFint_0δ, hFint_3δ3, hFint_δ1, hFint_12, hFint_2_3δ⟩ :=
    pv_sector_cutoff_base_integrabilities r hr α ε hε hεr
  obtain ⟨hFint_01, hFint_02, hFint_0_3δ⟩ :=
    pv_sector_cutoff_composed_integrabilities r hr α ε hε hεr
  have hI1 : ∫ t in (0 : ℝ)..δ, F t = 0 := by
    rw [show ∫ t in (0 : ℝ)..δ, F t = ∫ t in (0 : ℝ)..δ, (0 : ℂ) from by
      apply intervalIntegral.integral_congr; intro t ht
      rw [Set.uIcc_of_le (le_of_lt hδ)] at ht
      dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
      rw [sectorCurve_norm_seg1 r hr α t ⟨ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
      calc t * r ≤ δ * r := by nlinarith [ht.2]
        _ = ε := by rw [hδ_def]; field_simp]
    exact intervalIntegral.integral_zero
  have hI5 : ∫ t in (3 - δ)..(3 : ℝ), F t = 0 := by
    rw [show ∫ t in (3 - δ)..(3 : ℝ), F t = ∫ t in (3 - δ)..(3 : ℝ), (0 : ℂ) from by
      apply intervalIntegral.integral_congr; intro t ht
      rw [Set.uIcc_of_le (by linarith : 3 - δ ≤ 3)] at ht
      dsimp only [F]; simp only [sub_zero]; rw [if_neg (not_lt.mpr _)]
      rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
      calc (3 - t) * r ≤ δ * r := by nlinarith [ht.1]
        _ = ε := by rw [hδ_def]; field_simp]
    exact intervalIntegral.integral_zero
  have hI2 := pv_cutoff_integral_seg1_eq_inv r hr α ε hε hεr
  have hI3 := pv_cutoff_integral_seg2_eq_Ialpha r hr α ε hε hεr
  have hI4 := pv_cutoff_integral_seg3_eq_neg_inv r hr α ε hε hεr
  have h_split : ∫ t in (0 : ℝ)..3, F t =
      (∫ t in (0 : ℝ)..δ, F t) + (∫ t in δ..(1 : ℝ), F t) + (∫ t in (1 : ℝ)..2, F t) +
      (∫ t in (2 : ℝ)..(3 - δ), F t) + (∫ t in (3 - δ)..(3 : ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hFint_0_3δ hFint_3δ3,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_02 hFint_2_3δ,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_01 hFint_12,
        ← intervalIntegral.integral_add_adjacent_intervals hFint_0δ hFint_δ1]
  rw [h_split, hI1, hI2, hI3, hI4, hI5, zero_add, add_zero]
  have := log_cancellation r hr ε hε hεr; linear_combination this

/-- **Lemma 3.1 (dz/z part)**: The principal value of `dz/z` along the sector curve
from 0 to 3 equals `I * alpha`.

The divergences from the radial segments cancel, leaving only the arc contribution. -/
theorem pv_sector_dz_over_z (r : ℝ) (hr : 0 < r) (α : ℝ)
    (_hα_nonneg : 0 ≤ α) (_hα_le : α ≤ 2 * Real.pi) :
    CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α := by
  have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..3,
        (if ‖sectorCurve r α t - 0‖ > ε
          then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
          else 0) = I * ↑α := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr] with ε hε hε_pos
    simp only [mem_Ioi] at hε_pos
    exact pv_sector_cutoff_eq r hr α ε hε_pos (mem_Iio.mp hε)
  have h_tendsto : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..3,
        if ‖sectorCurve r α t - 0‖ > ε
          then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t
          else 0)
      (𝓝[>] 0) (𝓝 (I * ↑α)) :=
    tendsto_const_nhds.congr' (h_ev.mono (fun ε h => h.symm))
  constructor
  · -- The PV exists
    exact ⟨I * ↑α, h_tendsto⟩
  · -- The PV value is I * α
    have : cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 = I * ↑α := by
      unfold cauchyPrincipalValue'
      exact h_tendsto.limUnder_eq
    exact this

end
