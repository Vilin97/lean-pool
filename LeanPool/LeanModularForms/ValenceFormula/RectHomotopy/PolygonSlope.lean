/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.PolygonProps

/-!
# Polygon slope analysis and derivative bounds

Proves slope identities for `fdPolygon` on each segment, tendsto at breakpoints,
non-differentiability at partition points `{1,2,3,4}`, and global derivative bounds.

* `slope_fdPolygon_segN` — slope equals segment derivative on each interval
* `fdPolygon_not_differentiableAt_partition` — left/right slopes differ
* `fdPolygon_deriv_bounded` — `∃ M, ∀ t ∈ Icc 0 5, ‖deriv fdPolygon t‖ ≤ M`
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma slope_fdPolygon_seg1 (s t : ℝ) (hs : s < 1) (ht : t < 1) (hst : s ≠ t) :
    slope fdPolygon s t =
      -(HHeight - Real.sqrt 3 / 2) * I := by
  have hs' : s ≤ 1 := le_of_lt hs
  have ht' : t ≤ 1 := le_of_lt ht
  have heq_s : fdPolygon s = 1/2 + (HHeight - ↑s * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, hs', ↓reduceIte]
  have heq_t : fdPolygon t = 1/2 + (HHeight - ↑t * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, ht', ↓reduceIte]
  simp only [slope_def_module, heq_s, heq_t]
  erw [Complex.real_smul]
  have hne : (↑t : ℂ) - ↑s ≠ 0 := by
    simpa only [sub_ne_zero, ne_eq, Complex.ofReal_inj] using hst.symm
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; ring

lemma slope_fdPolygon_seg2 (s t : ℝ) (hs : s > 1) (ht : t > 1) (hs2 : s ≤ 2) (ht2 : t ≤ 2)
    (hst : s ≠ t) :
    slope fdPolygon s t = iPoint - rho' := by
  have hs' : ¬(s ≤ 1) := not_le.mpr hs
  have ht' : ¬(t ≤ 1) := not_le.mpr ht
  have heq_s : fdPolygon s =
      chordSegment rho' iPoint (s - 1) := by simp only [fdPolygon, hs', ↓reduceIte, hs2]
  have heq_t : fdPolygon t =
      chordSegment rho' iPoint (t - 1) := by simp only [fdPolygon, ht', ↓reduceIte, ht2]
  simp only [slope_def_module, heq_s, heq_t, chordSegment, Complex.real_smul]
  have hne : (↑t : ℂ) - ↑s ≠ 0 := by
    simpa only [sub_ne_zero, ne_eq, Complex.ofReal_inj] using hst.symm
  simp only [Complex.ofReal_sub, Complex.ofReal_one, rho', iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_seg3 (s t : ℝ) (hs : s > 2) (ht : t > 2) (hs3 : s ≤ 3) (ht3 : t ≤ 3)
    (hst : s ≠ t) :
    slope fdPolygon s t = rho - iPoint := by
  have hs1 : ¬(s ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hs)
  have ht1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) ht)
  have hs2 : ¬(s ≤ 2) := not_le.mpr hs
  have ht2 : ¬(t ≤ 2) := not_le.mpr ht
  have heq_s : fdPolygon s =
      chordSegment iPoint rho (s - 2) := by simp only [fdPolygon, hs1, ↓reduceIte, hs2, hs3]
  have heq_t : fdPolygon t =
      chordSegment iPoint rho (t - 2) := by simp only [fdPolygon, ht1, ↓reduceIte, ht2, ht3]
  simp only [slope_def_module, heq_s, heq_t, chordSegment, Complex.real_smul]
  have hne : (↑t : ℂ) - ↑s ≠ 0 := by
    simpa only [sub_ne_zero, ne_eq, Complex.ofReal_inj] using hst.symm
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat, rho, iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_seg4 (s t : ℝ) (hs : s > 3) (ht : t > 3) (hs4 : s ≤ 4) (ht4 : t ≤ 4)
    (hst : s ≠ t) :
    slope fdPolygon s t = (HHeight - Real.sqrt 3 / 2) * I := by
  have hs1 : ¬(s ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hs)
  have ht1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) ht)
  have hs2 : ¬(s ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hs)
  have ht2 : ¬(t ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) ht)
  have hs3 : ¬(s ≤ 3) := not_le.mpr hs
  have ht3 : ¬(t ≤ 3) := not_le.mpr ht
  have heq_s : fdPolygon s = -1/2 + (Real.sqrt 3 / 2 +
      (s - 3) * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, hs1, ↓reduceIte, hs2, hs3, hs4]
  have heq_t : fdPolygon t = -1/2 + (Real.sqrt 3 / 2 +
      (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, ht1, ↓reduceIte, ht2, ht3, ht4]
  simp only [slope_def_module, heq_s, heq_t]
  erw [Complex.real_smul]
  have hne : (↑t : ℂ) - ↑s ≠ 0 := by
    simpa only [sub_ne_zero, ne_eq, Complex.ofReal_inj] using hst.symm
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; ring

lemma slope_fdPolygon_seg5 (s t : ℝ) (hs : s > 4) (ht : t > 4) (hst : s ≠ t) :
    slope fdPolygon s t = 1 := by
  have hs1 : ¬(s ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hs)
  have ht1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) ht)
  have hs2 : ¬(s ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hs)
  have ht2 : ¬(t ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) ht)
  have hs3 : ¬(s ≤ 3) := not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hs)
  have ht3 : ¬(t ≤ 3) := not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) ht)
  have hs4 : ¬(s ≤ 4) := not_le.mpr hs
  have ht4 : ¬(t ≤ 4) := not_le.mpr ht
  have heq_s : fdPolygon s = (s - 9/2) + HHeight * I := by
    simp only [fdPolygon, hs1, ↓reduceIte, hs2, hs3, hs4]
  have heq_t : fdPolygon t = (t - 9/2) + HHeight * I := by
    simp only [fdPolygon, ht1, ↓reduceIte, ht2, ht3, ht4]
  simp only [slope_def_module, heq_s, heq_t]
  erw [Complex.real_smul]
  have hne : (↑t : ℂ) - ↑s ≠ 0 := by
    simpa only [sub_ne_zero, ne_eq, Complex.ofReal_inj] using hst.symm
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; ring

private lemma HHeight_sub_sqrt3_half : (↑HHeight - ↑(Real.sqrt 3) / 2 : ℂ) = 1 := by
  simp only [HHeight]; push_cast; ring

lemma fdPolygon_deriv_ne_at_t1 : (-I : ℂ) ≠ (iPoint - rho') := by
  simp only [rho', iPoint]
  intro heq
  have h_lhs : (-I : ℂ).re = 0 := by simp only [Complex.neg_re, Complex.I_re, neg_zero]
  have h_rhs : (I - (1/2 + ↑(Real.sqrt 3) / 2 * I)).re = -1/2 := by
    simp only [Complex.sub_re, Complex.I_re, Complex.add_re,
      Complex.one_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.I_im, mul_one]
    norm_num
  rw [heq] at h_lhs; rw [h_rhs] at h_lhs; linarith

lemma fdPolygon_deriv_ne_at_t2 : (iPoint - rho' : ℂ) ≠ (rho - iPoint) := by
  simp only [rho', iPoint, rho]
  intro heq
  have h_sqrt3_lt : Real.sqrt 3 / 2 < 1 := by
    have h2 : Real.sqrt 3 < 2 := by
      have : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [Real.sqrt_nonneg 3]
    linarith
  have h_sqrt3_re : (↑(Real.sqrt 3) / 2 : ℂ).re = Real.sqrt 3 / 2 := by
    simp only [Complex.div_ofNat_re, Complex.ofReal_re]
  have him : (I - (1/2 + ↑(Real.sqrt 3) / 2 * I)).im =
      ((-1 : ℂ)/2 + ↑(Real.sqrt 3) / 2 * I - I).im := by rw [heq]
  simp only [Complex.sub_im, Complex.I_im, Complex.add_im, Complex.one_im,
    Complex.div_ofNat_im, Complex.mul_im, Complex.I_re, mul_zero,
    Complex.ofReal_im, mul_one, add_zero, Complex.neg_im,
    zero_div, h_sqrt3_re] at him
  linarith

lemma fdPolygon_deriv_ne_at_t3 : (rho - iPoint : ℂ) ≠ I := by
  simp only [rho, iPoint]
  intro heq
  have h_lhs : ((-(1 : ℂ))/2 + ↑(Real.sqrt 3) / 2 * I - I).re = -1/2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.one_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.I_im, mul_one, sub_zero]
    norm_num
  rw [heq] at h_lhs
  have h_rhs : (I : ℂ).re = 0 := Complex.I_re
  rw [h_rhs] at h_lhs; linarith

lemma fdPolygon_deriv_ne_at_t4 : (I : ℂ) ≠ (1 : ℂ) := by
  intro heq
  have h_lhs : (I : ℂ).im = 1 := Complex.I_im
  have h_rhs : (1 : ℂ).im = 0 := Complex.one_im
  rw [heq] at h_lhs; rw [h_rhs] at h_lhs; linarith

lemma slope_fdPolygon_at_t1_left (s : ℝ) (hs : s < 1) :
    slope fdPolygon 1 s =
      -(HHeight - Real.sqrt 3 / 2) * I := by
  have heq1 : fdPolygon 1 = 1/2 + (Real.sqrt 3 / 2) * I := by
    simp only [fdPolygon, show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
    simp only [HHeight]; push_cast; ring
  have heqs : fdPolygon s = 1/2 + (HHeight - ↑s * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, le_of_lt hs, ↓reduceIte]
  simp only [slope_def_module, heq1, heqs]
  erw [Complex.real_smul]
  have hne : (↑s : ℂ) - 1 ≠ 0 := by
    simp only [sub_ne_zero, ne_eq, Complex.ofReal_eq_one]; exact ne_of_lt hs
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; simp only [HHeight]; push_cast; ring

lemma slope_fdPolygon_at_t1_right (s : ℝ) (hs : s > 1) (hs2 : s ≤ 2) :
    slope fdPolygon 1 s = iPoint - rho' := by
  have heq1 : fdPolygon 1 = rho' := by
    simp only [fdPolygon, show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
    simp only [rho', HHeight]; push_cast; ring
  have heqs : fdPolygon s = chordSegment rho' iPoint (s - 1) := by
    simp only [fdPolygon, not_le.mpr hs, ↓reduceIte, hs2]
  simp only [slope_def_module, heq1, heqs, chordSegment, Complex.real_smul]
  have hne : (↑s : ℂ) - 1 ≠ 0 := by
    simp only [sub_ne_zero, ne_eq, Complex.ofReal_eq_one]; exact ne_of_gt hs
  simp only [Complex.ofReal_sub, Complex.ofReal_one, rho', iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_at_t2_left (s : ℝ) (hs1 : s > 1) (hs2 : s < 2) :
    slope fdPolygon 2 s = iPoint - rho' := by
  have heq2 : fdPolygon 2 = iPoint := by
    simp only [fdPolygon, show ¬((2 : ℝ) ≤ 1) from by norm_num, ↓reduceIte,
      show (2 : ℝ) ≤ 2 from le_refl 2, chordSegment]; norm_num
  have heqs : fdPolygon s = chordSegment rho' iPoint (s - 1) := by
    simp only [fdPolygon, not_le.mpr hs1, ↓reduceIte, le_of_lt hs2]
  simp only [slope_def_module, heq2, heqs, chordSegment, Complex.real_smul]
  have hne : (↑s : ℂ) - 2 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_lt hs2
  simp only [Complex.ofReal_sub, Complex.ofReal_one, rho', iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_at_t2_right (s : ℝ) (hs2 : s > 2) (hs3 : s ≤ 3) :
    slope fdPolygon 2 s = rho - iPoint := by
  have heq2 : fdPolygon 2 = iPoint := by
    simp only [fdPolygon, show ¬((2 : ℝ) ≤ 1) from by norm_num, ↓reduceIte,
      show (2 : ℝ) ≤ 2 from le_refl 2, chordSegment]
    ring_nf; simp
  have heqs : fdPolygon s = chordSegment iPoint rho (s - 2) := by
    simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hs2),
      ↓reduceIte, not_le.mpr hs2, hs3]
  simp only [slope_def_module, heq2, heqs, chordSegment, Complex.real_smul]
  have hne : (↑s : ℂ) - 2 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_gt hs2
  simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one, rho, iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_at_t3_left (s : ℝ) (hs2 : s > 2) (hs3 : s < 3) :
    slope fdPolygon 3 s = rho - iPoint := by
  have heq3 : fdPolygon 3 = rho := by
    simp only [fdPolygon, show ¬((3 : ℝ) ≤ 1) from by norm_num,
      show ¬((3 : ℝ) ≤ 2) from by norm_num, ↓reduceIte,
      show (3 : ℝ) ≤ 3 from le_refl 3, chordSegment]
    ring_nf; simp
  have heqs : fdPolygon s = chordSegment iPoint rho (s - 2) := by
    simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hs2),
      ↓reduceIte, not_le.mpr hs2, le_of_lt hs3]
  simp only [slope_def_module, heq3, heqs, chordSegment, Complex.real_smul]
  have hne : (↑s : ℂ) - 3 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_lt hs3
  simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one, rho, iPoint]
  push_cast; field_simp [hne]; ring

lemma slope_fdPolygon_at_t3_right (s : ℝ) (hs3 : s > 3) (hs4 : s ≤ 4) :
    slope fdPolygon 3 s = (HHeight - Real.sqrt 3 / 2) * I := by
  have heq3 : fdPolygon 3 = -(1 : ℂ)/2 + (Real.sqrt 3 / 2) * I := by
    simp only [fdPolygon, show ¬((3 : ℝ) ≤ 1) from by norm_num,
      show ¬((3 : ℝ) ≤ 2) from by norm_num, ↓reduceIte,
      show (3 : ℝ) ≤ 3 from le_refl 3, chordSegment]
    ring_nf; simp; simp only [rho]; ring
  have heqs : fdPolygon s = -1/2 + (Real.sqrt 3 / 2 +
      (s - 3) * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hs3),
      ↓reduceIte, not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hs3),
      not_le.mpr hs3, hs4]
  simp only [slope_def_module, heq3, heqs]
  erw [Complex.real_smul]
  have hne : (↑s : ℂ) - 3 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_gt hs3
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; simp only [HHeight]; push_cast; ring

lemma slope_fdPolygon_at_t4_left (s : ℝ) (hs3 : s > 3) (hs4 : s < 4) :
    slope fdPolygon 4 s = (HHeight - Real.sqrt 3 / 2) * I := by
  have heq4 : fdPolygon 4 = -(1 : ℂ)/2 + HHeight * I := by
    simp only [fdPolygon, show ¬((4 : ℝ) ≤ 1) from by norm_num,
      show ¬((4 : ℝ) ≤ 2) from by norm_num, show ¬((4 : ℝ) ≤ 3) from by norm_num,
      ↓reduceIte, show (4 : ℝ) ≤ 4 from le_refl 4]
    simp only [HHeight]; push_cast; ring
  have heqs : fdPolygon s = -1/2 + (Real.sqrt 3 / 2 +
      (s - 3) * (HHeight - Real.sqrt 3 / 2)) * I := by
    simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hs3),
      ↓reduceIte, not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hs3),
      not_le.mpr hs3, le_of_lt hs4]
  simp only [slope_def_module, heq4, heqs]
  erw [Complex.real_smul]
  have hne : (↑s : ℂ) - 4 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_lt hs4
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; simp only [HHeight]; push_cast; ring

lemma slope_fdPolygon_at_t4_right (s : ℝ) (hs4 : s > 4) :
    slope fdPolygon 4 s = 1 := by
  have heq4 : fdPolygon 4 = -(1 : ℂ)/2 + HHeight * I := by
    simp only [fdPolygon, show ¬((4 : ℝ) ≤ 1) from by norm_num,
      show ¬((4 : ℝ) ≤ 2) from by norm_num, show ¬((4 : ℝ) ≤ 3) from by norm_num,
      ↓reduceIte, show (4 : ℝ) ≤ 4 from le_refl 4]
    simp only [HHeight]; push_cast; ring
  have heqs : fdPolygon s = (s - 9/2) + HHeight * I := by
    simp only [fdPolygon, not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hs4),
      ↓reduceIte, not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hs4),
      not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hs4), not_le.mpr hs4]
  simp only [slope_def_module, heq4, heqs]
  erw [Complex.real_smul]
  have hne : (↑s : ℂ) - 4 ≠ 0 := by simp only [sub_ne_zero]; norm_cast; exact ne_of_gt hs4
  simp only [Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hne]; push_cast; ring

lemma slope_fdPolygon_tendsto_seg1_left :
    Tendsto (slope fdPolygon 1) (𝓝[<] 1) (𝓝 (-(HHeight - Real.sqrt 3 / 2) * I)) := by
  apply Tendsto.congr' (f₁ := fun _ => -(HHeight - Real.sqrt 3 / 2) * I)
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
    exact (slope_fdPolygon_at_t1_left s hs.2).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg2_right :
    Tendsto (slope fdPolygon 1) (𝓝[>] 1) (𝓝 (iPoint - rho')) := by
  apply Tendsto.congr' (f₁ := fun _ => iPoint - rho')
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with s hs
    exact (slope_fdPolygon_at_t1_right s hs.1 (le_of_lt hs.2)).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg2_left :
    Tendsto (slope fdPolygon 2) (𝓝[<] 2) (𝓝 (iPoint - rho')) := by
  apply Tendsto.congr' (f₁ := fun _ => iPoint - rho')
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 : ℝ) < 2)] with s hs
    exact (slope_fdPolygon_at_t2_left s hs.1 hs.2).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg3_right :
    Tendsto (slope fdPolygon 2) (𝓝[>] 2) (𝓝 (rho - iPoint)) := by
  apply Tendsto.congr' (f₁ := fun _ => rho - iPoint)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (2 : ℝ) < 3)] with s hs
    exact (slope_fdPolygon_at_t2_right s hs.1 (le_of_lt hs.2)).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg3_left :
    Tendsto (slope fdPolygon 3) (𝓝[<] 3) (𝓝 (rho - iPoint)) := by
  apply Tendsto.congr' (f₁ := fun _ => rho - iPoint)
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (2 : ℝ) < 3)] with s hs
    exact (slope_fdPolygon_at_t3_left s hs.1 hs.2).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg4_right :
    Tendsto (slope fdPolygon 3) (𝓝[>] 3) (𝓝 ((HHeight - Real.sqrt 3 / 2) * I)) := by
  apply Tendsto.congr' (f₁ := fun _ => (HHeight - Real.sqrt 3 / 2) * I)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (3 : ℝ) < 4)] with s hs
    exact (slope_fdPolygon_at_t3_right s hs.1 (le_of_lt hs.2)).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg4_left :
    Tendsto (slope fdPolygon 4) (𝓝[<] 4) (𝓝 ((HHeight - Real.sqrt 3 / 2) * I)) := by
  apply Tendsto.congr' (f₁ := fun _ => (HHeight - Real.sqrt 3 / 2) * I)
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (3 : ℝ) < 4)] with s hs
    exact (slope_fdPolygon_at_t4_left s hs.1 hs.2).symm
  · exact tendsto_const_nhds

lemma slope_fdPolygon_tendsto_seg5_right :
    Tendsto (slope fdPolygon 4) (𝓝[>] 4) (𝓝 1) := by
  apply Tendsto.congr' (f₁ := fun _ => (1 : ℂ))
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (4 : ℝ) < 5)] with s hs
    exact (slope_fdPolygon_at_t4_right s hs.1).symm
  · exact tendsto_const_nhds

/-- If `fdPolygon` is differentiable at `k` and the slope tends to `vL` from the left and
    `vR` from the right, then `vL = vR`. Used to derive a contradiction at partition points. -/
private lemma fdPolygon_slope_lr_eq {vL vR : ℂ} (k₀ : ℝ)
    (hLbot : (𝓝[<] k₀).NeBot) (hRbot : (𝓝[>] k₀).NeBot)
    (hdiff : DifferentiableAt ℝ fdPolygon k₀)
    (hLtends : Tendsto (slope fdPolygon k₀) (𝓝[<] k₀) (𝓝 vL))
    (hRtends : Tendsto (slope fdPolygon k₀) (𝓝[>] k₀) (𝓝 vR)) : vL = vR := by
  have hslope : Tendsto (slope fdPolygon k₀) (𝓝[≠] k₀) (𝓝 (deriv fdPolygon k₀)) :=
    hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt
  have hL := tendsto_nhds_unique' hLbot
    (hslope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_lt hx))) hLtends
  have hR := tendsto_nhds_unique' hRbot
    (hslope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))) hRtends
  rw [← hL, ← hR]

lemma fdPolygon_not_differentiableAt_partition (t : ℝ) (ht : t ∈ ({1, 2, 3, 4} : Finset ℝ)) :
    ¬DifferentiableAt ℝ fdPolygon t := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · intro hdiff
    have h := fdPolygon_slope_lr_eq 1 inferInstance inferInstance hdiff
      slope_fdPolygon_tendsto_seg1_left slope_fdPolygon_tendsto_seg2_right
    rw [fdPolygon_seg1_deriv_val] at h
    exact fdPolygon_deriv_ne_at_t1 h
  · exact fun hdiff => fdPolygon_deriv_ne_at_t2
      (fdPolygon_slope_lr_eq 2 inferInstance inferInstance hdiff
        slope_fdPolygon_tendsto_seg2_left slope_fdPolygon_tendsto_seg3_right)
  · intro hdiff
    have h := fdPolygon_slope_lr_eq 3 inferInstance inferInstance hdiff
      slope_fdPolygon_tendsto_seg3_left slope_fdPolygon_tendsto_seg4_right
    rw [fdPolygon_seg4_deriv_val] at h
    exact fdPolygon_deriv_ne_at_t3 h
  · intro hdiff
    have h := fdPolygon_slope_lr_eq 4 inferInstance inferInstance hdiff
      slope_fdPolygon_tendsto_seg4_left slope_fdPolygon_tendsto_seg5_right
    rw [fdPolygon_seg4_deriv_val] at h
    exact fdPolygon_deriv_ne_at_t4 h

lemma fdPolygon_deriv_bounded :
    ∃ M : ℝ, ∀ t ∈ Icc 0 5, ‖deriv fdPolygon t‖ ≤ M := by
  use 3
  intro t ht
  by_cases h : DifferentiableAt ℝ fdPolygon t
  · by_cases h_seg1 : t < 1
    · have heq : deriv fdPolygon t = deriv fdPolygonSeg1 t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_lt_nhds h_seg1] with s hs
        simp only [fdPolygon, show s ≤ 1 from le_of_lt hs, if_true, fdPolygonSeg1]
      rw [heq, fdPolygon_deriv_seg1]; simp only
      rw [Complex.norm_mul, norm_neg, Complex.norm_I, mul_one,
        HHeight_sub_sqrt3_half, norm_one]; norm_num
    · push Not at h_seg1
      by_cases h_seg2 : t < 2 ∧ t > 1
      · have heq : deriv fdPolygon t = deriv fdPolygonSeg2 t := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [eventually_gt_nhds h_seg2.2, eventually_lt_nhds h_seg2.1] with s hs1 hs2
          simp only [fdPolygon, show ¬s ≤ 1 from not_le.mpr hs1,
            show s ≤ 2 from le_of_lt hs2, if_true, if_false, fdPolygonSeg2]
        rw [heq, fdPolygon_deriv_seg2]
        calc ‖iPoint - rho'‖ ≤ ‖iPoint‖ + ‖rho'‖ := norm_sub_le _ _
          _ = 1 + 1 := by rw [i_point_norm, rho'_norm]
          _ ≤ 3 := by norm_num
      · push Not at h_seg2
        by_cases h_seg3 : t < 3 ∧ t > 2
        · have heq : deriv fdPolygon t = deriv fdPolygonSeg3 t := by
            apply Filter.EventuallyEq.deriv_eq
            filter_upwards [eventually_gt_nhds h_seg3.2,
              eventually_lt_nhds h_seg3.1] with s hs1 hs2
            simp only [fdPolygon,
              show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) hs1),
              show ¬s ≤ 2 from not_le.mpr hs1, show s ≤ 3 from le_of_lt hs2,
              if_true, if_false, fdPolygonSeg3]
          rw [heq, fdPolygon_deriv_seg3]
          calc ‖rho - iPoint‖ ≤ ‖rho‖ + ‖iPoint‖ := norm_sub_le _ _
            _ = 1 + 1 := by rw [rho_norm, i_point_norm]
            _ ≤ 3 := by norm_num
        · push Not at h_seg3
          by_cases h_seg4 : t < 4 ∧ t > 3
          · have heq : deriv fdPolygon t = deriv fdPolygonSeg4 t := by
              apply Filter.EventuallyEq.deriv_eq
              filter_upwards [eventually_gt_nhds h_seg4.2,
                eventually_lt_nhds h_seg4.1] with s hs1 hs2
              simp only [fdPolygon,
                show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hs1),
                show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hs1),
                show ¬s ≤ 3 from not_le.mpr hs1, show s ≤ 4 from le_of_lt hs2,
                if_true, if_false, fdPolygonSeg4]
            rw [heq, fdPolygon_deriv_seg4]; simp only
            rw [Complex.norm_mul, Complex.norm_I, mul_one,
              HHeight_sub_sqrt3_half, norm_one]; norm_num
          · push Not at h_seg4
            by_cases h_seg5 : t > 4 ∧ t < 5
            · have heq : deriv fdPolygon t = deriv fdPolygonSeg5 t := by
                apply Filter.EventuallyEq.deriv_eq
                filter_upwards [eventually_gt_nhds h_seg5.1,
                  eventually_lt_nhds h_seg5.2] with s hs1 hs2
                simp only [fdPolygon,
                  show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hs1),
                  show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hs1),
                  show ¬s ≤ 3 from not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hs1),
                  show ¬s ≤ 4 from not_le.mpr hs1, if_false, fdPolygonSeg5]
              rw [heq, fdPolygon_deriv_seg5]; simp only [norm_one]; norm_num
            · push Not at h_seg5
              by_cases h_zero : t = 0
              · have heq : deriv fdPolygon t = deriv fdPolygonSeg1 t := by
                  apply Filter.EventuallyEq.deriv_eq; rw [h_zero]
                  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hs
                  simp only [fdPolygon, show s ≤ 1 from le_of_lt hs, if_true, fdPolygonSeg1]
                rw [heq, fdPolygon_deriv_seg1]; simp only
                rw [Complex.norm_mul, norm_neg, Complex.norm_I, mul_one,
                  HHeight_sub_sqrt3_half, norm_one]; norm_num
              · by_cases h_five : t = 5
                · have heq : deriv fdPolygon t = deriv fdPolygonSeg5 t := by
                    apply Filter.EventuallyEq.deriv_eq; rw [h_five]
                    filter_upwards [Ioi_mem_nhds (by norm_num : (4 : ℝ) < 5)] with s hs
                    simp only [fdPolygon,
                      show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hs),
                      show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hs),
                      show ¬s ≤ 3 from not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hs),
                      show ¬s ≤ 4 from not_le.mpr hs, if_false, fdPolygonSeg5]
                  rw [heq, fdPolygon_deriv_seg5]; simp only [norm_one]; norm_num
                · exfalso
                  have ht_le4 : t ≤ 4 := by grind
                  have ht_ge1 : t ≥ 1 := h_seg1
                  have ht_in : t ∈ ({1, 2, 3, 4} : Finset ℝ) := by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    by_cases ht2 : t < 2
                    · left; exact le_antisymm (h_seg2 ht2) ht_ge1
                    · push Not at ht2
                      by_cases ht3 : t < 3
                      · right; left; exact le_antisymm (h_seg3 ht3) ht2
                      · push Not at ht3
                        by_cases ht4 : t < 4
                        · right; right; left; exact le_antisymm (h_seg4 ht4) ht3
                        · push Not at ht4; right; right; right; exact le_antisymm ht_le4 ht4
                  exact fdPolygon_not_differentiableAt_partition t ht_in h
  · simp only [deriv_zero_of_not_differentiableAt h, norm_zero]; norm_num

end RectHomotopyProof
