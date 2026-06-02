/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.PVChain.Helpers
import LeanPool.LeanModularForms.ValenceFormula.OrbitSum

/-!
# On-Curve Capture Lemmas

If `f` vanishes at a point on the boundary curve `fdBoundaryH H`, then that
point is captured by one of the singular sets `sArcOfS S` or `sVertOfS S`.

## Main Results

* `oncurve_arc_capture` — arc points (‖·‖ = 1) land in `sArcOfS S`
* `oncurve_vert_capture` — seg1 points (t ∈ (0,1)) land in `sVertOfS S`
* `height_contradiction` — seg5 / endpoint points (im = H) contradict the height bound
* `oncurve_seg4_capture` — seg4 points (t ∈ (3,4)) land in `sVertOfS S` via T-periodicity
* `oncurve_full_capture` — full assembly for all t ∈ [0,5]
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf

/-- Arc points with ‖·‖ = 1 are captured by `sArcOfS S`. -/
theorem oncurve_arc_capture
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 5)
    (h_norm : ‖fdBoundaryH H t‖ = 1) (h_zero : modularFormCompOfComplex f (fdBoundaryH H t) = 0) :
    fdBoundaryH H t ∈ (↑(sArcOfS S) : Set ℂ) := by
  set z := fdBoundaryH H t with hz_def
  have h_im_ge := fdBoundary_H_im_ge_sqrt3_div_2 H hH.le t ht
  have h_im_pos : 0 < z.im := by linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have h_normSq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h_norm] at this; linarith
  have h_im_sq_ge : z.im ^ 2 ≥ 3/4 := by
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_ge,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h_abs_re : |z.re| ≤ 1/2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z.re + 1/2), sq_nonneg (z.re - 1/2)]
  let p : ℍ := ⟨z, h_im_pos⟩
  have hp_fd : p ∈ 𝒟 := by
    refine ⟨?_, h_abs_re⟩
    change 1 ≤ Complex.normSq z
    rw [Complex.normSq_apply]; nlinarith
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero
  have hp_in_S := hS_complete p hp_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf p hp_zero)
  change z ∈ (↑(sArcOfS S) : Set ℂ)
  simp only [sArcOfS, Finset.coe_union, Finset.coe_image, Finset.coe_insert,
    Finset.coe_singleton, Set.mem_union, Set.mem_image]
  left; left
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, show ‖z‖ = 1 from h_norm⟩, rfl⟩

/-- Seg1 points with `t ∈ (0,1)` are captured by `sVertOfS S`. -/
theorem oncurve_vert_capture
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H' : ℝ} (hH' : Real.sqrt 3 / 2 < H') {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (h_zero : modularFormCompOfComplex f (fdBoundaryH H' t) = 0) :
    (fdBoundaryH H' t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ) := by
  set z := fdBoundaryH H' t with hz_def
  have hz_seg : z = fdBoundarySeg1H H' t := by
    rw [hz_def, fdBoundary_H_eq_seg1_H (le_of_lt ht.2)]
  have h_re : z.re = 1/2 := by
    rw [hz_seg]; simp [fdBoundarySeg1H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  have h_im_val : z.im = H' - t * (H' - Real.sqrt 3 / 2) := by
    rw [hz_seg]; simp [fdBoundarySeg1H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      div_ofNat]
  have h_im_gt : z.im > Real.sqrt 3 / 2 := by rw [h_im_val]; nlinarith [ht.2]
  have h_im_pos : 0 < z.im := by
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have h_re_sq : z.re ^ 2 = 1/4 := by rw [h_re]; ring
  have h_norm_gt : ‖z‖ > 1 := by
    have h_im_sq_gt : z.im ^ 2 > 3 / 4 := by
      nlinarith [mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt,
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    calc 1 = Real.sqrt 1 := by simp only [Real.sqrt_one]
      _ < Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  let p : ℍ := ⟨z, h_im_pos⟩
  have hp_fd : p ∈ 𝒟 := by
    refine ⟨?_, by change |z.re| ≤ 1/2; rw [h_re]; norm_num⟩
    change 1 ≤ Complex.normSq z
    rw [Complex.normSq_apply]
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt.le,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero
  have hp_in_S := hS_complete p hp_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf p hp_zero)
  change z ∈ (↑(sVertOfS S) : Set ℂ)
  unfold sVertOfS
  rw [Finset.coe_union, Finset.coe_union, Finset.coe_union]
  left; left; left
  rw [Finset.coe_image]
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, h_re, h_norm_gt⟩, rfl⟩

/-- A zero at height `H` with `|re| ≤ 1/2` contradicts the height bound. -/
theorem height_contradiction
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    {z : ℂ} (h_im : z.im = H) (h_re : |z.re| ≤ 1 / 2)
    (h_zero : modularFormCompOfComplex f z = 0) : False := by
  have h_im_pos : 0 < z.im := by linarith
  let p : ℍ := ⟨z, h_im_pos⟩
  have hp_fd : p ∈ 𝒟 := by
    refine ⟨?_, h_re⟩
    change 1 ≤ Complex.normSq z
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im, sq_abs z.im]
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero
  have hp_in_S := hS_complete p hp_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf p hp_zero)
  have h_p_im : (↑p : ℂ).im = z.im := rfl
  linarith [hH_bound p hp_in_S]

omit hf in
lemma seg4_eq_seg1_minus_one_H (H : ℝ) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundarySeg4H H (4 - s) = fdBoundarySeg1H H s - 1 := by
  simp only [fdBoundarySeg4H, fdBoundarySeg1H]
  have h1 : ((4 - s : ℝ) : ℂ) - 3 = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  simp only [h1]; push_cast; ring

/-- Seg4 points with `t ∈ (3,4)` are captured by `sVertOfS S` via T-periodicity. -/
theorem oncurve_seg4_capture
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Ioo (3 : ℝ) 4)
    (h_zero : modularFormCompOfComplex f (fdBoundaryH H t) = 0) :
    fdBoundaryH H t ∈ (↑(sVertOfS S) : Set ℂ) := by
  set z := fdBoundaryH H t with hz_def
  have hz_seg : z = fdBoundarySeg4H H t :=
    fdBoundary_H_eq_seg4_H (by linarith [ht.1]) (le_of_lt ht.2)
  set s := 4 - t with hs_def
  have hs_Icc : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hs_Ioo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h4s : (4 : ℝ) - s = t := by rw [hs_def]; ring
  have h_seg_eq : z = fdBoundarySeg1H H s - 1 := by
    rw [hz_seg, ← h4s]; exact seg4_eq_seg1_minus_one_H H s hs_Icc
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex f
      (by simp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictPeriods)
    simpa only [Complex.ofReal_one] using this
  have h_z_plus_1 : z + 1 = fdBoundarySeg1H H s := by rw [h_seg_eq]; ring
  have h_zero_seg1 : modularFormCompOfComplex f (fdBoundarySeg1H H s) = 0 := by
    rw [← h_z_plus_1]; exact (h_periodic z).symm ▸ h_zero
  have h_re : (fdBoundarySeg1H H s).re = 1/2 := by
    simp [fdBoundarySeg1H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  have h_im_val : (fdBoundarySeg1H H s).im = H - s * (H - Real.sqrt 3 / 2) := by
    simp [fdBoundarySeg1H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
  have h_im_gt : (fdBoundarySeg1H H s).im > Real.sqrt 3 / 2 := by
    rw [h_im_val]; nlinarith [hs_Ioo.2]
  have h_im_pos : 0 < (fdBoundarySeg1H H s).im := by
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have h_re_sq : (fdBoundarySeg1H H s).re ^ 2 = 1/4 := by rw [h_re]; ring
  have h_norm_gt : ‖fdBoundarySeg1H H s‖ > 1 := by
    have h_im_sq_gt : (fdBoundarySeg1H H s).im ^ 2 > 3/4 := by
      nlinarith [mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt,
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    calc 1 = Real.sqrt 1 := by simp only [Real.sqrt_one]
      _ < Real.sqrt ((fdBoundarySeg1H H s).re ^ 2 + (fdBoundarySeg1H H s).im ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  let p : ℍ := ⟨fdBoundarySeg1H H s, h_im_pos⟩
  have hp_fd : p ∈ 𝒟 := by
    refine ⟨?_, by change |(fdBoundarySeg1H H s).re| ≤ 1/2; rw [h_re]; norm_num⟩
    change 1 ≤ Complex.normSq (fdBoundarySeg1H H s)
    rw [Complex.normSq_apply]
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt.le,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero_seg1
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero_seg1
  have hp_in_S := hS_complete p hp_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf p hp_zero)
  change z ∈ (↑(sVertOfS S) : Set ℂ)
  rw [h_seg_eq]
  unfold sVertOfS
  rw [Finset.coe_union, Finset.coe_union, Finset.coe_union]
  left; left; right
  rw [Finset.coe_image]
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, h_re, h_norm_gt⟩, rfl⟩

/-- Full on-curve capture: any zero of `f` on `fdBoundaryH H` is in the singular set. -/
theorem oncurve_full_capture (S : Finset ℍ) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) :
    ∀ t ∈ Icc (0 : ℝ) 5,
      modularFormCompOfComplex f (fdBoundaryH H t) = 0 →
      fdBoundaryH H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ) := by
  intro t ht h_zero
  rw [Finset.coe_union]
  rcases le_or_gt t 1 with h1 | h1
  · rcases (eq_or_lt_of_le ht.1 : 0 = t ∨ 0 < t) with rfl | h0
    · exfalso
      have h_re : |((fdBoundaryH H 0)).re| ≤ 1/2 := by
        rw [fdBoundary_H_eq_seg1_H (by norm_num : (0 : ℝ) ≤ 1)]
        simp [fdBoundarySeg1H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
      have h_im : (fdBoundaryH H 0).im = H := by
        rw [fdBoundary_H_eq_seg1_H (by norm_num : (0 : ℝ) ≤ 1)]
        simp [fdBoundarySeg1H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
      exact height_contradiction f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero
    · rcases (eq_or_lt_of_le h1 : t = 1 ∨ t < 1) with rfl | h1s
      · left
        rw [fdBoundary_H_at_one_eq_rho_plus_one H]
        exact Finset.mem_coe.mpr (sArcOfS_rho_plus_one_in S)
      · right
        exact oncurve_vert_capture f hf S hS_complete hH_sqrt3 ⟨h0, h1s⟩ h_zero
  · rcases le_or_gt t 3 with h3 | h3
    · rcases (eq_or_lt_of_le h3 : t = 3 ∨ t < 3) with rfl | h3s
      · left
        rw [fdBoundary_H_at_three_eq_rho H]
        exact Finset.mem_coe.mpr (sArcOfS_rho_in S)
      · left
        have h_norm : ‖fdBoundaryH H t‖ = 1 := by
          rw [fdBoundary_H_eq_arc h1 h3s]
          exact Complex.norm_exp_ofReal_mul_I _
        exact oncurve_arc_capture f hf S hS_complete hH_sqrt3
          ⟨by linarith, by linarith [ht.2]⟩ h_norm h_zero
    · rcases le_or_gt t 4 with h4 | h4
      · rcases (eq_or_lt_of_le h4 : t = 4 ∨ t < 4) with rfl | h4s
        · exfalso
          have h_re : |(fdBoundaryH H 4).re| ≤ 1/2 := by
            rw [fdBoundary_H_eq_seg4_H (by norm_num : (3 : ℝ) < 4) (le_refl 4)]
            simp [fdBoundarySeg4H, add_re, neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
              div_ofNat]; norm_num
          have h_im : (fdBoundaryH H 4).im = H := by
            rw [fdBoundary_H_eq_seg4_H (by norm_num : (3 : ℝ) < 4) (le_refl 4)]
            simp [fdBoundarySeg4H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
              div_ofNat]; ring
          exact height_contradiction f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero
        · right
          exact oncurve_seg4_capture f hf S hS_complete hH_sqrt3 ⟨h3, h4s⟩ h_zero
      · exfalso
        have h_re : |(fdBoundaryH H t).re| ≤ 1/2 := by
          rw [fdBoundary_H_eq_seg5_H (by linarith : (4 : ℝ) < t)]
          simp only [fdBoundarySeg5H, add_re, sub_re, ofReal_re, div_ofNat_re, re_ofNat, mul_re,
            I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, one_div]
          rw [abs_le]; constructor <;> linarith [ht.2]
        have h_im : (fdBoundaryH H t).im = H := by
          rw [fdBoundary_H_eq_seg5_H (by linarith : (4 : ℝ) < t)]
          simp [fdBoundarySeg5H, add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
        exact height_contradiction f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero

end
