/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Smooth
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.MainTheorem
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# Interior Winding Number

The generalized winding number of the fundamental domain boundary
around any strict interior point equals -1.

## Main Results

* `fdBoundary_H_avoids_interior` — the boundary at height H
    never passes through a strict interior point
* `gWN_fdBoundary_H_eq_neg_one_of_interior` — gWN = -1 for
    interior points with im < heightCutoff
* `gWN_fdBoundary_H_eq_neg_one_of_strictInterior` — gWN = -1
    for any strict interior point with im < H
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma fdBoundary_H_norm_eq_one_arc {H t : ℝ} (h1 : 1 < t) (h3 : t < 3) :
    ‖fdBoundaryH H t‖ = 1 := by
  by_cases h2 : t ≤ 2
  · rw [fdBoundary_H_eq_seg2_H H h1 h2]; simp only [fdBoundarySeg2H, fdBoundarySeg2]
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  · push Not at h2
    rw [fdBoundary_H_eq_seg3_H H h2 (le_of_lt h3)]; simp only [fdBoundarySeg3H, fdBoundarySeg3]
    rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
    exact norm_exp_ofReal_mul_I _

/-- The boundary at height H avoids any strict interior point p
with ‖p‖ > 1, |re p| < 1/2, im p > 0, im p < H. -/
theorem fdBoundary_H_avoids_interior (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (_hp_im_pos : 0 < p.im) {H : ℝ} (hp_im : p.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundaryH H t ≠ p := by
  intro t ht habs
  simp only [Icc, mem_setOf_eq] at ht
  by_cases h1 : t ≤ 1
  · have hre : (fdBoundaryH H t).re = 1 / 2 := by
      rw [fdBoundary_H_eq_seg1_H h1, fdBoundarySeg1H]
      simp only [add_re, mul_re, ofReal_re, ofReal_im,
        I_re, I_im, div_ofNat, one_re]
      norm_num
    rw [habs] at hre
    have := abs_lt.mp hp_re; linarith
  · push Not at h1
    by_cases h3 : t ≤ 3
    · have hnorm : ‖fdBoundaryH H t‖ = 1 := by
        rcases eq_or_lt_of_le h3 with rfl | h3'
        · rw [fdBoundary_H_at_three H]
          exact ellipticPointRho_norm
        · exact fdBoundary_H_norm_eq_one_arc h1 h3'
      rw [habs] at hnorm; linarith
    · push Not at h3
      by_cases h4 : t ≤ 4
      · have hre : (fdBoundaryH H t).re = -1 / 2 := by
          rw [fdBoundary_H_eq_seg4_H h3 h4,
            fdBoundarySeg4H]
          simp only [add_re, neg_re, mul_re, ofReal_re,
            ofReal_im, I_re, I_im, div_ofNat, one_re]
          norm_num
        rw [habs] at hre
        have := abs_lt.mp hp_re; linarith
      · push Not at h4
        have him : (fdBoundaryH H t).im = H := by
          rw [fdBoundary_H_eq_seg5_H h4,
            fdBoundarySeg5H]
          simp only [add_im, mul_im, ofReal_re, ofReal_im,
            I_re, I_im, div_ofNat]
          norm_num
        rw [habs] at him; linarith

private lemma fdBoundary_H_eq_arc' {H : ℝ} {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundaryH H t = Complex.exp (↑(Real.pi * (1 + t) / 6) * I) := by
  simp only [fdBoundaryH, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
  by_cases h2 : t ≤ 2
  · simp only [h2, ↓reduceIte]; congr 1; push_cast; ring
  · simp only [h2, ↓reduceIte, show t ≤ 3 from le_of_lt ht3]; congr 1; push_cast; ring

private lemma arc_hasDerivAt' (s : ℝ) :
    HasDerivAt (fun s' : ℝ => exp ((↑Real.pi * (↑s' + 1) / 6) * I))
      (exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I)) s := by
  apply HasDerivAt.cexp
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by simpa using (hasDerivAt_id s).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) + 1) 1 s := by
    simpa using h1.add_const (1 : ℂ)
  have h3 : HasDerivAt (fun s : ℝ =>
      ↑Real.pi * ((s : ℂ) + 1)) (↑Real.pi * 1) s := by
    have := (hasDerivAt_const s (↑Real.pi : ℂ)).mul h2
    simp only [zero_mul, zero_add] at this; exact this
  have h4 : HasDerivAt (fun s : ℝ =>
      ↑Real.pi * ((s : ℂ) + 1) / 6 * I) (↑Real.pi * 1 / 6 * I) s := (h3.div_const _).mul_const _
  convert h4 using 1; ring

private lemma fdBoundary_H_hasDerivAt_arc' (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    HasDerivAt (fdBoundaryH H)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] (fun s => Complex.exp ((↑Real.pi * (↑s + 1) / 6) * I)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3, Ioo_mem_nhds ht1 ht3,
      fun s hs => (fdBoundary_H_eq_arc' hs.1 hs.2).trans (by congr 1; congr 1; push_cast; ring)⟩
  exact (heq.hasDerivAt_iff.mpr (arc_hasDerivAt' t)).congr_deriv (by push_cast; ring)

private def heightSens : ℝ → ℂ := fun t =>
  if t ≤ 1 then ↑(1 - t) * I
  else if t ≤ 3 then 0
  else if t ≤ 4 then ↑(t - 3) * I
  else I

private lemma heightSens_continuous : Continuous heightSens := by
  unfold heightSens
  apply Continuous.if
  · intro t ht; rw [show {t : ℝ | t ≤ 1} = Set.Iic 1 from rfl, frontier_Iic] at ht
    simp only [mem_singleton_iff] at ht; subst ht
    simp only [show (1 : ℝ) ≤ 3 from by norm_num, ↓reduceIte]; push_cast; ring
  · exact (continuous_ofReal.comp (by fun_prop)).mul continuous_const
  · apply Continuous.if
    · intro t ht; rw [show {t : ℝ | t ≤ 3} = Set.Iic 3 from rfl, frontier_Iic] at ht
      simp only [mem_singleton_iff] at ht; subst ht
      simp only [show (3 : ℝ) ≤ 4 from by norm_num, ↓reduceIte]; push_cast; ring
    · exact continuous_const
    · apply Continuous.if
      · intro t ht; rw [show {t : ℝ | t ≤ 4} = Set.Iic 4 from rfl, frontier_Iic] at ht
        simp only [mem_singleton_iff] at ht; subst ht; push_cast; ring
      · exact (continuous_ofReal.comp (by fun_prop)).mul continuous_const
      · exact continuous_const

private lemma fdBoundary_H_decomp (H₀ H' : ℝ) (t : ℝ) :
    fdBoundaryH H' t = fdBoundaryH H₀ t + ↑(H' - H₀) * heightSens t := by
  unfold fdBoundaryH heightSens
  by_cases h2 : t ≤ 2
  · by_cases h1 : t ≤ 1 <;>
      simp only [h1, h2, ↓reduceIte, show t ≤ 3 from by linarith] <;> push_cast <;> ring
  · push Not at h2
    have h1 : ¬ t ≤ 1 := by linarith
    by_cases h3 : t ≤ 3 <;> by_cases h4 : t ≤ 4 <;>
      simp only [show ¬ t ≤ 2 from by linarith, h1, h3, h4, ↓reduceIte] <;> push_cast <;> ring

private lemma fdHomot_continuous (H₀ H₁ : ℝ) :
    Continuous (fun (q : ℝ × ℝ) => fdBoundaryH (H₀ + q.2 * (H₁ - H₀)) q.1) := by
  have h_eq : (fun (q : ℝ × ℝ) => fdBoundaryH (H₀ + q.2 * (H₁ - H₀)) q.1) =
    fun q => fdBoundaryH H₀ q.1 + ↑(q.2 * (H₁ - H₀)) * heightSens q.1 := by
    ext q; rw [fdBoundary_H_decomp H₀]; ring_nf
  rw [h_eq]
  exact ((fdBoundary_H_continuous H₀).comp continuous_fst).add
    ((continuous_ofReal.comp (continuous_snd.mul continuous_const)).mul
      (heightSens_continuous.comp continuous_fst))

private lemma fdHomot_deriv_continuousOn_piece (H₀ H₁ : ℝ) (p₁ p₂ : ℝ)
    (hfree : ∀ x ∈ Ioo p₁ p₂, x ∉ fdBoundaryHPartition) :
    ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun t => fdBoundaryH (H₀ + q.2 * (H₁ - H₀)) t) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  by_cases h_le1 : p₂ ≤ 1
  · apply ContinuousOn.congr (f := fun q : ℝ × ℝ =>
        -(↑(H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2) : ℂ) * I)
    · exact ((continuous_ofReal.comp (by fun_prop :
        Continuous (fun q : ℝ × ℝ => H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2))).neg.mul
        continuous_const).continuousOn
    · intro q hq
      convert (fdBoundary_H_hasDerivAt_seg1 _ (lt_of_lt_of_le hq.1.2 h_le1)).deriv using 1
      push_cast; ring
  · push Not at h_le1
    have hp1_ge1 : 1 ≤ p₁ := by
      by_contra h; push Not at h
      exact hfree 1 ⟨h, h_le1⟩ (by simp [fdBoundaryHPartition, Finset.mem_insert])
    by_cases h_le3 : p₂ ≤ 3
    · apply ContinuousOn.congr (f := fun q : ℝ × ℝ =>
          ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + q.1) / 6) * I))
      · exact (continuous_const.mul
          ((continuous_ofReal.comp (by fun_prop)).mul continuous_const |>.cexp)).continuousOn
      · intro q hq
        exact (fdBoundary_H_hasDerivAt_arc' _ (lt_of_le_of_lt hp1_ge1 hq.1.1)
          (lt_of_lt_of_le hq.1.2 h_le3)).deriv
    · push Not at h_le3
      have hp1_ge3 : 3 ≤ p₁ := by
        by_contra h; push Not at h
        exact hfree 3 ⟨by linarith, h_le3⟩
          (by simp [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton])
      by_cases h_le4 : p₂ ≤ 4
      · apply ContinuousOn.congr (f := fun q : ℝ × ℝ =>
            (↑(H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2) : ℂ) * I)
        · exact ((continuous_ofReal.comp (by fun_prop :
            Continuous (fun q : ℝ × ℝ => H₀ + q.2 * (H₁ - H₀) - Real.sqrt 3 / 2))).mul
            continuous_const).continuousOn
        · intro q hq
          convert (fdBoundary_H_hasDerivAt_seg4 _ (lt_of_le_of_lt hp1_ge3 hq.1.1)
            (lt_of_lt_of_le hq.1.2 h_le4)).deriv using 1
          push_cast; ring
      · push Not at h_le4
        have hp1_ge4 : 4 ≤ p₁ := by
          by_contra h; push Not at h
          exact hfree 4 ⟨by linarith, h_le4⟩
            (by simp [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton])
        apply ContinuousOn.congr (f := fun _ => (1 : ℂ))
        · exact continuousOn_const
        · intro q hq
          exact (fdBoundary_H_hasDerivAt_seg5 _ (lt_of_le_of_lt hp1_ge4 hq.1.1)).deriv

private lemma fdHomot_deriv_bound (H : ℝ) (hH : heightCutoff ≤ H) :
    ∃ M, ∀ t ∈ Icc (0 : ℝ) 5, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => fdBoundaryH (heightCutoff + s * (H - heightCutoff)) t') t‖ ≤ M := by
  refine ⟨max (H - Real.sqrt 3 / 2) 1, fun t _ht s hs => ?_⟩
  set H_s := heightCutoff + s * (H - heightCutoff) with hH_s_def
  have hH_s_sqrt : Real.sqrt 3 / 2 < H_s := by nlinarith [sqrt3_div2_lt_heightCutoff, hs.1, hs.2]
  have hH_s_le : H_s ≤ H := by nlinarith [hs.2]
  rw [show (fun t' => fdBoundaryH H_s t') = fdBoundaryH H_s from rfl]
  by_cases htp : t ∈ fdBoundaryHPartition
  · have hnd : ¬DifferentiableAt ℝ (fdBoundaryH H_s) t := by
      simp only [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton] at htp
      rcases htp with rfl | rfl | rfl
      · exact fdBoundary_H_not_differentiableAt_1 hH_s_sqrt
      · exact fdBoundary_H_not_differentiableAt_3 hH_s_sqrt
      · exact fdBoundary_H_not_differentiableAt_4 hH_s_sqrt
    erw [deriv_zero_of_not_differentiableAt hnd]; rw [norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  · simp only [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton] at htp
    push Not at htp; obtain ⟨h1, h3, h4⟩ := htp
    by_cases ht1 : t < 1
    · erw [(fdBoundary_H_hasDerivAt_seg1 H_s ht1).deriv]
      rw [neg_mul, norm_neg, norm_mul,
          Complex.norm_I, mul_one,
          show (↑H_s : ℂ) - ↑(Real.sqrt 3) / 2 = ↑(H_s - Real.sqrt 3 / 2) from by
            push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hH_s_sqrt)]
      exact le_trans (by linarith) (le_max_left _ _)
    · push Not at ht1
      have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
      by_cases ht3 : t < 3
      · erw [(fdBoundary_H_hasDerivAt_arc' H_s ht1' ht3).deriv]
        rw [norm_mul, norm_mul,
            Complex.norm_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 6)),
            Complex.norm_I, mul_one, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact le_trans (by have := Real.pi_le_four; linarith) (le_max_right _ _)
      · push Not at ht3
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm h3)
        by_cases ht4 : t < 4
        · erw [(fdBoundary_H_hasDerivAt_seg4 H_s ht3' ht4).deriv]
          rw [norm_mul,
              Complex.norm_I, mul_one,
              show (↑H_s : ℂ) - ↑(Real.sqrt 3) / 2 = ↑(H_s - Real.sqrt 3 / 2) from by
                push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hH_s_sqrt)]
          exact le_trans (by linarith) (le_max_left _ _)
        · push Not at ht4
          have ht4' : 4 < t := lt_of_le_of_ne ht4 (Ne.symm h4)
          erw [(fdBoundary_H_hasDerivAt_seg5 H_s ht4').deriv]; rw [norm_one]
          exact le_max_right _ _

private lemma fdBoundary_H_piecewise_homotopic (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < heightCutoff) {H : ℝ} (hH : heightCutoff ≤ H) :
    PiecewiseCurvesHomotopicAvoiding (fdBoundaryH heightCutoff) (fdBoundaryH H)
      0 5 p fdBoundaryHPartition := by
  refine ⟨fun q => fdBoundaryH (heightCutoff + q.2 * (H - heightCutoff)) q.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fdHomot_continuous heightCutoff H
  · intro t _; simp only [zero_mul, add_zero]
  · intro t _
    change fdBoundaryH (heightCutoff + 1 * (H - heightCutoff)) t = fdBoundaryH H t
    congr 1; ring
  · intro s _; exact fdBoundary_H_closed _
  · intro t ht s hs
    exact fdBoundary_H_avoids_interior p hp_norm hp_re hp_im_pos
      (lt_of_lt_of_le hp_im (by nlinarith [hs.1] : heightCutoff ≤ _)) t ht
  · exact fun t _ ht_not_P s _ =>
      fdBoundary_H_differentiableAt_off_partition (heightCutoff + s * (H - heightCutoff)) t ht_not_P
  · exact fun p₁ p₂ _ hfree _ =>
      fdHomot_deriv_continuousOn_piece heightCutoff H p₁ p₂ hfree
  · exact fdHomot_deriv_bound H hH

/-- The winding number of the fixed boundary fdBoundary around
an interior point p is -1. -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < heightCutoff) :
    generalizedWindingNumber' fdBoundary 0 5 p = -1 := by
  have heq : RectHomotopyProof.fdBoundary = fdBoundary := by
    ext t; simp only [RectHomotopyProof.fdBoundary, fdBoundary,
      RectHomotopyProof.H_height_eq_heightCutoff]
  exact heq ▸ RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one
    p hp_norm hp_re hp_im_pos
    (RectHomotopyProof.H_height_eq_heightCutoff ▸ hp_im)

/-- Variant for upper half-plane points. -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one_uhp
    (s : UpperHalfPlane) (hs_norm : ‖(s : ℂ)‖ > 1) (hs_re : |(s : ℂ).re| < 1 / 2)
    (hs_im : (s : ℂ).im < heightCutoff) :
    generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) =
      -1 :=
  generalizedWindingNumber_fdBoundary_eq_neg_one (s : ℂ) hs_norm hs_re s.im_pos hs_im

/-- For interior points with im < heightCutoff, the generalized
winding number of fdBoundaryH around p is -1 for any
H ≥ heightCutoff. -/
theorem gWN_fdBoundary_H_eq_neg_one_of_interior (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < heightCutoff) {H : ℝ} (hH : heightCutoff ≤ H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 p =
      -1 := by
  have hbase := generalizedWindingNumber_fdBoundary_eq_neg_one p hp_norm hp_re hp_im_pos hp_im
  rw [fdBoundary_eq_fdBoundary_H] at hbase
  rcases eq_or_lt_of_le hH with rfl | _
  · exact hbase
  · have h_eq := windingNumber_eq_of_piecewise_homotopic _ _ 0 5 p fdBoundaryHPartition
        (by norm_num : (0 : ℝ) < 5)
        (fdBoundary_H_piecewise_homotopic p hp_norm hp_re hp_im_pos hp_im hH)
    exact h_eq.symm.trans hbase

private lemma gWN_translate (γ : ℝ → ℂ) (a b : ℝ) (p : ℂ) :
    generalizedWindingNumber' (fun t => γ t - p) a b 0 =
    generalizedWindingNumber' γ a b p := by unfold generalizedWindingNumber'; simp only [sub_zero]

/-- For any strict interior point with im < H, the generalized
winding number of fdBoundaryH around p is -1.
Requires H ≥ heightCutoff. -/
theorem gWN_fdBoundary_H_eq_neg_one_of_strictInterior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1 / 2)
    (hp_im_pos : 0 < p.im) {H : ℝ} (hH : heightCutoff ≤ H) (hp_im : p.im < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 p =
      -1 := by
  by_cases hp_low : p.im < heightCutoff
  · exact gWN_fdBoundary_H_eq_neg_one_of_interior p hp_norm hp_re hp_im_pos hp_low hH
  push Not at hp_low
  set Hmid := (1 + heightCutoff) / 2
  have hHmid_gt1 : 1 < Hmid := by simp only [Hmid]; linarith [one_lt_heightCutoff]
  have hHmid_lt : Hmid < heightCutoff := by simp only [Hmid]; linarith [one_lt_heightCutoff]
  set q : ℂ := ↑p.re + ↑Hmid * I
  have hq_re : q.re = p.re := by
    simp only [q, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  have hq_im : q.im = Hmid := by
    simp only [q, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hq_im_pos : 0 < q.im := hq_im ▸ by linarith
  have hq_norm : ‖q‖ > 1 := by linarith [Complex.abs_im_le_norm q, abs_of_pos hq_im_pos]
  have hq_re_bound : |q.re| < 1 / 2 := hq_re ▸ hp_re
  have hq_im_lt : q.im < heightCutoff := hq_im ▸ hHmid_lt
  have hq_wn := gWN_fdBoundary_H_eq_neg_one_of_interior q hq_norm hq_re_bound hq_im_pos
    hq_im_lt hH
  set zPath : ℝ → ℂ := fun s => ↑p.re + ↑((1 - s) * Hmid + s * p.im) * I
  have hzs_re : ∀ s, (zPath s).re = p.re := fun s => by
    simp only [zPath, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  have hzs_im : ∀ s, (zPath s).im = (1 - s) * Hmid + s * p.im := fun s => by
    simp only [zPath, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hH_sqrt : Real.sqrt 3 / 2 < H := lt_of_lt_of_le sqrt3_div2_lt_heightCutoff hH
  have hhom : PiecewiseCurvesHomotopicAvoiding
      (fun t => fdBoundaryH H t - q) (fun t => fdBoundaryH H t - p)
      0 5 0 fdBoundaryFullPartition := by
    refine ⟨fun r => fdBoundaryH H r.1 - zPath r.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((fdBoundary_H_continuous H).comp continuous_fst).sub
        ((continuous_const.add ((continuous_ofReal.comp (by fun_prop :
          Continuous (fun s => (1 - s) * Hmid + s * p.im))).mul continuous_const)).comp
          continuous_snd)
    · intro t _; change fdBoundaryH H t - zPath 0 = fdBoundaryH H t - q
      congr 1; simp only [zPath, q]; push_cast; ring
    · intro t _; change fdBoundaryH H t - zPath 1 = fdBoundaryH H t - p
      congr 1; simp only [zPath]; push_cast; ring_nf; exact Complex.re_add_im p
    · intro s _; simp only [sub_left_inj]; exact fdBoundary_H_closed H
    · intro t ht s hs
      simp only [sub_ne_zero]
      have hzs_im_ge : Hmid ≤ (zPath s).im := by
        rw [hzs_im]; nlinarith [hs.1, hs.2, hp_low, hHmid_lt]
      exact fdBoundary_H_avoids_interior (zPath s)
        (by linarith [Complex.abs_im_le_norm (zPath s),
            abs_of_pos (show 0 < (zPath s).im by linarith)])
        (by rw [hzs_re]; exact hp_re) (by linarith)
        (by rw [hzs_im]; nlinarith [hs.1, hs.2, hp_im, hHmid_lt, hH])
        t ht
    · intro t _ ht_not_P s _
      change DifferentiableAt ℝ (fun t' => fdBoundaryH H t' - zPath s) t
      have : t ∉ fdBoundaryHPartition := by
        simp only [fdBoundaryFullPartition, fdBoundaryHPartition,
          Finset.mem_insert, Finset.mem_singleton] at ht_not_P ⊢
        push Not at ht_not_P ⊢; exact ⟨ht_not_P.2.1, ht_not_P.2.2.2.1, ht_not_P.2.2.2.2.1⟩
      exact (fdBoundary_H_differentiableAt_off_partition H t this).sub
        (differentiableAt_const _)
    · intro p₁ p₂ _ hfree hsub
      change ContinuousOn (fun r : ℝ × ℝ =>
        deriv (fun t' => fdBoundaryH H t' - zPath r.2) r.1)
        (Ioo p₁ p₂ ×ˢ Icc 0 1)
      have hc_base : ContinuousOn (deriv (fdBoundaryH H)) (Ioo p₁ p₂) :=
        fun t ht => (fdBoundary_H_deriv_continuousAt_off_fullPartition H t
          (hsub ht) (hfree t ht)).continuousWithinAt
      exact (hc_base.comp continuousOn_fst (fun r hr => hr.1)).congr (fun r hr => by
        have ht_not_part : r.1 ∉ fdBoundaryHPartition := by
          simp only [fdBoundaryFullPartition, fdBoundaryHPartition,
            Finset.mem_insert, Finset.mem_singleton] at hfree ⊢
          push Not; have := hfree r.1 hr.1; push Not at this
          exact ⟨this.2.1, this.2.2.2.1, this.2.2.2.2.1⟩
        have hd := fdBoundary_H_differentiableAt_off_partition H r.1 ht_not_part
        simp only [Function.comp_def]
        erw [show (fun t' => fdBoundaryH H t' - zPath r.2) =
            fdBoundaryH H - fun _ => zPath r.2 from funext fun _ => rfl,
          deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero])
    · obtain ⟨M, hM'⟩ := piecewiseC1Immersion_deriv_bounded (fdBoundaryHImmersion H hH_sqrt)
      have hM : ∀ t ∈ Icc (0 : ℝ) 5, ‖deriv (fdBoundaryH H) t‖ ≤ M := hM'
      refine ⟨M, fun t ht s _ => ?_⟩
      change ‖deriv (fun t' => fdBoundaryH H t' - zPath s) t‖ ≤ M
      by_cases hd : DifferentiableAt ℝ (fdBoundaryH H) t
      · erw [show (fun t' => fdBoundaryH H t' - zPath s) =
            fdBoundaryH H - fun _ => zPath s from funext fun _ => rfl,
          deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
        exact hM t ht
      · have hnd : ¬DifferentiableAt ℝ (fun t' => fdBoundaryH H t' - zPath s) t := by
          erw [show (fun t' => fdBoundaryH H t' - zPath s) =
              fun t' => fdBoundaryH H t' + (-zPath s) from by ext; ring,
            differentiableAt_add_const_iff]
          exact hd
        erw [deriv_zero_of_not_differentiableAt hnd]; rw [norm_zero]
        linarith [norm_nonneg (deriv (fdBoundaryH H) t), hM t ht]
  have h_eq := windingNumber_eq_of_piecewise_homotopic _ _ 0 5 0 fdBoundaryFullPartition
    (by norm_num : (0 : ℝ) < 5) hhom
  rw [gWN_translate, gWN_translate] at h_eq
  exact h_eq.symm.trans hq_wn

end
