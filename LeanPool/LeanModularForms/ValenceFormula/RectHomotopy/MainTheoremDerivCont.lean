/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.BoundaryHomotopySmooth

/-!
# Derivative continuity for the homotopy on partition pieces

Proves that the t-derivative of `fdBoundaryToPolygonHomotopy` is continuous
on each partition piece `(p₁, p₂) × [0, 1]`, where `(p₁, p₂)` avoids the
partition points `{1, 2, 3, 4}`.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- On `(1, 2)`, the homotopy's `t`-derivative equals the arc/chord formula at `(t, s)`. -/
private lemma seg2_deriv_eq (s t : ℝ) (ht1 : 1 < t) (ht2 : t < 2) :
    deriv (fun t' => fdBoundaryToPolygonHomotopy (t', s)) t =
      (1 - s) • ((Real.pi / 6) * I *
        Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 6)) * I)) + s • (iPoint - rho') := by
  have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
      (fun t' : ℝ =>
        let arc_point := Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 6)) * I)
        let chord_point := chordSegment rho' iPoint (t' - 1)
        (1 - s) • arc_point + s • chord_point) := by
    filter_upwards [eventually_gt_nhds ht1, eventually_lt_nhds ht2] with t' ht1' ht2'
    simp only [fdBoundaryToPolygonHomotopy]
    simp only [not_le.mpr ht1', le_of_lt ht2', ite_false, ite_true]
    congr 2; ring_nf
  rw [heq.deriv_eq]
  have h_inner : HasDerivAt (fun t' : ℝ =>
      (Real.pi : ℂ) / 3 + ((t' : ℂ) - 1) * ((Real.pi : ℂ) / 6)) ((Real.pi : ℂ) / 6) t := by
    have h_shift : HasDerivAt (fun t' : ℝ => (t' : ℂ) - 1) 1 t :=
      Complex.ofRealCLM.hasDerivAt.sub_const 1
    have h_mul := h_shift.mul_const ((Real.pi : ℂ) / 6)
    simp only [one_mul] at h_mul
    exact h_mul.const_add ((Real.pi : ℂ) / 3)
  have h_arc : HasDerivAt (fun t' : ℝ =>
      Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 6)) * I))
      ((Real.pi / 6) * I * Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 6)) * I)) t := by
    have h_comp := (Complex.hasDerivAt_exp (((Real.pi : ℂ) / 3 +
      ((t : ℂ) - 1) * ((Real.pi : ℂ) / 6)) * I)).comp t (h_inner.mul_const I)
    simp only [mul_comm (Complex.exp _)] at h_comp
    exact h_comp
  have h_chord : HasDerivAt (fun t' : ℝ => chordSegment rho' iPoint (t' - 1))
      (iPoint - rho') t := by
    simp only [chordSegment]
    have h_shift : HasDerivAt (fun t' : ℝ => t' - 1) (1 : ℝ) t := (hasDerivAt_id t).sub_const 1
    have h1 : HasDerivAt (fun t' : ℝ => (1 - (t' - 1)) • rho') (-rho') t := by
      have h_coef : HasDerivAt (fun t' : ℝ => (1 - (t' - 1) : ℝ)) (-1 : ℝ) t := by
        have := (hasDerivAt_const t (1 : ℝ)).sub h_shift
        simp only [zero_sub] at this
        exact this
      have := h_coef.smul_const rho'
      simpa only [neg_one_smul] using this
    have h2 : HasDerivAt (fun t' : ℝ => (t' - 1) • iPoint) iPoint t := by
      have := h_shift.smul_const iPoint
      simpa only [one_smul] using this
    exact (h1.add h2).congr_deriv (by ring)
  exact ((h_arc.const_smul (1 - s)).add (h_chord.const_smul s)).deriv

/-- On `(2, 3)`, the homotopy's `t`-derivative equals the arc/chord formula at `(t, s)`. -/
private lemma seg3_deriv_eq (s t : ℝ) (ht2 : 2 < t) (ht3 : t < 3) :
    deriv (fun t' => fdBoundaryToPolygonHomotopy (t', s)) t =
      (1 - s) • ((Real.pi / 6) * I *
        Complex.exp ((Real.pi / 2 + (t - 2) * (Real.pi / 6)) * I)) + s • (rho - iPoint) := by
  have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', s)) =ᶠ[𝓝 t]
      (fun t' : ℝ =>
        let arc_point := Complex.exp ((Real.pi / 2 + (t' - 2) * (Real.pi / 6)) * I)
        let chord_point := chordSegment iPoint rho (t' - 2)
        (1 - s) • arc_point + s • chord_point) := by
    filter_upwards [eventually_gt_nhds ht2, eventually_lt_nhds ht3] with t' ht2' ht3'
    simp only [fdBoundaryToPolygonHomotopy]
    simp only [not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) ht2'), not_le.mpr ht2',
      le_of_lt ht3', ite_false, ite_true]
    congr 2; ring_nf
  rw [heq.deriv_eq]
  have h_inner : HasDerivAt (fun t' : ℝ =>
      (Real.pi : ℂ) / 2 + ((t' : ℂ) - 2) * ((Real.pi : ℂ) / 6)) ((Real.pi : ℂ) / 6) t := by
    have h_shift : HasDerivAt (fun t' : ℝ => (t' : ℂ) - 2) 1 t :=
      Complex.ofRealCLM.hasDerivAt.sub_const 2
    have h_mul := h_shift.mul_const ((Real.pi : ℂ) / 6)
    simp only [one_mul] at h_mul
    exact h_mul.const_add ((Real.pi : ℂ) / 2)
  have h_arc : HasDerivAt (fun t' : ℝ =>
      Complex.exp ((Real.pi / 2 + (t' - 2) * (Real.pi / 6)) * I))
      ((Real.pi / 6) * I * Complex.exp ((Real.pi / 2 + (t - 2) * (Real.pi / 6)) * I)) t := by
    have h_comp := (Complex.hasDerivAt_exp (((Real.pi : ℂ) / 2 +
      ((t : ℂ) - 2) * ((Real.pi : ℂ) / 6)) * I)).comp t (h_inner.mul_const I)
    simp only [mul_comm (Complex.exp _)] at h_comp
    exact h_comp
  have h_chord : HasDerivAt (fun t' : ℝ => chordSegment iPoint rho (t' - 2))
      (rho - iPoint) t := by
    simp only [chordSegment]
    have h_shift : HasDerivAt (fun t' : ℝ => t' - 2) (1 : ℝ) t := (hasDerivAt_id t).sub_const 2
    have h1 : HasDerivAt (fun t' : ℝ => (1 - (t' - 2)) • iPoint) (-iPoint) t := by
      have h_coef : HasDerivAt (fun t' : ℝ => (1 - (t' - 2) : ℝ)) (-1 : ℝ) t := by
        have := (hasDerivAt_const t (1 : ℝ)).sub h_shift
        simp only [zero_sub] at this
        exact this
      have := h_coef.smul_const iPoint
      simpa only [neg_one_smul] using this
    have h2 : HasDerivAt (fun t' : ℝ => (t' - 2) • rho) rho t := by
      have := h_shift.smul_const rho
      simpa only [one_smul] using this
    exact (h1.add h2).congr_deriv (by ring)
  exact ((h_arc.const_smul (1 - s)).add (h_chord.const_smul s)).deriv

private lemma deriv_cont_seg1 (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂) (h_seg1 : p₂ ≤ 1) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    have hconst : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1,
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
        -((HHeight : ℂ) - Real.sqrt 3 / 2) * I := by
      intro q ⟨hq1, _hq2⟩
      have ht_lt1 : q.1 < 1 := lt_of_lt_of_le hq1.2 h_seg1
      have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => (1/2 : ℂ) + (HHeight - (↑t' : ℂ) * (HHeight - Real.sqrt 3 / 2)) * I) := by
        filter_upwards [eventually_lt_nhds ht_lt1] with t' ht'
        simp only [fdBoundaryToPolygonHomotopy, le_of_lt ht', ite_true]
      rw [heq.deriv_eq]
      have h1 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ)) 1 q.1 := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
          ((HHeight : ℂ) - Real.sqrt 3 / 2) q.1 := by
        have := h1.mul_const ((HHeight : ℂ) - Real.sqrt 3 / 2)
        simp only [one_mul] at this; exact this
      have h3 : HasDerivAt (fun t' : ℝ =>
            (HHeight : ℂ) - (↑t' : ℂ) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
          (-((HHeight : ℂ) - Real.sqrt 3 / 2)) q.1 := by
        have := (hasDerivAt_const q.1 (HHeight : ℂ)).sub h2
        simp only [zero_sub] at this; exact this
      have h5 := (hasDerivAt_const q.1 ((1/2 : ℂ))).add (h3.mul_const I)
      simp only [zero_add] at h5; convert h5.deriv using 2
      all_goals rfl
    apply ContinuousOn.congr continuousOn_const hconst

private lemma deriv_cont_seg2 (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂)
    (h_seg2_lo : p₁ ≥ 1) (h_seg2_hi : p₂ ≤ 2) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    apply continuousOn_of_forall_continuousAt
    intro q ⟨hq1, hq2⟩
    have ht_gt1 : q.1 > 1 := lt_of_le_of_lt h_seg2_lo hq1.1
    have ht_lt2 : q.1 < 2 := lt_of_lt_of_le hq1.2 h_seg2_hi
    have hderiv_eq := seg2_deriv_eq q.2 q.1 ht_gt1 ht_lt2
    have h_formula_cont : ContinuousAt (fun r : ℝ × ℝ => (1 - r.2) •
            ((Real.pi / 6) * I * Complex.exp ((Real.pi / 3 + (r.1 - 1) * (Real.pi / 6)) * I)) +
          r.2 • (iPoint - rho')) q := by fun_prop
    apply h_formula_cont.congr
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (Ioo_mem_nhds hq1.1 hq1.2) univ_mem] with r hr
    exact (seg2_deriv_eq r.2 r.1 (lt_of_le_of_lt h_seg2_lo hr.1.1)
      (lt_of_lt_of_le hr.1.2 h_seg2_hi)).symm

private lemma deriv_cont_seg3 (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂)
    (h_seg3_lo : p₁ ≥ 2) (h_seg3_hi : p₂ ≤ 3) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    apply continuousOn_of_forall_continuousAt
    intro q ⟨hq1, _hq2⟩
    have h_formula_cont : ContinuousAt (fun r : ℝ × ℝ => (1 - r.2) •
            ((Real.pi / 6) * I * Complex.exp ((Real.pi / 2 + (r.1 - 2) * (Real.pi / 6)) * I)) +
          r.2 • (rho - iPoint)) q := by fun_prop
    apply h_formula_cont.congr
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (Ioo_mem_nhds hq1.1 hq1.2) univ_mem] with r hr
    exact (seg3_deriv_eq r.2 r.1 (lt_of_le_of_lt h_seg3_lo hr.1.1)
      (lt_of_lt_of_le hr.1.2 h_seg3_hi)).symm

private lemma deriv_cont_seg4 (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂)
    (h_seg4_lo : p₁ ≥ 3) (h_seg4_hi : p₂ ≤ 4) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    have hconst : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1,
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1 =
        (((HHeight : ℂ) - Real.sqrt 3 / 2) * I) := by
      intro q ⟨hq1, _hq2⟩
      have ht_gt3 : q.1 > 3 := lt_of_le_of_lt h_seg4_lo hq1.1
      have ht_lt4 : q.1 < 4 := lt_of_lt_of_le hq1.2 h_seg4_hi
      have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => (-1/2 : ℂ) +
              ((Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) *
                ((HHeight : ℂ) - Real.sqrt 3 / 2)) * I) := by
        filter_upwards [eventually_gt_nhds ht_gt3, eventually_lt_nhds ht_lt4] with t' ht3' ht4'
        simp only [fdBoundaryToPolygonHomotopy,
          not_le.mpr (by linarith : 1 < t'), not_le.mpr (by linarith : 2 < t'),
          not_le.mpr ht3', le_of_lt ht4', ite_false, ite_true]
      rw [heq.deriv_eq]
      have h1 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ)) 1 q.1 := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t' : ℝ => (↑t' : ℂ) - 3) 1 q.1 := h1.sub_const 3
      have h3 : HasDerivAt (fun t' : ℝ => ((↑t' : ℂ) - 3) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
          ((HHeight : ℂ) - Real.sqrt 3 / 2) q.1 := by
        have := h2.mul_const ((HHeight : ℂ) - Real.sqrt 3 / 2)
        simp only [one_mul] at this; exact this
      have h4 : HasDerivAt (fun t' : ℝ =>
            (Real.sqrt 3 / 2 : ℂ) + ((↑t' : ℂ) - 3) * ((HHeight : ℂ) - Real.sqrt 3 / 2))
          ((HHeight : ℂ) - Real.sqrt 3 / 2) q.1 := by
        have := (hasDerivAt_const q.1 (Real.sqrt 3 / 2 : ℂ)).add h3
        simp only [zero_add] at this; exact this
      have h6 := (hasDerivAt_const q.1 ((-1/2 : ℂ))).add (h4.mul_const I)
      simp only [zero_add] at h6; exact h6.deriv
    apply ContinuousOn.congr continuousOn_const hconst

private lemma deriv_cont_seg5 (p₁ p₂ : ℝ) (_hp₁p₂ : p₁ < p₂) (h_seg5 : p₁ ≥ 4) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
    have hconst : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1,
        deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1 = (1 : ℂ) := by
      intro q ⟨hq1, _hq2⟩
      have ht_gt4 : q.1 > 4 := lt_of_le_of_lt h_seg5 hq1.1
      have heq : (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) =ᶠ[𝓝 q.1]
          (fun t' : ℝ => ((↑t' : ℂ) - 9/2) + (HHeight : ℂ) * I) := by
        filter_upwards [eventually_gt_nhds ht_gt4] with t' ht4'
        simp only [fdBoundaryToPolygonHomotopy,
          not_le.mpr (by linarith : 1 < t'), not_le.mpr (by linarith : 2 < t'),
          not_le.mpr (by linarith : 3 < t'), not_le.mpr ht4', ite_false]
      rw [heq.deriv_eq]
      have hd : HasDerivAt (fun t' : ℝ => ((↑t' : ℂ) - 9/2) + (HHeight : ℂ) * I) 1 q.1 :=
        (Complex.ofRealCLM.hasDerivAt.sub_const (9/2)).add_const ((HHeight : ℂ) * I)
      exact hd.deriv
    apply ContinuousOn.congr continuousOn_const hconst

lemma fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces (p₁ p₂ : ℝ) (hp₁p₂ : p₁ < p₂)
    (hpiece : ∀ t ∈ Ioo p₁ p₂,
      t ∉ ({1, 2, 3, 4} : Finset ℝ))
    (h_sub : Ioo p₁ p₂ ⊆ Ioo 0 5) :
    ContinuousOn (fun (q : ℝ × ℝ) =>
        deriv (fun t' =>
          fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
      (Ioo p₁ p₂ ×ˢ Icc 0 1) := by
  rcases interval_in_segment p₁ p₂ hp₁p₂ hpiece h_sub with
    h_seg1 | ⟨h_seg2_lo, h_seg2_hi⟩ | ⟨h_seg3_lo, h_seg3_hi⟩ |
    ⟨h_seg4_lo, h_seg4_hi⟩ | h_seg5
  · exact deriv_cont_seg1 p₁ p₂ hp₁p₂ h_seg1
  · exact deriv_cont_seg2 p₁ p₂ hp₁p₂ h_seg2_lo h_seg2_hi
  · exact deriv_cont_seg3 p₁ p₂ hp₁p₂ h_seg3_lo h_seg3_hi
  · exact deriv_cont_seg4 p₁ p₂ hp₁p₂ h_seg4_lo h_seg4_hi
  · exact deriv_cont_seg5 p₁ p₂ hp₁p₂ h_seg5

end RectHomotopyProof
