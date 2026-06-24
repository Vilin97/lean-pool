/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Polygon properties: values, segment functions, derivatives, differentiability

Defines per-segment functions `fdPolygonSeg1`..`fdPolygonSeg5` and proves:

* Values at key points (`fdPolygon_at_t1` .. `fdPolygon_at_t4`)
* Segment continuity and matching at breakpoints
* `fdPolygon_continuous` and `fdPolygon_closed`
* Derivative computation helpers and segment derivatives
* Segment differentiability and `fdPolygon_differentiableAt_off_partition`
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma fdPolygon_at_t1 : fdPolygon 1 = rho' := by
  simp only [fdPolygon,
    show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
  simp only [HHeight, rho']; push_cast; ring

lemma fdPolygon_at_t2 : fdPolygon 2 = iPoint := by
  simp only [fdPolygon,
    show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  simp only [chordSegment, iPoint, show (2 : ℝ) - 1 = 1 by ring, sub_self]
  simp

lemma fdPolygon_at_t3 : fdPolygon 3 = rho := by
  simp only [fdPolygon,
    show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num,
    show (3 : ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  simp only [chordSegment, rho, show (3 : ℝ) - 2 = 1 by ring, sub_self]
  simp

lemma fdPolygon_at_t4 :
    fdPolygon 4 = -1/2 + HHeight * I := by
  simp only [fdPolygon,
    show ¬(4 : ℝ) ≤ 1 from by norm_num,
    show ¬(4 : ℝ) ≤ 2 from by norm_num,
    show ¬(4 : ℝ) ≤ 3 from by norm_num,
    show (4 : ℝ) ≤ 4 from le_refl 4, ↓reduceIte]
  simp only [HHeight]; push_cast; ring

/-- The first segment of the boundary polygon (right vertical edge). -/
noncomputable def fdPolygonSeg1 : ℝ → ℂ := fun t =>
  1/2 + (HHeight - t * (HHeight - Real.sqrt 3 / 2)) * I

/-- The second segment of the boundary polygon (chord from `ρ'` to `i`). -/
noncomputable def fdPolygonSeg2 : ℝ → ℂ := fun t =>
  chordSegment rho' iPoint (t - 1)

/-- The third segment of the boundary polygon (chord from `i` to `ρ`). -/
noncomputable def fdPolygonSeg3 : ℝ → ℂ := fun t =>
  chordSegment iPoint rho (t - 2)

/-- The fourth segment of the boundary polygon (left vertical edge). -/
noncomputable def fdPolygonSeg4 : ℝ → ℂ := fun t =>
  -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (HHeight - Real.sqrt 3 / 2)) * I

/-- The fifth segment of the boundary polygon (top horizontal edge). -/
noncomputable def fdPolygonSeg5 : ℝ → ℂ := fun t => (t - 9/2) + HHeight * I

lemma fdPolygon_seg1_continuous :
    Continuous fdPolygonSeg1 := by unfold fdPolygonSeg1; continuity

lemma fdPolygon_seg2_continuous :
    Continuous fdPolygonSeg2 := by unfold fdPolygonSeg2 chordSegment; continuity

lemma fdPolygon_seg3_continuous :
    Continuous fdPolygonSeg3 := by unfold fdPolygonSeg3 chordSegment; continuity

lemma fdPolygon_seg4_continuous :
    Continuous fdPolygonSeg4 := by unfold fdPolygonSeg4; continuity

lemma fdPolygon_seg5_continuous :
    Continuous fdPolygonSeg5 := by unfold fdPolygonSeg5; continuity

lemma fdPolygon_match_t1 :
    fdPolygonSeg1 1 = fdPolygonSeg2 1 := by
  simp only [fdPolygonSeg1, fdPolygonSeg2,
    chordSegment, HHeight, rho', sub_self]
  simp

lemma fdPolygon_match_t2 :
    fdPolygonSeg2 2 = fdPolygonSeg3 2 := by
  simp only [fdPolygonSeg2, fdPolygonSeg3,
    chordSegment, iPoint, show (2 : ℝ) - 1 = 1 by ring,
    show (2 : ℝ) - 2 = 0 by ring, sub_self]
  simp

lemma fdPolygon_match_t3 :
    fdPolygonSeg3 3 = fdPolygonSeg4 3 := by
  simp only [fdPolygonSeg3, fdPolygonSeg4,
    chordSegment, rho, HHeight, show (3 : ℝ) - 2 = 1 by ring, sub_self]
  simp

lemma fdPolygon_match_t4 :
    fdPolygonSeg4 4 = fdPolygonSeg5 4 := by
  simp only [fdPolygonSeg4, fdPolygonSeg5, HHeight]
  push_cast; ring

lemma fdPolygon_continuous : Continuous fdPolygon := by
  have hf : ∀ a : ℝ, frontier {x : ℝ | x ≤ a} = {a} := fun _ => frontier_Iic
  have h_full : Continuous (fun t =>
      if t ≤ 1 then fdPolygonSeg1 t
      else if t ≤ 2 then fdPolygonSeg2 t
      else if t ≤ 3 then fdPolygonSeg3 t
      else if t ≤ 4 then fdPolygonSeg4 t
      else fdPolygonSeg5 t) := by
    apply Continuous.if
    · intro t ht; rw [hf 1, mem_singleton_iff] at ht; rw [ht]
      simpa only [show (1 : ℝ) ≤ 2 from by norm_num, ↓reduceIte] using fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hf 2, mem_singleton_iff] at ht; rw [ht]
        simpa only [show (2 : ℝ) ≤ 3 from by norm_num, ↓reduceIte] using fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · apply Continuous.if
        · intro t ht; rw [hf 3, mem_singleton_iff] at ht; rw [ht]
          simpa only [show (3 : ℝ) ≤ 4 from by norm_num, ↓reduceIte] using fdPolygon_match_t3
        · exact fdPolygon_seg3_continuous
        · apply Continuous.if
          · intro t ht; rw [hf 4, mem_singleton_iff] at ht; rw [ht]
            exact fdPolygon_match_t4
          · exact fdPolygon_seg4_continuous
          · exact fdPolygon_seg5_continuous
  exact h_full

lemma fdPolygon_closed : fdPolygon 0 = fdPolygon 5 := by
  simp only [fdPolygon, show ¬(5 : ℝ) ≤ 1 from by norm_num, show ¬(5 : ℝ) ≤ 2 from by norm_num,
    show ¬(5 : ℝ) ≤ 3 from by norm_num, show ¬(5 : ℝ) ≤ 4 from by norm_num,
    show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte, HHeight]
  push_cast; ring

lemma Complex.deriv_ofReal' :
    deriv (fun t : ℝ => (↑t : ℂ)) = fun _ => 1 :=
  funext fun t => (Complex.ofRealCLM.hasDerivAt (x := t)).deriv

lemma deriv_affine_mul (a b : ℂ) :
    deriv (fun t : ℝ => a + ↑t * b) = fun _ => b := by
  ext t
  have h_add : HasDerivAt (fun t : ℝ => a + ↑t * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add (Complex.ofRealCLM.hasDerivAt.mul_const b)
  simpa using h_add.deriv

lemma deriv_affine_shifted_mul (a b : ℂ) (c : ℝ) :
    deriv (fun t : ℝ => a + (↑t - ↑c) * b) = fun _ => b := by
  ext t
  have h_sub : HasDerivAt (fun t : ℝ => (↑t : ℂ) - ↑c) (1 - 0) t :=
    Complex.ofRealCLM.hasDerivAt.sub (hasDerivAt_const t (↑c : ℂ))
  have h_add : HasDerivAt (fun t : ℝ => a + (↑t - ↑c) * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add (by simpa using h_sub.mul_const b)
  simpa using h_add.deriv

lemma fdPolygon_deriv_seg1 :
    deriv fdPolygonSeg1 =
      fun _ => -(HHeight - Real.sqrt 3 / 2) * I := by
  have hrw : fdPolygonSeg1 = fun (t : ℝ) => ((1 : ℂ)/2 + HHeight * I) + ↑t *
        (-(HHeight - Real.sqrt 3 / 2) * I) := by ext t; simp only [fdPolygonSeg1]; ring
  rw [hrw, deriv_affine_mul]

lemma fdPolygon_deriv_seg2 :
    deriv fdPolygonSeg2 = fun _ => iPoint - rho' := by
  have hrw : fdPolygonSeg2 = fun (t : ℝ) =>
      rho' + (↑t - ↑(1 : ℝ)) * (iPoint - rho') := by
    ext t
    simp only [fdPolygonSeg2, chordSegment, rho',
      iPoint, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg3 :
    deriv fdPolygonSeg3 = fun _ => rho - iPoint := by
  have hrw : fdPolygonSeg3 = fun (t : ℝ) =>
      iPoint + (↑t - ↑(2 : ℝ)) * (rho - iPoint) := by
    ext t
    simp only [fdPolygonSeg3, chordSegment, rho,
      iPoint, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
    push_cast; ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg4 :
    deriv fdPolygonSeg4 =
      fun _ => (HHeight - Real.sqrt 3 / 2) * I := by
  have hrw : fdPolygonSeg4 = fun (t : ℝ) =>
      (-(1 : ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - ↑(3 : ℝ)) *
        ((HHeight - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygonSeg4, HHeight]
    push_cast; ring
  rw [hrw, deriv_affine_shifted_mul]

lemma fdPolygon_deriv_seg5 :
    deriv fdPolygonSeg5 = fun _ => 1 := by
  have hrw : fdPolygonSeg5 = fun (t : ℝ) => (-(9 : ℂ)/2 + HHeight * I) + ↑t * (1 : ℂ) := by
    ext t; simp only [fdPolygonSeg5, HHeight]
    push_cast; ring
  rw [hrw, deriv_affine_mul]

/-- An affine map `t ↦ a + ↑t * b` is `ℝ`-differentiable. -/
private lemma differentiable_affine_mul (a b : ℂ) :
    Differentiable ℝ (fun t : ℝ => a + ↑t * b) :=
  (differentiable_const _).add (Complex.ofRealCLM.differentiable.mul (differentiable_const _))

/-- A shifted affine map `t ↦ a + (↑t - c) * b` is `ℝ`-differentiable. -/
private lemma differentiable_affine_shifted_mul (a b c : ℂ) :
    Differentiable ℝ (fun t : ℝ => a + (↑t - c) * b) :=
  (differentiable_const _).add
    ((Complex.ofRealCLM.differentiable.sub (differentiable_const _)).mul (differentiable_const _))

lemma fdPolygon_seg1_differentiable :
    Differentiable ℝ fdPolygonSeg1 := by
  have h : fdPolygonSeg1 = fun (t : ℝ) => ((1 : ℂ)/2 + HHeight * I) + ↑t *
        (-(HHeight - Real.sqrt 3 / 2) * I) := by ext t; simp only [fdPolygonSeg1]; ring
  rw [h]; exact differentiable_affine_mul _ _

lemma fdPolygon_seg2_differentiable :
    Differentiable ℝ fdPolygonSeg2 := by
  have h : fdPolygonSeg2 = fun (t : ℝ) =>
      rho' + (↑t - (1 : ℂ)) * (iPoint - rho') := by
    ext t
    simp only [fdPolygonSeg2, chordSegment, rho',
      iPoint, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [h]; exact differentiable_affine_shifted_mul _ _ _

lemma fdPolygon_seg3_differentiable :
    Differentiable ℝ fdPolygonSeg3 := by
  have h : fdPolygonSeg3 = fun (t : ℝ) =>
      iPoint + (↑t - (2 : ℂ)) * (rho - iPoint) := by
    ext t
    simp only [fdPolygonSeg3, chordSegment, rho,
      iPoint, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [h]; exact differentiable_affine_shifted_mul _ _ _

lemma fdPolygon_seg4_differentiable :
    Differentiable ℝ fdPolygonSeg4 := by
  have h : fdPolygonSeg4 = fun (t : ℝ) => (-(1 : ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - (3 : ℂ)) *
        ((HHeight - Real.sqrt 3 / 2) * I) := by
    ext t; simp only [fdPolygonSeg4, HHeight]
    push_cast; ring
  rw [h]; exact differentiable_affine_shifted_mul _ _ _

lemma fdPolygon_seg5_differentiable :
    Differentiable ℝ fdPolygonSeg5 := by
  have h : fdPolygonSeg5 = fun (t : ℝ) => (-(9 : ℂ)/2 + HHeight * I) + ↑t * (1 : ℂ) := by
    ext t; simp only [fdPolygonSeg5, HHeight]
    push_cast; ring
  rw [h]; exact differentiable_affine_mul _ _

lemma fdPolygon_differentiableAt_off_partition (t : ℝ) (ht : t ∈ Ioo 0 5)
    (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ)) :
    DifferentiableAt ℝ fdPolygon t := by
  simp only [Finset.mem_insert, Finset.mem_singleton,
    not_or] at ht_not_P
  obtain ⟨ht_ne1, ht_ne2, ht_ne3, ht_ne4⟩ := ht_not_P
  by_cases h1 : t < 1
  · have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg1 := by
      filter_upwards [eventually_lt_nhds h1,
        eventually_gt_nhds ht.1] with s hs1 hs2
      simp only [fdPolygon,
        show s ≤ 1 from le_of_lt hs1, if_true,
        fdPolygonSeg1]
    exact fdPolygon_seg1_differentiable.differentiableAt.congr_of_eventuallyEq heq
  · push Not at h1
    by_cases h2 : t < 2
    · have h1' : t > 1 :=
        lt_of_le_of_ne h1 (Ne.symm ht_ne1)
      have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg2 := by
        filter_upwards [eventually_gt_nhds h1',
          eventually_lt_nhds h2] with s hs1 hs2
        simp only [fdPolygon,
          show ¬s ≤ 1 from not_le.mpr hs1,
          show s ≤ 2 from le_of_lt hs2,
          if_true, if_false, fdPolygonSeg2]
      exact fdPolygon_seg2_differentiable.differentiableAt.congr_of_eventuallyEq heq
    · push Not at h2
      by_cases h3 : t < 3
      · have h2' : t > 2 :=
          lt_of_le_of_ne h2 (Ne.symm ht_ne2)
        have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg3 := by
          filter_upwards [eventually_gt_nhds h2',
            eventually_lt_nhds h3] with s hs1 hs2
          simp only [fdPolygon,
            show ¬s ≤ 1 from not_le.mpr (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
                (le_of_lt hs1)),
            show ¬s ≤ 2 from not_le.mpr hs1,
            show s ≤ 3 from le_of_lt hs2,
            if_true, if_false, fdPolygonSeg3]
        exact fdPolygon_seg3_differentiable.differentiableAt.congr_of_eventuallyEq heq
      · push Not at h3
        by_cases h4 : t < 4
        · have h3' : t > 3 :=
            lt_of_le_of_ne h3 (Ne.symm ht_ne3)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg4 := by
            filter_upwards [eventually_gt_nhds h3',
              eventually_lt_nhds h4] with s hs1 hs2
            simp only [fdPolygon,
              show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) hs1),
              show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) hs1),
              show ¬s ≤ 3 from not_le.mpr hs1,
              show s ≤ 4 from le_of_lt hs2,
              if_true, if_false, fdPolygonSeg4]
          exact fdPolygon_seg4_differentiable.differentiableAt.congr_of_eventuallyEq heq
        · push Not at h4
          have h4' : t > 4 :=
            lt_of_le_of_ne h4 (Ne.symm ht_ne4)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygonSeg5 := by
            filter_upwards [eventually_gt_nhds h4',
              eventually_lt_nhds ht.2] with s hs1 hs2
            simp only [fdPolygon,
              show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) hs1),
              show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) hs1),
              show ¬s ≤ 3 from not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) hs1),
              show ¬s ≤ 4 from not_le.mpr hs1,
              if_false, fdPolygonSeg5]
          exact fdPolygon_seg5_differentiable.differentiableAt.congr_of_eventuallyEq heq

lemma fdPolygon_seg1_deriv_val :
    -(HHeight - Real.sqrt 3 / 2) * I = -I := by simp only [HHeight]; push_cast; ring

lemma fdPolygon_seg4_deriv_val : (HHeight - Real.sqrt 3 / 2) * I = I := by
  simp only [HHeight]; push_cast; ring

end RectHomotopyProof
