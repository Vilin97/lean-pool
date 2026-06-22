/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Bounds

/-!
# Fundamental Domain Boundary – Smoothness

Differentiability, derivatives, limits, and curve/immersion constructions
for the fundamental domain boundary.

## Main Definitions

* `fdBoundaryHCurve` — H-parameterized boundary as `PiecewiseC1Curve`
* `fdBoundaryHImmersion` — H-parameterized boundary as `PiecewiseC1Immersion`
* `fdBoundaryCurve` — fixed-height boundary as `PiecewiseC1Curve`
* `fdBoundaryImmersion` — fixed-height boundary as `PiecewiseC1Immersion`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
private instance : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
private instance : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul

-- The arc on t ∈ (1,3) is ArcCalculus.unitArc (π/3) (2π/3) 1 3.
private lemma arc_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s' : ℝ => exp ((↑Real.pi * (↑s' + 1) / 6) * I))
      (exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I)) s := by
  have h := ArcCalculus.unitArc_hasDerivAt
    (Real.pi / 3) (Real.pi * 2 / 3) (1 : ℝ) (3 : ℝ) s (by norm_num)
  have hfun : ArcCalculus.unitArc (Real.pi / 3) (Real.pi * 2 / 3) (1 : ℝ) (3 : ℝ) =
      fun s' : ℝ => exp ((↑Real.pi * (↑s' + 1) / 6) * I) := by
    funext s'; simp only [ArcCalculus.unitArc]; push_cast; ring_nf
  rw [hfun] at h
  convert h using 1
  congr 1; congr 1; push_cast; ring

private lemma fdBoundary_H_eq_arc_near {H : ℝ} {s : ℝ}
    (hs1 : 1 < s) (hs3 : s < 3) :
    fdBoundaryH H =ᶠ[𝓝 s] fun s' =>
      exp ((↑Real.pi * (↑s' + 1) / 6) * I) := by
  filter_upwards [Ioi_mem_nhds hs1, Iio_mem_nhds hs3]
    with s' hs1' hs3'
  simp only [fdBoundaryH, show ¬s' ≤ 1 from not_le.mpr hs1']
  by_cases hs2' : s' ≤ 2
  · simp only [hs2', ite_true, ite_false]
    congr 1; ring
  · simp only [show ¬s' ≤ 2 from hs2',
      show s' ≤ 3 from le_of_lt hs3', ite_true, ite_false]
    congr 1; ring

private lemma arc_deriv_continuous :
    Continuous (fun s : ℝ =>
      exp ((↑Real.pi * (↑s + 1) / 6) * I) *
        (↑Real.pi / 6 * I)) :=
  (Complex.continuous_exp.comp
    (((continuous_const.mul
      (Complex.continuous_ofReal.add continuous_const)).div_const
        _).mul continuous_const)).mul continuous_const

private lemma arc_limit_ne_zero (c : ℝ) :
    exp ((↑Real.pi * (↑c + 1) / 6) * I) *
      (↑Real.pi / 6 * I) ≠ 0 :=
  mul_ne_zero (exp_ne_zero _) (mul_ne_zero
    (div_ne_zero (by exact_mod_cast ne_of_gt Real.pi_pos)
      (by norm_num : (6 : ℂ) ≠ 0)) I_ne_zero)

lemma fdBoundary_H_differentiableAt_off_partition
    (H : ℝ) (t : ℝ)
    (htp : t ∉ fdBoundaryHPartition) :
    DifferentiableAt ℝ (fdBoundaryH H) t := by
  simp only [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp; obtain ⟨ht1, ht3, ht4⟩ := htp
  by_cases h1 : t < 1
  · have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s =>
        (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      simp only [fdBoundaryH, show s ≤ 1 from le_of_lt hs, ite_true]
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((differentiableAt_const _ |>.sub
        (Complex.ofRealCLM.differentiable.differentiableAt |>.mul
          (differentiableAt_const _))).mul (differentiableAt_const _))).congr_of_eventuallyEq heq
  · by_cases h3 : t < 3
    · exact (arc_hasDerivAt t).differentiableAt.congr_of_eventuallyEq
        (fdBoundary_H_eq_arc_near (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm ht1)) h3)
    · by_cases h4 : t < 4
      · have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s =>
            (-1 : ℂ) / 2 +
              (↑(Real.sqrt 3) / 2 +
                (↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
          filter_upwards [Ioi_mem_nhds (lt_of_le_of_ne (not_lt.mp h3) (Ne.symm ht3)),
            Iio_mem_nhds h4] with s (hs3 : 3 < s) (hs4 : s < 4)
          simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith, show ¬s ≤ 2 from by linarith,
            show ¬s ≤ 3 from by linarith, show s ≤ 4 from by linarith, ite_true, ite_false]
        exact (DifferentiableAt.add (differentiableAt_const _)
          ((differentiableAt_const _ |>.add
            ((Complex.ofRealCLM.differentiable.differentiableAt |>.sub
              (differentiableAt_const _)).mul (differentiableAt_const _))).mul
            (differentiableAt_const _))).congr_of_eventuallyEq heq
      · have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s => (↑s - 9/2 : ℂ) + ↑H * I := by
          filter_upwards [Ioi_mem_nhds (lt_of_le_of_ne (not_lt.mp h4) (Ne.symm ht4))]
            with s (hs4 : 4 < s)
          simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith, show ¬s ≤ 2 from by linarith,
            show ¬s ≤ 3 from by linarith, show ¬s ≤ 4 from by linarith, ite_false]
        exact (DifferentiableAt.add
          (Complex.ofRealCLM.differentiable.differentiableAt |>.sub
            (differentiableAt_const _)) (differentiableAt_const _)).congr_of_eventuallyEq heq

lemma fdBoundary_H_hasDerivAt_seg1' (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fdBoundaryH H)
      (-(H - Real.sqrt 3 / 2) * I) t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t]
      fun s => (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simp only [fdBoundaryH, show s ≤ 1 from le_of_lt hs.2, ite_true]
  have h1 : HasDerivAt (fun s : ℝ => (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
      (-(↑H - ↑(Real.sqrt 3) / 2) * I) t := by
    have h2 : HasDerivAt (fun s : ℝ => (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
        ((0 - 1 * (↑H - ↑(Real.sqrt 3) / 2)) * I) t := by
      apply HasDerivAt.mul_const
      exact (hasDerivAt_const t (↑H : ℂ)).sub ((hasDerivAt_id t).ofReal_comp.mul_const _)
    simp only [zero_sub, one_mul] at h2; exact h2
  have hd : HasDerivAt (fun s : ℝ =>
      (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
      (-(↑H - ↑(Real.sqrt 3) / 2) * I) t := by
    exact h1.const_add ((1 : ℂ) / 2)
  exact hd.congr_of_eventuallyEq heq

lemma fdBoundary_H_hasDerivAt_seg4' (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (3 : ℝ) 4) :
    HasDerivAt (fdBoundaryH H)
      ((H - Real.sqrt 3 / 2) * I) t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s : ℝ => (-1 : ℂ) / 2 +
      (↑(Real.sqrt 3) / 2 + (↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s ⟨hs1, hs2⟩
    simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith,
      show ¬s ≤ 2 from by linarith, show ¬s ≤ 3 from by linarith,
      show s ≤ 4 from by linarith, ite_true, ite_false]
  have hd : HasDerivAt (fun s : ℝ => (-1 : ℂ) / 2 +
      (↑(Real.sqrt 3) / 2 + (↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)
      ((↑H - ↑(Real.sqrt 3) / 2) * I) t := by
    have h_ofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h_lin : HasDerivAt (fun s : ℝ => (↑s : ℂ) - 3) 1 t := by
      have := h_ofReal.sub (hasDerivAt_const t (3 : ℂ)); simp only [sub_zero] at this; exact this
    have h_scaled : HasDerivAt (fun s : ℝ => ((↑s : ℂ) - 3) * (↑H - ↑(Real.sqrt 3) / 2))
        (1 * (↑H - ↑(Real.sqrt 3) / 2)) t := h_lin.mul_const _
    have h_shifted : HasDerivAt (fun s : ℝ =>
        ↑(Real.sqrt 3) / 2 + ((↑s : ℂ) - 3) * (↑H - ↑(Real.sqrt 3) / 2))
        (0 + 1 * (↑H - ↑(Real.sqrt 3) / 2)) t := (hasDerivAt_const t _).add h_scaled
    have h_timesI : HasDerivAt (fun s : ℝ =>
        (↑(Real.sqrt 3) / 2 + ((↑s : ℂ) - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)
        ((0 + 1 * (↑H - ↑(Real.sqrt 3) / 2)) * I) t := h_shifted.mul_const _
    have h_final : HasDerivAt (fun s : ℝ => (-1 : ℂ) / 2 +
        (↑(Real.sqrt 3) / 2 + ((↑s : ℂ) - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)
        (0 + (0 + 1 * (↑H - ↑(Real.sqrt 3) / 2)) * I) t := (hasDerivAt_const t _).add h_timesI
    simp only [zero_add, one_mul] at h_final; exact h_final
  exact hd.congr_of_eventuallyEq heq

lemma fdBoundary_H_hasDerivAt_seg5' (H : ℝ) (t : ℝ)
    (ht : t ∈ Ioo (4 : ℝ) 5) :
    HasDerivAt (fdBoundaryH H) 1 t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s ⟨hs1, hs2⟩
    simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith,
      show ¬s ≤ 2 from by linarith, show ¬s ≤ 3 from by linarith,
      show ¬s ≤ 4 from by linarith, ite_false]
  have h1 : HasDerivAt (fun s : ℝ => (↑s - 9/2 : ℂ)) (1 : ℂ) t := by
    have := ((hasDerivAt_id t).ofReal_comp).sub (hasDerivAt_const t (9/2 : ℂ))
    simp only [sub_zero, ofReal_one] at this; exact this
  exact (h1.add (hasDerivAt_const t (↑H * I : ℂ)) |>.congr_deriv (by simp only [add_zero])
    ).congr_of_eventuallyEq heq

lemma fdBoundary_H_deriv_ne_zero_off_fullPartition
    (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5)
    (htp : t ∉ fdBoundaryFullPartition) :
    deriv (fdBoundaryH H) t ≠ 0 := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp; obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩ := htp
  have ht' : t ∈ Ioo (0 : ℝ) 5 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
     lt_of_le_of_ne ht.2 ht5⟩
  by_cases h1 : t < 1
  · have hd := (fdBoundary_H_hasDerivAt_seg1' H t ⟨ht'.1, h1⟩)
    rw [show deriv (fdBoundaryH H) t = _ from hd.deriv]
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero, sub_eq_zero, I_ne_zero, or_false]
    intro h; apply_fun Complex.re at h
    simp [ofReal_re] at h; linarith
  · push Not at h1
    have h1' : 1 < t := lt_of_le_of_ne h1 (Ne.symm ht1)
    by_cases h3 : t < 3
    · have hd := ((arc_hasDerivAt t).congr_of_eventuallyEq
          (fdBoundary_H_eq_arc_near (H := H) h1' h3))
      rw [show deriv (fdBoundaryH H) t = _ from hd.deriv]
      exact arc_limit_ne_zero t
    · push Not at h3
      have h3' : 3 < t := lt_of_le_of_ne h3 (Ne.symm ht3)
      by_cases h4 : t < 4
      · have hd := (fdBoundary_H_hasDerivAt_seg4' H t ⟨h3', h4⟩)
        rw [show deriv (fdBoundaryH H) t = _ from hd.deriv]
        simp only [ne_eq, mul_eq_zero, sub_eq_zero, I_ne_zero, or_false]
        intro h; apply_fun Complex.re at h
        simp [ofReal_re] at h; linarith
      · push Not at h4
        have hd := (fdBoundary_H_hasDerivAt_seg5' H t
          ⟨lt_of_le_of_ne h4 (Ne.symm ht4), ht'.2⟩)
        rw [show deriv (fdBoundaryH H) t = _ from hd.deriv]
        exact one_ne_zero

lemma fdBoundary_H_deriv_continuousAt_off_fullPartition
    (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 5)
    (htp : t ∉ fdBoundaryFullPartition) :
    ContinuousAt (deriv (fdBoundaryH H)) t := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at htp
  push Not at htp; obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5⟩ := htp
  by_cases h1 : t < 1
  · apply ContinuousAt.congr (continuousAt_const (y := -(H - Real.sqrt 3 / 2) * I))
    filter_upwards [Ioo_mem_nhds ht.1 h1] with s hs
    exact (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv.symm
  · push Not at h1
    have h1' : 1 < t := lt_of_le_of_ne h1 (Ne.symm ht1)
    by_cases h3 : t < 3
    · have hderiv_eq : deriv (fdBoundaryH H) =ᶠ[𝓝 t]
          fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I) *
            (↑Real.pi / 6 * I) := by
        filter_upwards
          [(fdBoundary_H_eq_arc_near (H := H) h1' h3).deriv]
          with s hs
        exact hs ▸ (arc_hasDerivAt s).deriv
      exact (continuousAt_congr hderiv_eq).mpr
        arc_deriv_continuous.continuousAt
    · push Not at h3
      have h3' : 3 < t := lt_of_le_of_ne h3 (Ne.symm ht3)
      by_cases h4 : t < 4
      · apply ContinuousAt.congr (continuousAt_const (y := (H - Real.sqrt 3 / 2) * I))
        filter_upwards [Ioo_mem_nhds h3' h4] with s hs
        exact (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv.symm
      · push Not at h4
        have h4' : 4 < t := lt_of_le_of_ne h4 (Ne.symm ht4)
        apply ContinuousAt.congr (continuousAt_const (y := 1))
        filter_upwards [Ioo_mem_nhds h4' ht.2] with s hs
        exact (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv.symm

private lemma tendsto_of_eventually_const_left {c : ℂ} {p : ℝ}
    {f : ℝ → ℂ} {a : ℝ} (ha : a < p)
    (hf : ∀ s ∈ Ioo a p, f s = c) : Tendsto f (𝓝[<] p) (𝓝 c) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsLT ha] with s hs; exact (hf s hs).symm)

private lemma tendsto_of_eventually_const_right {c : ℂ} {p : ℝ}
    {f : ℝ → ℂ} {b : ℝ} (hb : p < b)
    (hf : ∀ s ∈ Ioo p b, f s = c) : Tendsto f (𝓝[>] p) (𝓝 c) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsGT hb] with s hs; exact (hf s hs).symm)

private lemma seg_vertical_deriv_ne_zero {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    (↑H - ↑(Real.sqrt 3) / 2) * I ≠ (0 : ℂ) := by
  apply mul_ne_zero _ I_ne_zero
  intro h; apply_fun Complex.re at h
  simp only [sub_re, ofReal_re, div_ofNat, zero_re] at h
  linarith

private lemma arc_tendsto_left {H : ℝ} (p : ℝ) (h1p : 1 < p) (hp3 : p ≤ 3) :
    Tendsto (deriv (fdBoundaryH H)) (𝓝[<] p) (𝓝 (exp ((↑Real.pi * (↑p + 1) / 6) * I) *
      (↑Real.pi / 6 * I))) := by
  set F := fun s : ℝ => exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I) with hF_def
  apply arc_deriv_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [Ioo_mem_nhdsLT h1p] with s hs
  have hs1 : 1 < s := hs.1
  have hs3 : s < 3 := lt_of_lt_of_le hs.2 hp3
  have heq := fdBoundary_H_eq_arc_near (H := H) hs1 hs3
  exact ((Filter.EventuallyEq.deriv_eq heq).trans (arc_hasDerivAt s).deriv).symm

private lemma arc_tendsto_right {H : ℝ} (p : ℝ) (hp1 : 1 ≤ p) (hp3 : p < 3) :
    Tendsto (deriv (fdBoundaryH H)) (𝓝[>] p) (𝓝 (exp ((↑Real.pi * (↑p + 1) / 6) * I) *
      (↑Real.pi / 6 * I))) := by
  set F := fun s : ℝ => exp ((↑Real.pi * (↑s + 1) / 6) * I) * (↑Real.pi / 6 * I) with hF_def
  apply arc_deriv_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [Ioo_mem_nhdsGT hp3] with s hs
  have hs1 : 1 < s := lt_of_le_of_lt hp1 hs.1
  have hs3 : s < 3 := hs.2
  have heq := fdBoundary_H_eq_arc_near (H := H) hs1 hs3
  exact ((Filter.EventuallyEq.deriv_eq heq).trans (arc_hasDerivAt s).deriv).symm

lemma fdBoundary_H_left_deriv_limit (H : ℝ)
    (hH : Real.sqrt 3 / 2 < H)
    (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hp' : (0 : ℝ) < p) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv (fdBoundaryH H)) (𝓝[<] p)
        (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · linarith
  · refine ⟨-(↑H - ↑(Real.sqrt 3) / 2) * I, ?_, ?_⟩
    · rw [neg_mul]; exact neg_ne_zero.mpr (seg_vertical_deriv_ne_zero hH)
    · exact tendsto_of_eventually_const_left (show (0 : ℝ) < 1 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv)
  · exact ⟨_, arc_limit_ne_zero 2, arc_tendsto_left 2 (by norm_num) (by norm_num)⟩
  · exact ⟨_, arc_limit_ne_zero 3, arc_tendsto_left 3 (by norm_num) (by norm_num)⟩
  · exact ⟨_, seg_vertical_deriv_ne_zero hH,
      tendsto_of_eventually_const_left (show (3 : ℝ) < 4 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv)⟩
  · exact ⟨1, one_ne_zero,
      tendsto_of_eventually_const_left (show (4 : ℝ) < 5 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv)⟩

lemma fdBoundary_H_hasDerivAt_seg1 (H : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fdBoundaryH H) (-(H - Real.sqrt 3 / 2) * I) t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t]
      fun s => (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [fdBoundaryH, show s ≤ 1 from le_of_lt hs, ite_true]
  have h1 : HasDerivAt (fun s : ℝ => (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
      (-(↑H - ↑(Real.sqrt 3) / 2) * I) t := by
    have h2 : HasDerivAt (fun s : ℝ => (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
        ((0 - 1 * (↑H - ↑(Real.sqrt 3) / 2)) * I) t := by
      apply HasDerivAt.mul_const
      exact (hasDerivAt_const t (↑H : ℂ)).sub ((hasDerivAt_id t).ofReal_comp.mul_const _)
    simp only [zero_sub, one_mul] at h2; exact h2
  have hd : HasDerivAt (fun s : ℝ =>
      (1 : ℂ) / 2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I)
      (-(↑H - ↑(Real.sqrt 3) / 2) * I) t := by
    exact h1.const_add ((1 : ℂ) / 2)
  exact hd.congr_of_eventuallyEq heq

lemma fdBoundary_H_hasDerivAt_seg4 (H : ℝ) {t : ℝ} (h3 : 3 < t) (h4 : t < 4) :
    HasDerivAt (fdBoundaryH H) ((H - Real.sqrt 3 / 2) * I) t :=
  fdBoundary_H_hasDerivAt_seg4' H t ⟨h3, h4⟩

lemma fdBoundary_H_hasDerivAt_seg5 (H : ℝ) {t : ℝ} (h4 : 4 < t) :
    HasDerivAt (fdBoundaryH H) 1 t := by
  have heq : fdBoundaryH H =ᶠ[𝓝 t] fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I := by
    filter_upwards [Ioi_mem_nhds h4] with s hs
    have hs4 : (4 : ℝ) < s := hs
    simp only [fdBoundaryH, show ¬s ≤ 1 from by linarith,
      show ¬s ≤ 2 from by linarith, show ¬s ≤ 3 from by linarith,
      show ¬s ≤ 4 from by linarith, ite_false]
  have h1 : HasDerivAt (fun s : ℝ => (↑s - 9/2 : ℂ)) (1 : ℂ) t := by
    have := ((hasDerivAt_id t).ofReal_comp).sub (hasDerivAt_const t (9/2 : ℂ))
    simp only [sub_zero, ofReal_one] at this; exact this
  have hd : HasDerivAt (fun s : ℝ => (↑s - 9/2 : ℂ) + ↑H * I) (1 : ℂ) t := by
    exact h1.add_const (↑H * I : ℂ)
  exact hd.congr_of_eventuallyEq heq

theorem continuous_fdBoundary_seg1_H (H : ℝ) :
    Continuous (fdBoundarySeg1H H) := by
  unfold fdBoundarySeg1H; fun_prop

theorem continuous_fdBoundary_seg4_H (H : ℝ) :
    Continuous (fdBoundarySeg4H H) := by
  unfold fdBoundarySeg4H; fun_prop

theorem continuous_fdBoundary_seg5_H (H : ℝ) :
    Continuous (fdBoundarySeg5H H) := by
  unfold fdBoundarySeg5H; fun_prop

lemma hasDerivAt_fdBoundary_seg1_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg1H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundarySeg1H H = fun s : ℝ =>
      ((1 : ℂ) / 2 + ↑H * I) + ↑s * (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundarySeg1H]; push_cast; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg4_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg4H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundarySeg4H H = fun s : ℝ =>
      ((-1 : ℂ) / 2 + ↑(Real.sqrt 3) / 2 * I) +
        ↑(s - 3) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundarySeg4H]; push_cast; ring
  rw [hfun]
  have h_sub : HasDerivAt (fun s : ℝ => (↑(s - 3) : ℂ)) 1 t := by
    have := ((hasDerivAt_id t).sub (hasDerivAt_const t (3 : ℝ))).ofReal_comp
    simp only [sub_zero, ofReal_one] at this; exact this
  exact (h_sub.mul_const _).const_add _ |>.congr_deriv (by push_cast; ring)

lemma hasDerivAt_fdBoundary_seg5_H (H t : ℝ) :
    HasDerivAt (fdBoundarySeg5H H) 1 t := by
  have hfun : fdBoundarySeg5H H = fun s : ℝ =>
      ((-9 / 2 : ℂ) + ↑H * I) + ↑s * (1 : ℂ) := by
    ext s; simp only [fdBoundarySeg5H]; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by norm_cast)

private lemma seg4_eventuallyEq_left_4 (H : ℝ) :
    fdBoundarySeg4H H =ᶠ[𝓝[≤] 4] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 3 5 ∩ Iic 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  rcases eq_or_lt_of_le (show s ≤ 4 from hs.2) with rfl | h
  · simp only [fdBoundarySeg4H, fdBoundary_H_at_four]; push_cast; ring
  · exact (fdBoundary_H_eq_seg4_H (by linarith [hs.1.1]) (le_of_lt h)).symm

private lemma seg5_eventuallyEq_right_4 (H : ℝ) :
    fdBoundarySeg5H H =ᶠ[𝓝[≥] 4] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 3 5 ∩ Ici 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ici : (4 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ici with rfl | h
  · simp only [fdBoundarySeg5H, fdBoundary_H_at_four]; push_cast; ring
  · exact (fdBoundary_H_eq_seg5_H h).symm

lemma fdBoundary_H_not_differentiableAt_4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundaryH H) 4 := by
  intro hdiff
  have hleft : HasDerivWithinAt (fdBoundaryH H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Iic 4) 4 :=
    ((seg4_eventuallyEq_left_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundarySeg4H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg4_H H 4).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundaryH H) 1 (Ici 4) 4 :=
    ((seg5_eventuallyEq_right_4 H).hasDerivWithinAt_iff (by
      simp only [fdBoundarySeg5H, fdBoundary_H_at_four]; push_cast; ring)).mp
      (hasDerivAt_fdBoundary_seg5_H H 4).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have him := congr_arg Complex.im
    (((uniqueDiffWithinAt_Iic (4 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (4 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm)
  simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, one_im] at him
  linarith [sub_pos.mpr hH]

private lemma arc_eventuallyEq_left_3 (H : ℝ) :
    (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≤] 3] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 2 4 ∩ Iic 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs1 : 1 < s := by linarith [hs.1.1]
  have hs3 : s ≤ 3 := hs.2
  rcases eq_or_lt_of_le hs3 with rfl | hs3'
  · rw [show fdBoundaryH H 3 = fdBoundary 3 from
      (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm]
    simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
      show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_rfl]
    congr 1; push_cast; ring
  · exact (fdBoundary_H_eq_arc_near hs1 hs3').symm.eq_of_nhds

private lemma seg4_eventuallyEq_right_3 (H : ℝ) :
    fdBoundarySeg4H H =ᶠ[𝓝[≥] 3] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 2 4 ∩ Ici 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ici : (3 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ici with rfl | h
  · rw [show fdBoundaryH H 3 = fdBoundary 3 from
      (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm, fdBoundary_at_three]
    simp only [fdBoundarySeg4H, ellipticPointRho, ellipticPointRho',
      UpperHalfPlane.coe_mk]; push_cast; ring
  · exact (fdBoundary_H_eq_seg4_H h (by linarith [hs.1.2])).symm

lemma fdBoundary_H_not_differentiableAt_3 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundaryH H) 3 := by
  intro hdiff
  have hval_arc : (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) 3 = fdBoundaryH H 3 := by
    rw [show fdBoundaryH H 3 = fdBoundary 3 from
      (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm]
    simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
      show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_rfl]
    congr 1; push_cast; ring
  have hval_seg4 : fdBoundarySeg4H H 3 = fdBoundaryH H 3 := by
    rw [show fdBoundaryH H 3 = fdBoundary 3 from
      (fdBoundary_H_at_three H).trans fdBoundary_at_three.symm, fdBoundary_at_three]
    simp only [fdBoundarySeg4H, ellipticPointRho, ellipticPointRho',
      UpperHalfPlane.coe_mk]; push_cast; ring
  have hleft : HasDerivWithinAt (fdBoundaryH H)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * 4 / 6) * I)) (Iic 3) 3 :=
    ((arc_eventuallyEq_left_3 H).hasDerivWithinAt_iff hval_arc).mp
      ((arc_hasDerivAt 3).hasDerivWithinAt.congr_deriv (by
        have h1 : (↑Real.pi * (↑(3 : ℝ) + 1) / 6 : ℂ) * I = ↑(Real.pi * 4 / 6) * I := by
          congr 1; push_cast; ring
        have h2 : (↑Real.pi / 6 : ℂ) = ↑(Real.pi / 6) := by push_cast; ring
        rw [h1, h2]; ring))
  have hright : HasDerivWithinAt (fdBoundaryH H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Ici 3) 3 :=
    ((seg4_eventuallyEq_right_3 H).hasDerivWithinAt_iff hval_seg4).mp
      (hasDerivAt_fdBoundary_seg4_H H 3).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have eq1 := (uniqueDiffWithinAt_Iic (3 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt
  have eq2 := (uniqueDiffWithinAt_Ici (3 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt
  have heq : ↑(Real.pi / 6) * I * exp (↑(Real.pi * 4 / 6) * I) =
      (↑(H - Real.sqrt 3 / 2) : ℂ) * I := eq1.trans eq2.symm
  have hre := congr_arg Complex.re heq
  have hre_rhs : ((↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by simp [mul_re]
  have hre_lhs : (↑(Real.pi / 6) * I * exp (↑(Real.pi * 4 / 6) * I)).re =
      -(Real.pi / 6) * Real.sin (Real.pi * 4 / 6) := by
    rw [mul_assoc, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      I_mul_re, exp_ofReal_mul_I_im]; ring
  rw [hre_lhs, hre_rhs] at hre
  have hsin : Real.sin (Real.pi * 4 / 6) = Real.sqrt 3 / 2 := by
    rw [show Real.pi * 4 / 6 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hsin] at hre
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 from by norm_num)]

private lemma seg1_eventuallyEq_left_1 (H : ℝ) :
    fdBoundarySeg1H H =ᶠ[𝓝[≤] 1] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  exact ⟨Ioo 0 2 ∩ Iic 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin,
    fun s hs => (fdBoundary_H_eq_seg1_H hs.2).symm⟩

private lemma arc_eventuallyEq_right_1 (H : ℝ) :
    (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) =ᶠ[𝓝[≥] 1] fdBoundaryH H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Ioo 0 2 ∩ Ici 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ici : (1 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ici with rfl | hs1
  · simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_rfl, ite_true]
    have harg : (↑Real.pi * (↑(1 : ℝ) + 1) / 6) * I = ↑(Real.pi / 3 : ℝ) * I := by
      push_cast; ring
    rw [harg, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  · exact (fdBoundary_H_eq_arc_near hs1 (by linarith [hs.1.2])).symm.eq_of_nhds

lemma fdBoundary_H_not_differentiableAt_1 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundaryH H) 1 := by
  intro hdiff
  have hval_seg1 : fdBoundarySeg1H H 1 = fdBoundaryH H 1 :=
    (fdBoundary_H_eq_seg1_H le_rfl).symm
  have hval_arc : (fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I)) 1 = fdBoundaryH H 1 := by
    dsimp only
    have harg : (↑Real.pi * ((1 : ℂ) + 1) / 6) * I = ↑(Real.pi / 3 : ℝ) * I := by
      push_cast; ring
    rw [harg, exp_mul_I]
    simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_rfl, ite_true]
    rw [← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hleft : HasDerivWithinAt (fdBoundaryH H)
      (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Iic 1) 1 :=
    ((seg1_eventuallyEq_left_1 H).hasDerivWithinAt_iff hval_seg1).mp
      (hasDerivAt_fdBoundary_seg1_H H 1).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundaryH H)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * 2 / 6) * I)) (Ici 1) 1 :=
    ((arc_eventuallyEq_right_1 H).hasDerivWithinAt_iff hval_arc).mp
      ((arc_hasDerivAt 1).hasDerivWithinAt.congr_deriv (by
        have h1 : (↑Real.pi * (↑(1 : ℝ) + 1) / 6) * I = ↑(Real.pi * 2 / 6) * I := by
          congr 1; push_cast; ring
        have h2 : (↑Real.pi / 6 : ℂ) = ↑(Real.pi / 6) := by push_cast; ring
        rw [h1, h2]; ring))
  have hd := hdiff.hasDerivAt
  have heq : -(↑(H - Real.sqrt 3 / 2) : ℂ) * I =
      ↑(Real.pi / 6) * I * exp (↑(Real.pi * 2 / 6) * I) :=
    ((uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt).trans
      ((uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt).symm
  have hre := congr_arg Complex.re heq
  have hre_lhs : (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by simp [mul_re]
  have hre_rhs : (↑(Real.pi / 6) * I * exp (↑(Real.pi * 2 / 6) * I)).re =
      -(Real.pi / 6) * Real.sin (Real.pi * 2 / 6) := by
    rw [mul_assoc, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      I_mul_re, exp_ofReal_mul_I_im]; ring
  rw [hre_lhs, hre_rhs] at hre
  rw [show Real.pi * 2 / 6 = Real.pi / 3 from by ring] at hre
  rw [Real.sin_pi_div_three] at hre
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 from by norm_num)]

lemma fdBoundary_H_right_deriv_limit (H : ℝ)
    (hH : Real.sqrt 3 / 2 < H)
    (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hp' : p < (5 : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv (fdBoundaryH H)) (𝓝[>] p)
        (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨-(↑H - ↑(Real.sqrt 3) / 2) * I, ?_, ?_⟩
    · rw [neg_mul]; exact neg_ne_zero.mpr (seg_vertical_deriv_ne_zero hH)
    · exact tendsto_of_eventually_const_right (show (0 : ℝ) < 1 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg1' H s hs).deriv)
  · exact ⟨_, arc_limit_ne_zero 1, arc_tendsto_right 1 (by norm_num) (by norm_num)⟩
  · exact ⟨_, arc_limit_ne_zero 2, arc_tendsto_right 2 (by norm_num) (by norm_num)⟩
  · exact ⟨_, seg_vertical_deriv_ne_zero hH,
      tendsto_of_eventually_const_right (show (3 : ℝ) < 4 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg4' H s hs).deriv)⟩
  · exact ⟨1, one_ne_zero,
      tendsto_of_eventually_const_right (show (4 : ℝ) < 5 from by norm_num)
        (fun s hs => (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv)⟩
  · linarith

/-- The H-parameterized boundary as a `PiecewiseC1Curve`. -/
noncomputable def fdBoundaryHCurve (H : ℝ) :
    PiecewiseC1Curve where
  toFun := fdBoundaryH H
  a := 0
  b := 5
  hab := by norm_num
  partition := fdBoundaryFullPartition
  partition_subset := by
    intro x hx
    simp only [fdBoundaryFullPartition, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff] at hx
    simp only [Icc, Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> norm_num
  endpoints_in_partition := by
    constructor
    · simp [fdBoundaryFullPartition]
    · simp [fdBoundaryFullPartition]
  continuous_toFun := (fdBoundary_H_continuous H).continuousOn
  smooth_off_partition := by
    intro t ht htp
    have htP : t ∉ fdBoundaryHPartition := by
      simp only [fdBoundaryHPartition, fdBoundaryFullPartition, Finset.mem_insert,
        Finset.mem_singleton] at htp ⊢
      push Not at htp ⊢; exact ⟨htp.2.1, htp.2.2.2.1, htp.2.2.2.2.1⟩
    exact fdBoundary_H_differentiableAt_off_partition H t htP
  deriv_continuous_off_partition := by
    intro t ht htp
    exact fdBoundary_H_deriv_continuousAt_off_fullPartition H t ht htp

/-- The H-parameterized boundary as a `PiecewiseC1Immersion`.
Requires H > √3/2 for nonzero derivative. -/
noncomputable def fdBoundaryHImmersion (H : ℝ)
    (hH : Real.sqrt 3 / 2 < H) :
    PiecewiseC1Immersion where
  toPiecewiseC1Curve := fdBoundaryHCurve H
  deriv_ne_zero := by
    intro t ht htp
    exact fdBoundary_H_deriv_ne_zero_off_fullPartition H hH t ht htp
  left_deriv_limit := by
    intro p hp hp'
    exact fdBoundary_H_left_deriv_limit H hH p hp hp'
  right_deriv_limit := by
    intro p hp hp'
    exact fdBoundary_H_right_deriv_limit H hH p hp hp'

lemma fdBoundary_HCurve_closed (H : ℝ) :
    (fdBoundaryHCurve H).IsClosed := by
  change fdBoundaryH H 0 = fdBoundaryH H 5
  exact fdBoundary_H_closed H

lemma fdBoundary_differentiableAt_off_partition
    (t : ℝ) (htp : t ∉ fdPartition) :
    DifferentiableAt ℝ fdBoundary t := by
  rw [fdBoundary_eq_fdBoundary_H]
  apply fdBoundary_H_differentiableAt_off_partition heightCutoff t
  simp only [fdBoundaryHPartition, fdPartition,
    Finset.mem_insert, Finset.mem_singleton] at htp ⊢
  push Not at htp ⊢; exact ⟨htp.1, htp.2.2.1, htp.2.2.2⟩

lemma fdBoundary_deriv_continuousAt_off_partition
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 5)
    (htp : t ∉ fdBoundaryFullPartition) :
    ContinuousAt (deriv fdBoundary) t := by
  rw [show deriv fdBoundary = deriv (fdBoundaryH heightCutoff) from
    congr_arg deriv fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_deriv_continuousAt_off_fullPartition heightCutoff t ht htp

lemma fdBoundary_deriv_ne_zero_off_partition
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 5)
    (htp : t ∉ fdBoundaryFullPartition) :
    deriv fdBoundary t ≠ 0 := by
  rw [show deriv fdBoundary = deriv (fdBoundaryH heightCutoff) from
    congr_arg deriv fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_deriv_ne_zero_off_fullPartition heightCutoff sqrt3_div2_lt_heightCutoff
    t ht htp

lemma fdBoundary_left_deriv_limit
    (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hp' : (0 : ℝ) < p) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv fdBoundary) (𝓝[<] p) (𝓝 L) := by
  rw [show deriv fdBoundary = deriv (fdBoundaryH heightCutoff) from
    congr_arg deriv fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_left_deriv_limit heightCutoff sqrt3_div2_lt_heightCutoff p hp hp'

lemma fdBoundary_right_deriv_limit
    (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hp' : p < (5 : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv fdBoundary) (𝓝[>] p) (𝓝 L) := by
  rw [show deriv fdBoundary = deriv (fdBoundaryH heightCutoff) from
    congr_arg deriv fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_right_deriv_limit heightCutoff sqrt3_div2_lt_heightCutoff p hp hp'

/-- The boundary of the fundamental domain as a `PiecewiseC1Curve`. -/
noncomputable def fdBoundaryCurve : PiecewiseC1Curve where
  toFun := fdBoundary
  a := 0
  b := 5
  hab := by norm_num
  partition := fdBoundaryFullPartition
  partition_subset := by
    intro x hx
    simp only [fdBoundaryFullPartition, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff] at hx
    simp only [Icc, Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> norm_num
  endpoints_in_partition := by
    constructor
    · simp [fdBoundaryFullPartition]
    · simp [fdBoundaryFullPartition]
  continuous_toFun := fdBoundary_continuous.continuousOn
  smooth_off_partition := by
    intro t ht htp
    have ht0 : t ≠ 0 := fun h => htp (h ▸ by simp [fdBoundaryFullPartition])
    have ht5 : t ≠ 5 := fun h => htp (h ▸ by simp [fdBoundaryFullPartition])
    have htoo : t ∈ Ioo (0 : ℝ) 5 := by
      simp only [mem_Icc] at ht
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht5⟩
    have htP : t ∉ fdPartition := by
      simp only [fdPartition, fdBoundaryFullPartition,
        Finset.mem_insert, Finset.mem_singleton] at htp ⊢
      push Not at htp ⊢; exact ⟨htp.2.1, htp.2.2.1, htp.2.2.2.1, htp.2.2.2.2.1⟩
    exact fdBoundary_differentiableAt_off_partition t htP
  deriv_continuous_off_partition := by
    intro t ht htp
    exact fdBoundary_deriv_continuousAt_off_partition t ht htp

/-- The boundary of the fundamental domain as a
`PiecewiseC1Immersion`. -/
noncomputable def fdBoundaryImmersion : PiecewiseC1Immersion where
  toPiecewiseC1Curve := fdBoundaryCurve
  deriv_ne_zero := by
    intro t ht htp
    exact fdBoundary_deriv_ne_zero_off_partition t ht htp
  left_deriv_limit := by
    intro p hp hp'
    exact fdBoundary_left_deriv_limit p hp hp'
  right_deriv_limit := by
    intro p hp hp'
    exact fdBoundary_right_deriv_limit p hp hp'

lemma fdBoundaryImmersion_closed :
    fdBoundaryCurve.IsClosed := by
  change fdBoundary 0 = fdBoundary 5
  exact fdBoundary_closed

lemma fdBoundary_H_hasDerivAt_arc (H : ℝ) {t : ℝ}
    (h1 : 1 < t) (h3 : t < 3) :
    HasDerivAt (fdBoundaryH H)
      (exp ((↑Real.pi * (↑t + 1) / 6) * I) *
        (↑Real.pi / 6 * I)) t :=
  (arc_hasDerivAt t).congr_of_eventuallyEq
    (fdBoundary_H_eq_arc_near (H := H) h1 h3)

lemma fdBoundary_H_deriv_continuousOn_Ioo_01 (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H)) (Ioo 0 1) := by
  intro t ⟨h0, h1⟩
  exact (fdBoundary_H_deriv_continuousAt_off_fullPartition
    H t ⟨h0, by linarith⟩ (by
      simp only [fdBoundaryFullPartition,
        Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    )).continuousWithinAt

lemma fdBoundary_H_deriv_continuousOn_Ioo_13 (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H)) (Ioo 1 3) := by
  intro t ht
  have hderiv_eq : deriv (fdBoundaryH H) =ᶠ[𝓝 t]
      fun s => exp ((↑Real.pi * (↑s + 1) / 6) * I) *
        (↑Real.pi / 6 * I) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (Filter.EventuallyEq.deriv_eq
      (fdBoundary_H_eq_arc_near (H := H) hs.1 hs.2)).trans
      (arc_hasDerivAt s).deriv
  exact (continuousAt_congr hderiv_eq).mpr
    arc_deriv_continuous.continuousAt |>.continuousWithinAt

lemma fdBoundary_H_deriv_continuousOn_Ioo_34 (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H)) (Ioo 3 4) := by
  intro t ht
  have h3 : 3 < t := ht.1
  have h4 : t < 4 := ht.2
  exact (fdBoundary_H_deriv_continuousAt_off_fullPartition
    H t ⟨by linarith, by linarith⟩ (by
      simp only [fdBoundaryFullPartition,
        Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    )).continuousWithinAt

lemma fdBoundary_H_deriv_continuousOn_Ioo_45 (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H)) (Ioo 4 5) := by
  intro t ht
  have : deriv (fdBoundaryH H) =ᶠ[𝓝 t]
      fun _ => (1 : ℂ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (fdBoundary_H_hasDerivAt_seg5' H s hs).deriv
  exact this.continuousAt.continuousWithinAt

private lemma norm_cast_sub_eq {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ‖(↑H - ↑(Real.sqrt 3) / 2 : ℂ)‖ = H - Real.sqrt 3 / 2 := by
  have hcast : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑(H - Real.sqrt 3 / 2) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

lemma fdBoundary_H_deriv_bound_ex {H : ℝ}
    (hH : Real.sqrt 3 / 2 < H) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      t ∉ fdBoundaryHPartition →
        ‖deriv (fdBoundaryH H) t‖ ≤ M := by
  refine ⟨max (H - Real.sqrt 3 / 2) 1,
    lt_max_of_lt_right one_pos, fun t ht => ?_⟩
  simp only [fdBoundaryHPartition, Finset.mem_insert,
    Finset.mem_singleton] at ht
  push Not at ht; obtain ⟨h1, h3, h4⟩ := ht
  by_cases ht1 : t < 1
  · rw [show deriv (fdBoundaryH H) t = _ from (fdBoundary_H_hasDerivAt_seg1 H ht1).deriv,
      neg_mul, norm_neg, norm_mul, Complex.norm_I, mul_one,
      norm_cast_sub_eq hH]
    exact le_max_left _ _
  · push Not at ht1
    by_cases ht3 : t < 3
    · rw [show deriv (fdBoundaryH H) t = _ from (fdBoundary_H_hasDerivAt_arc H
          (lt_of_le_of_ne ht1 (Ne.symm h1)) ht3).deriv]
      simp only [norm_mul, Complex.norm_I, mul_one]
      have hexp : ‖exp ((↑Real.pi * (↑t + 1) / 6) * I)‖ = 1 := by
        rw [show (↑Real.pi * (↑t + 1) / 6 : ℂ) * I =
          ↑(Real.pi * (t + 1) / 6) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hexp, one_mul]
      have hpi : ‖(↑Real.pi / 6 : ℂ)‖ = Real.pi / 6 := by
        rw [show (↑Real.pi / 6 : ℂ) = ↑(Real.pi / 6) from by
          push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hpi]
      exact le_max_of_le_right (by linarith [Real.pi_le_four])
    · push Not at ht3
      by_cases ht4 : t < 4
      · rw [show deriv (fdBoundaryH H) t = _ from (fdBoundary_H_hasDerivAt_seg4 H
            (lt_of_le_of_ne ht3 (Ne.symm h3)) ht4).deriv,
          norm_mul, Complex.norm_I, mul_one,
          norm_cast_sub_eq hH]
        exact le_max_left _ _
      · push Not at ht4
        rw [show deriv (fdBoundaryH H) t = _ from (fdBoundary_H_hasDerivAt_seg5 H
            (lt_of_le_of_ne ht4 (Ne.symm h4))).deriv,
          norm_one]
        exact le_max_right _ _

lemma fdBoundary_H_deriv_continuousOn_off_partition
    (H : ℝ) :
    ContinuousOn (deriv (fdBoundaryH H))
      (Icc 0 5 \ ↑fdBoundaryHPartition) := by
  intro t ht
  have ht_icc := ht.1
  have ht_part : t ∉ (fdBoundaryHPartition : Set ℝ) := ht.2
  simp only [fdBoundaryHPartition, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff, not_or] at ht_part
  obtain ⟨h1, h3, h4⟩ := ht_part
  by_cases ht0 : t = 0
  · subst ht0
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.congr (continuousAt_const (y := -(H - Real.sqrt 3 / 2) * I))
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 from by norm_num)]
      with s hs
    exact (fdBoundary_H_hasDerivAt_seg1 H hs).deriv.symm
  by_cases ht5 : t = 5
  · subst ht5
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.congr (continuousAt_const (y := 1))
    filter_upwards [Ioi_mem_nhds (show (4 : ℝ) < 5 from by norm_num)]
      with s hs
    exact (fdBoundary_H_hasDerivAt_seg5 H hs).deriv.symm
  have ht_ioo : t ∈ Ioo (0 : ℝ) 5 :=
    ⟨lt_of_le_of_ne ht_icc.1 (Ne.symm ht0),
     lt_of_le_of_ne ht_icc.2 ht5⟩
  by_cases ht1 : t < 1
  · exact ((fdBoundary_H_deriv_continuousOn_Ioo_01 H).continuousAt
      (Ioo_mem_nhds ht_ioo.1 ht1)).continuousWithinAt
  · push Not at ht1
    by_cases ht3' : t < 3
    · exact ((fdBoundary_H_deriv_continuousOn_Ioo_13 H).continuousAt
        (Ioo_mem_nhds (lt_of_le_of_ne ht1 (fun h => h1 h.symm))
          ht3')).continuousWithinAt
    · push Not at ht3'
      by_cases ht4' : t < 4
      · exact ((fdBoundary_H_deriv_continuousOn_Ioo_34 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht3' (fun h => h3 h.symm))
            ht4')).continuousWithinAt
      · push Not at ht4'
        exact ((fdBoundary_H_deriv_continuousOn_Ioo_45 H).continuousAt
          (Ioo_mem_nhds (lt_of_le_of_ne ht4' (fun h => h4 h.symm))
            ht_ioo.2)).continuousWithinAt

end
