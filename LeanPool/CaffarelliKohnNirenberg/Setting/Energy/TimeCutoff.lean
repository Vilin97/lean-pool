/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time Cutoff

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology


noncomputable section

namespace CKN

/-- A smooth backward cutoff with its transition confined to a time interval. -/
def backwardTimeCutoff (t h s : ℝ) : ℝ :=
  1 - smoothTransitionProfile ((s - (t - h / 2)) / (h / 2))

theorem backwardTimeCutoff_smooth {t h : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (backwardTimeCutoff t h) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (s - (t - h / 2)) / (h / 2)) := by
    exact ((contDiff_id.sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ℝ => t - h / 2))).div_const (h / 2))
  unfold backwardTimeCutoff
  apply contDiff_const.sub
  exact smoothTransitionProfile.smooth.comp harg

theorem backwardTimeCutoff_nonneg {t h s : ℝ} :
    0 ≤ backwardTimeCutoff t h s := by
  unfold backwardTimeCutoff
  linarith only [smoothTransitionProfile.le_one
    ((s - (t - h / 2)) / (h / 2))]

theorem backwardTimeCutoff_le_one {t h s : ℝ} :
    backwardTimeCutoff t h s ≤ 1 := by
  unfold backwardTimeCutoff
  linarith only [smoothTransitionProfile.nonneg
    ((s - (t - h / 2)) / (h / 2))]

theorem backwardTimeCutoff_eq_one_of_le {t h s : ℝ} (hh : 0 < h)
    (hs : s ≤ t - h) : backwardTimeCutoff t h s = 1 := by
  unfold backwardTimeCutoff
  rw [smoothTransitionProfile.zero_of_nonpos]
  · norm_num
  · apply (div_nonpos_iff).2
    right
    exact ⟨by linarith only [hs, hh], by positivity⟩

theorem backwardTimeCutoff_eq_zero_of_ge {t h s : ℝ} (hh : 0 < h)
    (hs : t ≤ s) : backwardTimeCutoff t h s = 0 := by
  unfold backwardTimeCutoff
  rw [smoothTransitionProfile.one_of_one_le]
  · norm_num
  · apply (le_div_iff₀ (by positivity)).2
    linarith only [hs, hh]

private theorem backwardTimeCutoff_hasDerivAt {t h s : ℝ} :
    HasDerivAt (backwardTimeCutoff t h)
      (-deriv smoothTransitionProfile
          ((s - (t - h / 2)) / (h / 2)) / (h / 2)) s := by
  have hprofile :=
    (smoothTransitionProfile.smooth.differentiable (by simp)
      ((s - (t - h / 2)) / (h / 2))).hasDerivAt
  have harg := ((hasDerivAt_id s).sub_const (t - h / 2)).div_const (h / 2)
  unfold backwardTimeCutoff
  convert (hasDerivAt_const s 1).sub (hprofile.comp s harg) using 1
  · funext x
    congr 1
  · ring

theorem backwardTimeCutoff_deriv_nonpos {t h s : ℝ} (hh : 0 < h) :
    deriv (backwardTimeCutoff t h) s ≤ 0 := by
  rw [(backwardTimeCutoff_hasDerivAt).deriv]
  have hnon : 0 ≤ deriv smoothTransitionProfile
      ((s - (t - h / 2)) / (h / 2)) := by
    simpa only [smoothTransitionProfile] using
      (Real.smoothTransition.monotone.deriv_nonneg
        (x := (s - (t - h / 2)) / (h / 2)))
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg hnon (by positivity : 0 ≤ h / 2))

theorem backwardTimeCutoff_abs_deriv_le {t h s : ℝ} (hh : 0 < h) :
    |deriv (backwardTimeCutoff t h) s| ≤ 16 / h := by
  rw [(backwardTimeCutoff_hasDerivAt).deriv, neg_div, abs_neg, abs_div,
    abs_of_pos (by positivity : 0 < h / 2)]
  calc
    |deriv smoothTransitionProfile
          ((s - (t - h / 2)) / (h / 2))| / (h / 2) ≤
        8 / (h / 2) :=
      div_le_div_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _) (by positivity)
    _ = 16 / h := by field_simp [ne_of_gt hh]; ring

theorem backwardTimeCutoff_integral_deriv {t h : ℝ} (hh : 0 < h) :
    ∫ s in t - h..t, deriv (backwardTimeCutoff t h) s = -1 := by
  have hfund := intervalIntegral.integral_deriv_eq_sub
    (f := backwardTimeCutoff t h) (a := t - h) (b := t)
    (fun s hs => (backwardTimeCutoff_smooth (t := t) (h := h)).differentiable
      (by simp) s)
    (by
      have hcont : Continuous (deriv (backwardTimeCutoff t h)) :=
        (backwardTimeCutoff_smooth (t := t) (h := h)).continuous_deriv (by simp)
      exact hcont.intervalIntegrable _ _)
  rw [backwardTimeCutoff_eq_zero_of_ge hh le_rfl,
    backwardTimeCutoff_eq_one_of_le hh le_rfl] at hfund
  simpa using hfund

private lemma backwardTimeCutoff_deriv_eq_zero_of_lt {t h s : ℝ}
    (hh : 0 < h) (hs : s < t - h) :
    deriv (backwardTimeCutoff t h) s = 0 := by
  have hev : backwardTimeCutoff t h =ᶠ[𝓝 s] (fun _ : ℝ => 1) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact backwardTimeCutoff_eq_one_of_le hh (le_of_lt hy)
  exact (hasDerivAt_const s 1).congr_of_eventuallyEq hev |>.deriv

private lemma backwardTimeCutoff_deriv_eq_zero_of_gt {t h s : ℝ}
    (hh : 0 < h) (hs : t < s) :
    deriv (backwardTimeCutoff t h) s = 0 := by
  have hev : backwardTimeCutoff t h =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
    filter_upwards [Ici_mem_nhds hs] with y hy
    exact backwardTimeCutoff_eq_zero_of_ge hh hy
  exact (hasDerivAt_const s 0).congr_of_eventuallyEq hev |>.deriv

theorem backwardTimeCutoff_kernel_support {t h : ℝ} (hh : 0 < h) :
    Function.support (fun s => -deriv (backwardTimeCutoff t h) s) ⊆ Icc (t - h) t := by
  intro s hs
  by_contra hnot
  have houtside : s < t - h ∨ t < s := by
    simpa only [mem_Icc, not_and_or, not_le] using hnot
  rcases houtside with hleft | hright
  · exact (Function.mem_support.mpr hs)
      (by rw [neg_eq_zero, backwardTimeCutoff_deriv_eq_zero_of_lt hh hleft])
  · exact (Function.mem_support.mpr hs)
      (by rw [neg_eq_zero,
        backwardTimeCutoff_deriv_eq_zero_of_gt (t := t) (h := h) (s := s) hh hright])

theorem backwardTimeCutoff_kernel_integral {t h : ℝ} (hh : 0 < h) :
    ∫ s, -deriv (backwardTimeCutoff t h) s = 1 := by
  have hsupp := backwardTimeCutoff_kernel_support (t := t) (h := h) hh
  have hind : (Icc (t - h) t).indicator
      (fun s => -deriv (backwardTimeCutoff t h) s) =
      (fun s => -deriv (backwardTimeCutoff t h) s) :=
    indicator_eq_self.2 hsupp
  rw [← hind, integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (a := t - h) (b := t)
    (by linarith only [hh])]
  rw [intervalIntegral.integral_neg,
    backwardTimeCutoff_integral_deriv (t := t) (h := h) hh]
  norm_num

end CKN
