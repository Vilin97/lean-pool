/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Pointwise bounds and support for normalized mollifications

Elementary stability properties of the normalized `ContDiffBump` mollification used
throughout the Caffarelli–Kohn–Nirenberg argument.

* `abs_mollify_le`: a uniform pointwise bound is preserved by mollification.
* `support_mollify_subset`: mollification does not spread the support of a function
  beyond the closed `ε`-neighbourhood of its topological support.
-/

public section

open MeasureTheory Metric

namespace CKN


noncomputable section

/-- The normalized mollification is the convolution against the scalar kernel, hence an integral
of `mollifier ε hε t * u (x - t)` over `t`. -/
private theorem mollify_eq_integral {d : ℕ} (u : Vec d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : Vec d) :
    mollify u ε hε x =
      ∫ t, mollifier (d := d) ε hε t * u (x - t) ∂MeasureTheory.volume := by
  simp only [mollify, MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- **Pointwise bound for a mollification.** If `u` is continuous and bounded above in absolute
value by `M`, then its normalized mollification at scale `ε` obeys the same bound at every point:
`|mollify u ε hε x| ≤ M`. This is the elementary bound under the Caffarelli–Kohn–Nirenberg
normalized kernel used in the slice-distribution estimates. -/
theorem abs_mollify_le {d : ℕ} {u : Vec d → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : ∀ x : Vec d, |u x| ≤ M) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    |mollify u ε hε x| ≤ M := by
  have hk_cont : Continuous (mollifier (d := d) ε hε) :=
    (mollifier_contDiff (d := d) hε (n := 0)).continuous
  have huc : Continuous fun t : Vec d => u (x - t) :=
    hu.comp (continuous_const.sub continuous_id)
  have hk_int : Integrable (mollifier (d := d) ε hε) MeasureTheory.volume :=
    hk_cont.integrable_of_hasCompactSupport (mollifier_hasCompactSupport (d := d) hε)
  have h_int : Integrable (fun t : Vec d => mollifier (d := d) ε hε t * u (x - t))
      MeasureTheory.volume :=
    (hk_cont.mul huc).integrable_of_hasCompactSupport
      ((mollifier_hasCompactSupport (d := d) hε).mul_right)
  have h_bound : Integrable (fun t : Vec d => mollifier (d := d) ε hε t * M)
      MeasureTheory.volume :=
    hk_int.mul_const M
  have h_abs_int : Integrable (fun t : Vec d => mollifier (d := d) ε hε t * |u (x - t)|)
      MeasureTheory.volume := by
    refine h_int.norm.congr ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg hε t)]
  have h_main :
      ‖∫ t, mollifier (d := d) ε hε t * u (x - t) ∂MeasureTheory.volume‖ ≤ M := by
    calc
      ‖∫ t, mollifier (d := d) ε hε t * u (x - t) ∂MeasureTheory.volume‖
          ≤ ∫ t, ‖mollifier (d := d) ε hε t * u (x - t)‖ ∂MeasureTheory.volume :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t, mollifier (d := d) ε hε t * |u (x - t)| ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with t
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg hε t)]
      _ ≤ ∫ t, mollifier (d := d) ε hε t * M ∂MeasureTheory.volume :=
            MeasureTheory.integral_mono h_abs_int h_bound
              (fun t => mul_le_mul_of_nonneg_left (hM (x - t)) (mollifier_nonneg hε t))
      _ = (∫ t, mollifier (d := d) ε hε t ∂MeasureTheory.volume) * M :=
            MeasureTheory.integral_mul_const M _
      _ = M := by rw [mollifier_integral_one (d := d) hε, one_mul]
  rw [mollify_eq_integral u hε x, ← Real.norm_eq_abs]
  exact h_main

/-- **Support of a mollification.** The support of `mollify u ε hε` is contained in the closed
`ε`-neighbourhood of the topological support of `u`: outside `cthickening ε (tsupport u)` the
mollification vanishes, because the Caffarelli–Kohn–Nirenberg kernel only sees the values of `u`
on the radius-`ε` ball around the point. -/
theorem support_mollify_subset {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollify u ε hε) ⊆ Metric.cthickening ε (tsupport u) := by
  intro x hx
  have hx_ne : mollify u ε hε x ≠ 0 := Function.mem_support.mp hx
  have h_exists : ∃ t, mollifier (d := d) ε hε t * u (x - t) ≠ 0 := by
    by_contra h
    refine hx_ne ?_
    have h_zero : (fun t : Vec d => mollifier (d := d) ε hε t * u (x - t)) = fun _ => 0 := by
      funext t
      by_contra ht
      exact h ⟨t, ht⟩
    rw [mollify_eq_integral u hε x, h_zero, MeasureTheory.integral_zero]
  obtain ⟨t, ht⟩ := h_exists
  have hk_ne : mollifier (d := d) ε hε t ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
  have hu_ne : u (x - t) ≠ 0 := fun h0 => ht (by rw [h0, mul_zero])
  have ht_ball : t ∈ Metric.closedBall (0 : Vec d) ε := by
    have h_mem : t ∈ tsupport (mollifier (d := d) ε hε) :=
      subset_tsupport _ (Function.mem_support.mpr hk_ne)
    have h_eq : tsupport (mollifier (d := d) ε hε) = Metric.closedBall (0 : Vec d) ε := by
      simpa only [mollifier, standardMollifier] using
        (standardMollifier (d := d) ε hε).tsupport_normed_eq (μ := MeasureTheory.volume)
    rwa [h_eq] at h_mem
  have ht_norm : ‖t‖ ≤ ε := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using ht_ball
  have hx_tsupp : x - t ∈ tsupport u :=
    subset_tsupport u (Function.mem_support.mpr hu_ne)
  exact Metric.mem_cthickening_of_dist_le x (x - t) ε (tsupport u) hx_tsupp
    (by simpa [dist_eq_norm, sub_sub_cancel] using ht_norm)

end

end CKN
