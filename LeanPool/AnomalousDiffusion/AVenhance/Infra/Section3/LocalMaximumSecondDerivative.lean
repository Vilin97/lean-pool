/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-! A one-dimensional second derivative test used by the parabolic maximum
principle. -/

@[expose] public section

open Filter
open scoped Topology

theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra hnot
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge hnot
  have hf' : ContDiff ℝ 1 (deriv f) := by simpa using hf.deriv'
  have hcont : Continuous (deriv (deriv f)) :=
    hf'.continuous_deriv_one
  have hposN : {y : ℝ | 0 < deriv (deriv f) y} ∈ 𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
  have hnear : {y : ℝ | f y ≤ f x ∧ 0 < deriv (deriv f) y} ∈ 𝓝 x :=
    hmax.and hposN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let y := x + r / 2
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball]
    have hdist : dist y x = r / 2 := by
      rw [Real.dist_eq]
      dsimp [y]
      rw [show x + r / 2 - x = r / 2 by ring,
        abs_of_nonneg (by linarith : 0 ≤ r / 2)]
    rw [hdist]
    linarith
  have hlocal : f y ≤ f x := (hball hyball).1
  have hsecond_pos (z : ℝ) (hz : z ∈ interior (Set.Icc x y)) :
      0 < deriv (deriv f) z := by
    have hz' : z ∈ Set.Ioo x y := by simpa [interior_Icc, hxy] using hz
    have hzball : z ∈ Metric.ball x r := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hz'.1))]
      have hzupper : z < x + r / 2 := by simpa [y] using hz'.2
      linarith
    exact (hball hzball).2
  have hderiv_strict : StrictMonoOn (deriv f) (Set.Icc x y) :=
    strictMonoOn_of_deriv_pos (convex_Icc x y)
      (hf'.continuous.continuousOn) hsecond_pos
  have hderiv_x : deriv f x = 0 := hmax.deriv_eq_zero
  have hderiv_y : 0 < deriv f y := by
    have hlt := hderiv_strict ⟨le_rfl, le_of_lt hxy⟩
      ⟨le_of_lt hxy, le_rfl⟩ hxy
    rw [hderiv_x] at hlt
    exact hlt
  have hfirst_pos (z : ℝ) (hz : z ∈ interior (Set.Icc x y)) :
      0 < deriv f z := by
    have hz' : z ∈ Set.Ioo x y := by simpa [interior_Icc, hxy] using hz
    have hlt := hderiv_strict ⟨le_rfl, le_of_lt hxy⟩
      (Set.mem_Icc.mpr ⟨le_of_lt hz'.1,
      le_of_lt hz'.2⟩) hz'.1
    rw [hderiv_x] at hlt
    exact hlt
  have hstrict_f : StrictMonoOn f (Set.Icc x y) :=
    strictMonoOn_of_deriv_pos (convex_Icc x y) hf.continuous.continuousOn hfirst_pos
  have hlt := hstrict_f ⟨le_rfl, le_of_lt hxy⟩
    ⟨le_of_lt hxy, le_rfl⟩ hxy
  exact (not_lt_of_ge hlocal) hlt
