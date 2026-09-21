/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Open Set -/

noncomputable section

open Set Metric TopologicalSpace Function

open scoped BigOperators ContDiff

namespace Homogenization

/-!
# Smooth cutoffs subordinate to an open set

For a compact set `K` contained in an open set `U` of a finite-dimensional real
normed space, this file constructs a smooth cutoff function that equals one on
`K` and has closed support inside `U`.

The construction covers `K` by finitely many smooth bump functions supported in
`U` and forms `1 - ∏ (1 - fₓ)`, a smooth partition-of-unity-style envelope.
-/

/-- A compact subset of an open set in a finite-dimensional real normed space admits a
smooth cutoff which is one on the compact set and has closed support in the open set. -/
theorem exists_contDiff_one_on_compact_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      EqOn χ 1 K ∧ tsupport χ ⊆ U := by
  classical
  have hlocal : ∀ x : K, ∃ d : ℝ, 0 < d ∧ Euclidean.closedBall (x : E) d ⊆ U := by
    intro x
    obtain ⟨d, hd, hdU⟩ :=
      Euclidean.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hKU x.2))
    exact ⟨d, hd, hdU⟩
  choose d hd_pos hdU using hlocal
  let b : (x : K) → ContDiffBump (toEuclidean (x : E)) := fun x =>
    { rIn := d x / 2
      rOut := d x
      rIn_pos := half_pos (hd_pos x)
      rIn_lt_rOut := half_lt_self (hd_pos x) }
  let f : K → E → ℝ := fun x => b x ∘ toEuclidean
  have hf_tsupport : ∀ x : K, tsupport (f x) ⊆ U := by
    intro x
    have hsupport : (f x).support ⊆ Euclidean.ball (x : E) (d x) := by
      intro y hy
      have hy' : toEuclidean y ∈ Function.support (b x) := by
        simpa only [f, Function.mem_support, Function.comp_apply, Ne] using hy
      rwa [ContDiffBump.support_eq] at hy'
    have htsupport : tsupport (f x) ⊆ Euclidean.closedBall (x : E) (d x) := by
      rw [tsupport, ← Euclidean.closure_ball _ (hd_pos x).ne']
      exact closure_mono hsupport
    exact htsupport.trans (hdU x)
  have hf_smooth : ∀ x : K, ContDiff ℝ ∞ (f x) := by
    intro x
    exact (b x).contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hf_bounds : ∀ x : K, ∀ y : E, 0 ≤ f x y ∧ f x y ≤ 1 := by
    intro x y
    exact ⟨(b x).nonneg, (b x).le_one⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : K => Euclidean.ball (x : E) (d x / 2))
    (fun x => Euclidean.isOpen_ball)
    (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, Euclidean.mem_ball_self (half_pos (hd_pos ⟨x, hx⟩))⟩)
  let χ : E → ℝ := fun y => 1 - ∏ x ∈ t, (1 - f x y)
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub <| contDiff_prod fun x _ => contDiff_const.sub (hf_smooth x)
  · intro y
    have hprod_nonneg : 0 ≤ ∏ x ∈ t, (1 - f x y) :=
      Finset.prod_nonneg fun x _ => sub_nonneg.mpr (hf_bounds x y).2
    have hprod_le_one : (∏ x ∈ t, (1 - f x y)) ≤ 1 :=
      Finset.prod_le_one
        (fun x _ => sub_nonneg.mpr (hf_bounds x y).2)
        (fun x _ => by linarith [(hf_bounds x y).1])
    exact ⟨sub_nonneg.mpr hprod_le_one, by linarith⟩
  · intro y hy
    rcases mem_iUnion₂.1 (ht hy) with ⟨x, hxt, hyx⟩
    have hfx : f x y = 1 := by
      apply (b x).one_of_mem_closedBall
      change Euclidean.dist y (x : E) ≤ d x / 2
      exact hyx.le
    have hzero : 1 - f x y = 0 := sub_eq_zero.mpr hfx.symm
    have hprod_zero : ∏ x ∈ t, (1 - f x y) = 0 := Finset.prod_eq_zero hxt hzero
    simp [χ, hprod_zero]
  · have hsupport : Function.support χ ⊆ ⋃ x ∈ t, tsupport (f x) := by
      intro y hy
      by_contra h
      have hz : ∀ x ∈ t, f x y = 0 := by
        intro x hxt
        by_contra hxy
        apply h
        exact mem_iUnion₂.2 ⟨x, hxt, subset_closure hxy⟩
      have hone : ∀ x ∈ t, 1 - f x y = 1 := by
        intro x hxt
        rw [hz x hxt, sub_zero]
      have hprod_one : ∏ x ∈ t, (1 - f x y) = 1 := by
        rw [Finset.prod_eq_one]
        intro x hxt
        exact hone x hxt
      have : χ y = 0 := by simp [χ, hprod_one]
      exact hy this
    have hclosed : IsClosed (⋃ x ∈ t, tsupport (f x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal hsupport hclosed).trans ?_
    intro y hy
    rcases mem_iUnion₂.1 hy with ⟨x, hxt, hyx⟩
    exact hf_tsupport x hyx

end Homogenization
