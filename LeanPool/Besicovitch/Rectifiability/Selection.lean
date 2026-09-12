/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Maximal disjoint selection

This file extracts a countable disjoint subfamily of uniformly bounded open sets. Every original
set meets a selected set whose diameter is more than half as large.
-/

@[expose] public section

open Bornology Set

namespace LeanPool.Besicovitch

/-- A uniformly bounded family of nonempty bounded open sets has a countable disjoint subfamily
meeting every member at a scale larger than half its diameter. -/
theorem exists_countable_disjoint_subfamily
    (family : Set (Set (EuclideanSpace ℝ (Fin 2))))
    (hopen : ∀ V ∈ family, IsOpen V)
    (hnonempty : ∀ V ∈ family, V.Nonempty)
    (hbounded : ∀ V ∈ family, IsBounded V)
    (R : ℝ) (hdiam : ∀ V ∈ family, Metric.diam V ≤ R) :
    ∃ chosen ⊆ family, chosen.PairwiseDisjoint id ∧ chosen.Countable ∧
      ∀ V ∈ family, ∃ W ∈ chosen,
        (V ∩ W).Nonempty ∧ Metric.diam V < 2 * Metric.diam W := by
  obtain ⟨chosen, hchosen, hdisjoint, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement id family Metric.diam (3 / 2)
      (by norm_num) (fun _ _ ↦ Metric.diam_nonneg) R hdiam hnonempty
  refine ⟨chosen, hchosen, hdisjoint, ?_, fun V hV ↦ ?_⟩
  · exact hdisjoint.countable_of_isOpen
      (fun W hW ↦ hopen W (hchosen hW)) (fun W hW ↦ hnonempty W (hchosen hW))
  obtain ⟨W, hW, hVW, hscale⟩ := hcover V hV
  refine ⟨W, hW, hVW, ?_⟩
  have hW_nontrivial : W.Nontrivial := by
    obtain ⟨x, hx⟩ := hnonempty W (hchosen hW)
    obtain ⟨y, hy, hyx⟩ :=
      preperfect_iff_nhds.mp (hopen W (hchosen hW)).preperfect x hx univ (by simp)
    exact nontrivial_of_mem_mem_ne hx hy.2 hyx.symm
  have hW_diam : 0 < Metric.diam W := Metric.diam_pos hW_nontrivial (hbounded W (hchosen hW))
  norm_num at hscale ⊢
  linarith

end LeanPool.Besicovitch
