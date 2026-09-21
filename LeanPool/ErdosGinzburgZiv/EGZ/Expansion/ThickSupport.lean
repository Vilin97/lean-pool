/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.DilatedGrowth
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A thick support contains a basis

Positive central thickness rules out containment in a proper linear
subspace.  A basis selected from the positive support can therefore be
used in the initial growth phase.
-/

open scoped BigOperators
open Module

namespace EGZ.Expansion

theorem IsCentrallyThick.span_positive_eq_top {p d K : ℕ}
    [NeZero p] [Fact p.Prime] {w : FpCoord p d → ℝ} {δ : ℝ}
    (ht : IsCentrallyThick w K δ) (hw : ∀ v, 0 ≤ w v)
    (hW : 0 < ∑ v, w v) (hδ : 0 < δ) :
    Submodule.span (ZMod p) {v | 0 < w v} = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨ξ, hξ, hker⟩ := (Submodule.span (ZMod p) {v | 0 < w v}).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  have hout := ht ξ hξ
  have hzero : (∑ v, if ¬ HasBoundedRepresentative p K (ξ v) then w v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : 0 < w v
    · have hξv : ξ v = 0 := hker (Submodule.subset_span hv)
      have hrep : HasBoundedRepresentative p K (ξ v) := ⟨0, by simp, by simpa using hξv.symm⟩
      simp [hrep]
    · have hwv : w v = 0 := le_antisymm (le_of_not_gt hv) (hw v)
      simp [hwv]
  rw [hzero] at hout
  exact (not_le_of_gt (mul_pos hδ hW)) hout

/-- Choose a basis indexed by the ambient dimension from positive-weight
translations. -/
theorem IsCentrallyThick.exists_basis {p d K : ℕ}
    [NeZero p] [Fact p.Prime] {w : FpCoord p d → ℝ} {δ : ℝ}
    (ht : IsCentrallyThick w K δ) (hw : ∀ v, 0 ≤ w v)
    (hW : 0 < ∑ v, w v) (hδ : 0 < δ) :
    ∃ E : Basis (Fin d) (ZMod p) (FpCoord p d), ∀ i, 0 < w (E i) := by
  classical
  have hs := (ht.span_positive_eq_top hw hW hδ).ge
  let I : Set (FpCoord p d) := (linearIndepOn_empty (ZMod p) id).extend
    (Set.empty_subset {v | 0 < w v})
  let B : Basis I (ZMod p) (FpCoord p d) := Basis.ofSpan hs
  let : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = d := by
    have hh := Module.finrank_eq_card_basis B
    simpa using hh.symm
  let E := B.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨E, ?_⟩
  intro i
  simp only [E, Basis.reindex_apply]
  exact Basis.ofSpan_subset hs ⟨(Fintype.equivFinOfCardEq hcard).symm i, rfl⟩

end EGZ.Expansion
