/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.FormalExpression
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointValue

/-!
# The complexity drop of Berarducci's reduction step

Berarducci, Lemma 9.5: replacing the selected factor of a formal expression by one truncation
`b₀^{|γ}` and one fewer copy of `b₀`, while doubling every other exponent, strictly decreases
the complexity, provided `γ` is a residual point of `b₀` close enough to zero.

Only two properties of the truncation are used, both supplied by the residual-point remarks of
Section 6 and Section 9: its ordinal value is strictly below `v_J(b₀)`, and its principal value is
at least `v_J^p(b₀)`. The combinatorial step is therefore stated for an arbitrary multiset of
factors having those two properties, which also accommodates the source's convention of omitting
the truncation when its value is one.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

namespace FormalExpression

open Classical in
/-- The factors of `w` other than the selected one. -/
noncomputable def unselected (w : FormalExpression K) (hw : w ≠ 0) : FormalExpression K :=
  w.filter (· ≠ selected w hw)

open Classical in
theorem unselected_eq (w : FormalExpression K) (hw : w ≠ 0) :
    unselected w hw = w.filter (· ≠ selected w hw) := (rfl)

open Classical in
theorem mem_unselected {w : FormalExpression K} {hw : w ≠ 0}
    {y : SeriesWithOrdinalValueAboveOne K} :
    y ∈ unselected w hw ↔ y ∈ w ∧ y ≠ selected w hw := by
  rw [unselected]
  exact Multiset.mem_filter

open Classical in
/-- Berarducci, Lemma 9.5: the expression
`b₀^{|γ} b₀^{k - 1} b₁^{2 k₁} ⋯ bₙ^{2 kₙ}` obtained from `w` by reducing the selected
exponent, doubling the others, and adjoining the truncation factors `t`. -/
noncomputable def reduced (w : FormalExpression K) (hw : w ≠ 0) (t : FormalExpression K) :
    FormalExpression K :=
  t + Multiset.replicate (selectedExponent w hw - 1) (selected w hw) +
    (unselected w hw + unselected w hw)

theorem reduced_eq (w : FormalExpression K) (hw : w ≠ 0) (t : FormalExpression K) :
    reduced w hw t = t + Multiset.replicate (selectedExponent w hw - 1) (selected w hw) +
      (unselected w hw + unselected w hw) := (rfl)

theorem mem_reduced {w : FormalExpression K} {hw : w ≠ 0} {t : FormalExpression K}
    {y : SeriesWithOrdinalValueAboveOne K} :
    y ∈ reduced w hw t ↔ y ∈ t ∨ (selectedExponent w hw - 1 ≠ 0 ∧ y = selected w hw) ∨
      (y ∈ w ∧ y ≠ selected w hw) := by
  rw [reduced]
  simp only [Multiset.mem_add, Multiset.mem_replicate, mem_unselected, or_self, or_assoc]

theorem one_le_selectedExponent (w : FormalExpression K) (hw : w ≠ 0) :
    1 ≤ selectedExponent w hw := by
  classical
  rw [selectedExponent_eq_count]
  exact Multiset.count_pos.mpr (isSelected_selected w hw).mem

open Classical in
/-- The reduction removes one copy of the selected factor. -/
theorem count_selected_reduced {w : FormalExpression K} {hw : w ≠ 0} {t : FormalExpression K}
    (ht : selected w hw ∉ t) :
    Multiset.count (selected w hw) (reduced w hw t) = selectedExponent w hw - 1 := by
  rw [reduced]
  simp only [Multiset.count_add, Multiset.count_replicate_self]
  rw [Multiset.count_eq_zero.mpr ht,
    Multiset.count_eq_zero.mpr fun h ↦ (mem_unselected.mp h).2 rfl]
  omega

open Classical in
/-- The reduction doubles the exponent of every other factor. -/
theorem count_reduced_of_ne {w : FormalExpression K} {hw : w ≠ 0} {t : FormalExpression K}
    {y : SeriesWithOrdinalValueAboveOne K} (hy : y ≠ selected w hw) (hyt : y ∉ t) :
    Multiset.count y (reduced w hw t) = 2 * Multiset.count y w := by
  rw [reduced, unselected]
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_filter,
    ite_eq_right (Ne.symm hy), ite_eq_left hy, Multiset.count_eq_zero.mpr hyt]
  omega

/-- The selected factor survives the reduction exactly when its exponent exceeds one. -/
theorem selected_mem_reduced {w : FormalExpression K} {hw : w ≠ 0} {t : FormalExpression K}
    (hk : 1 < selectedExponent w hw) : selected w hw ∈ reduced w hw t :=
  mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, rfl⟩))

theorem selectedExponent_lt_of_isSelected {w : FormalExpression K} {hw : w ≠ 0}
    {t : FormalExpression K} (hw₂ : reduced w hw t ≠ 0)
    (ht : selected w hw ∉ t) (hsel : selected (reduced w hw t) hw₂ = selected w hw) :
    selectedExponent (reduced w hw t) hw₂ < selectedExponent w hw := by
  rw [selectedExponent_eq_count, hsel, count_selected_reduced ht]
  have := one_le_selectedExponent w hw
  omega

/-- Case 1 of Berarducci, Lemma 9.5: when the selected exponent exceeds one, the selected factor
of the reduced expression is unchanged. -/
theorem isSelected_reduced (w : FormalExpression K) (hw : w ≠ 0) (t : FormalExpression K)
    (ht : ∀ u ∈ t, ordinalValue u.1 < ordinalValue (selected w hw).1)
    (htp : ∀ u ∈ t, (selected w hw).principalValue ≤ u.principalValue)
    (hk : 1 < selectedExponent w hw) :
    IsSelected (reduced w hw t) (selected w hw) := by
  have hsel := isSelected_selected w hw
  refine ⟨mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, rfl⟩)), ?_, ?_, ?_⟩
  · intro y hy
    rcases mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact htp y h
    · exact le_rfl
    · exact hsel.min_principalValue y hyw
  · intro y hy hyp
    rcases mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact (ht y h).le
    · exact le_rfl
    · exact hsel.max_ordinalValue y hyw hyp
  · intro y hy hyp hyo
    rcases mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact absurd hyo (ht y h).ne
    · exact irrefl_of (WellOrderingRel : SeriesWithOrdinalValueAboveOne K → _ → Prop) _
    · exact hsel.least y hyw hyp hyo

/-- The Dershowitz-Manna step behind the second case of Berarducci, Lemma 9.5: an expression each
of whose factors is either of strictly smaller ordinal value than the selected factor of `w`, or a
factor of `w` other than that one, has strictly smaller complexity. The selected factor of the
smaller expression never has to be identified. -/
theorem complexityLT_of_forall_lt_or_mem {w w' : FormalExpression K} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h : ∀ u ∈ w', ordinalValue u.1 < ordinalValue (selected w hw).1 ∨
      (u ∈ w ∧ u ≠ selected w hw)) :
    ComplexityLT (complexity w' hw') (complexity w hw) := by
  classical
  set f : SeriesWithOrdinalValueAboveOne K → Ordinal := fun y ↦ (ordinalValue y.1).val with hf
  set S : Finset (SeriesWithOrdinalValueAboveOne K) := w'.toFinset.filter
    (fun y ↦ ordinalValue (selected w' hw').1 ≤ ordinalValue y.1) with hS
  set T : Finset (SeriesWithOrdinalValueAboveOne K) :=
    w.toFinset.filter (fun y ↦ ordinalValue (selected w hw).1 ≤ ordinalValue y.1) with hT
  have hxT : selected w hw ∈ T :=
    Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (isSelected_selected w hw).mem, le_rfl⟩
  set R : Finset (SeriesWithOrdinalValueAboveOne K) := T.erase (selected w hw) with hR
  have hkey : ∀ u ∈ S, u ∉ R → ordinalValue u.1 < ordinalValue (selected w hw).1 := by
    intro u hu huR
    have humem : u ∈ w' := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hu).1
    rcases h u humem with hlt | ⟨huw, hux⟩
    · exact hlt
    · rw [hR, Finset.mem_erase] at huR
      have hTu : u ∉ T := fun hmem ↦ huR ⟨hux, hmem⟩
      refine lt_of_not_ge fun hle ↦ hTu ?_
      rw [hT]
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr huw, hle⟩
  have hsplit : ∀ A B : Finset (SeriesWithOrdinalValueAboveOne K),
      A.val = (A ∩ B).val + (A \ B).val := by
    intro A B
    rw [← Finset.filter_mem_eq_inter, Finset.sdiff_eq_filter, Finset.filter_val,
      Finset.filter_val]
    exact (Multiset.filter_add_not _ _).symm
  refine complexityLT_of_relevantValues (X := (S ∩ R).val.map f) (Y := (S \ R).val.map f)
    (Z := f (selected w hw) ::ₘ (R \ S).val.map f) (by simp) ?_ ?_ ?_
  · rw [relevantValues_eq_map, ← hS, hsplit S R, Multiset.map_add]
  · rw [relevantValues_eq_map, ← hT, ← Multiset.cons_erase (s := T.val) hxT,
      ← Finset.erase_val, ← hR, Multiset.map_cons, hsplit R S, Multiset.map_add,
      Finset.inter_comm, Multiset.add_cons]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hy
    rw [Finset.mem_val, Finset.mem_sdiff] at hu
    exact ⟨f (selected w hw), Multiset.mem_cons_self _ _,
      NatOrdinal.val.lt_iff_lt.mpr (hkey u hu.1 hu.2)⟩

/-- The factors other than the selected one form an expression of strictly smaller complexity. -/
theorem complexityLT_unselected {w : FormalExpression K} (hw : w ≠ 0)
    (hr : unselected w hw ≠ 0) :
    ComplexityLT (complexity (unselected w hw) hr) (complexity w hw) :=
  complexityLT_of_forall_lt_or_mem hw hr fun _ hu ↦ Or.inr (mem_unselected.mp hu)

/-- Berarducci, Lemma 9.5: the reduction step strictly decreases the complexity. The adjoined
factors are only required to have strictly smaller ordinal value and no smaller principal value
than the selected factor. -/
theorem complexityLT_reduced (w : FormalExpression K) (hw : w ≠ 0) (t : FormalExpression K)
    (ht : ∀ u ∈ t, ordinalValue u.1 < ordinalValue (selected w hw).1)
    (htp : ∀ u ∈ t, (selected w hw).principalValue ≤ u.principalValue)
    (hw₂ : reduced w hw t ≠ 0) :
    ComplexityLT (complexity (reduced w hw t) hw₂) (complexity w hw) := by
  classical
  have htmem : selected w hw ∉ t := fun h ↦ absurd (ht _ h) (lt_irrefl _)
  rcases lt_or_ge 1 (selectedExponent w hw) with hk | hk
  · -- Case 1: the selected factor survives, so only its exponent moves.
    have hsel : selected (reduced w hw t) hw₂ = selected w hw :=
      (eq_selected_of_isSelected hw₂ (isSelected_reduced w hw t ht htp hk)).symm
    refine complexityLT_of_selectedExponent ?_ (selectedExponent_lt_of_isSelected hw₂ htmem hsel)
    refine relevantValues_congr hw₂ hw hsel fun y hy ↦ ?_
    rw [hsel] at hy
    constructor
    · intro hmem
      rcases mem_reduced.mp hmem with hmem | ⟨-, rfl⟩ | ⟨hmem, -⟩
      · exact absurd hy (not_le.mpr (ht y hmem))
      · exact (isSelected_selected w hw).mem
      · exact hmem
    · intro hmem
      by_cases hyx : y = selected w hw
      · exact mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, hyx⟩))
      · exact mem_reduced.mpr (Or.inr (Or.inr ⟨hmem, hyx⟩))
  · -- Case 2: the selected factor disappears, and its value is replaced by smaller ones.
    have hk1 : selectedExponent w hw - 1 = 0 := by
      have := one_le_selectedExponent w hw
      omega
    refine complexityLT_of_forall_lt_or_mem hw hw₂ fun u hu ↦ ?_
    rcases mem_reduced.mp hu with hmem | ⟨hne, -⟩ | hmem
    · exact Or.inl (ht u hmem)
    · exact absurd hk1 hne
    · exact Or.inr hmem

end FormalExpression

/-- Berarducci, Lemma 9.5: for residual points of the selected factor close enough to zero, the
reduction step strictly decreases the complexity. -/
theorem exists_complexityLT_reduced (w : FormalExpression K) (hw : w ≠ 0) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      γ ∈ residualPointSet (FormalExpression.selected w hw) →
      ∀ t : FormalExpression K,
        (∀ u ∈ t, u.1 = translatedTruncation ((FormalExpression.selected w hw).1 : K⟦ℝ⟧) γ) →
        ∀ hw₂ : FormalExpression.reduced w hw t ≠ 0,
          FormalExpression.ComplexityLT (FormalExpression.complexity _ hw₂)
            (FormalExpression.complexity w hw) := by
  obtain ⟨η, hη, hcut⟩ := exists_ordinalValue_translatedTruncation_lt (FormalExpression.selected w
      hw)
  refine ⟨η, hη, fun γ hlow hhigh hγ t htu hw₂ ↦ ?_⟩
  refine FormalExpression.complexityLT_reduced w hw t (fun u hu ↦ ?_) (fun u hu ↦ ?_) hw₂
  · rw [htu u hu]
    exact hcut γ hlow hhigh
  · exact principalValue_le_of_mem_residualPointSet _ u hγ (htu u hu)

end Berarducci
