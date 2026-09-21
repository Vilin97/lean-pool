/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Selection and decreasing multiset complexity

Selection minimizes an ordinal priority, then maximizes an ordinal weight, with a fixed
well-order resolving ties. Complexity records the weights of distinct members at least as
heavy as the selection, followed by the selected multiplicity. Thus duplicating other members
does not increase the first component.

Removing one selected copy, doubling the other multiplicities, and adjoining lighter members
of no smaller priority strictly decreases this well-founded complexity. The argument abstracts
the finite-expression reduction in Berarducci, Definitions 9.1--9.3 and Lemma 9.5; it assumes
no series, ring, or valuation. The first component uses the Mathlib Dershowitz--Manna relation.
-/

public noncomputable section
universe u v
namespace Multiset

/-- Ordinal priorities and weights for selection in a finite multiset. -/
structure SelectionWeights (α : Type v) where
  priority : α → Ordinal.{u}
  weight : α → Ordinal.{u}

namespace SelectionWeights
variable {α : Type v} (s : SelectionWeights.{u, v} α)

/-- A member of least priority, greatest weight among those, and least in a fixed well-order. -/
structure IsSelected (w : Multiset α) (x : α) : Prop where
  mem : x ∈ w
  min_priority : ∀ y ∈ w, s.priority x ≤ s.priority y
  max_weight : ∀ y ∈ w, s.priority y = s.priority x →
    s.weight y ≤ s.weight x
  least : ∀ y ∈ w, s.priority y = s.priority x → s.weight y = s.weight x →
    ¬ WellOrderingRel y x

/-- Every nonempty finite multiset has a unique selected member. -/
theorem existsUnique_isSelected {w : Multiset α} (hw : w ≠ 0) :
    ∃! x, s.IsSelected w x := by
  classical
  have hne : w.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hw (Multiset.toFinset_eq_empty.mp h)
  obtain ⟨x₀, hx₀, hx₀min⟩ :=
    w.toFinset.exists_min_image (fun y ↦ s.priority y) hne
  set A := w.toFinset.filter fun y ↦ s.priority y = s.priority x₀ with hAdef
  have hAne : A.Nonempty := ⟨x₀, by simp [hAdef, hx₀]⟩
  obtain ⟨x₁, hx₁, hx₁max⟩ := A.exists_max_image (fun y ↦ s.weight y) hAne
  set B := A.filter fun y ↦ s.weight y = s.weight x₁ with hBdef
  have hBne : (↑B : Set α).Nonempty :=
    ⟨x₁, by simp [hBdef, hx₁]⟩
  have hwf : WellFounded (WellOrderingRel (α := α)) :=
    (WellOrderingRel.isWellOrder (α := α)).wf
  set x := hwf.min _ hBne with hxdef
  have hxB : x ∈ B := hwf.min_mem _ hBne
  have hxA : x ∈ A := (Finset.mem_filter.mp hxB).1
  have hxw : x ∈ w := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hxA).1
  have hxprin : s.priority x = s.priority x₀ := (Finset.mem_filter.mp hxA).2
  have hxord : s.weight x = s.weight x₁ := (Finset.mem_filter.mp hxB).2
  refine ⟨x, ⟨hxw, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    rw [hxprin]
    exact hx₀min y (Multiset.mem_toFinset.mpr hy)
  · intro y hy hyprin
    rw [hxord]
    refine hx₁max y ?_
    simp only [hAdef, Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨hy, hyprin.trans hxprin⟩
  · intro y hy hyprin hyord
    have hyB : y ∈ (↑B : Set α) := by
      simp only [hBdef, hAdef, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨⟨hy, hyprin.trans hxprin⟩, hyord.trans hxord⟩
    exact hwf.not_lt_min _ hyB
  · rintro y hy
    have hsel : s.IsSelected w x := by
      refine ⟨hxw, ?_, ?_, ?_⟩
      · intro z hz
        rw [hxprin]
        exact hx₀min z (Multiset.mem_toFinset.mpr hz)
      · intro z hz hzprin
        rw [hxord]
        refine hx₁max z ?_
        simp only [hAdef, Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hz, hzprin.trans hxprin⟩
      · intro z hz hzprin hzord
        have hzB : z ∈ (↑B : Set α) := by
          simp only [hBdef, hAdef, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset]
          exact ⟨⟨hz, hzprin.trans hxprin⟩, hzord.trans hxord⟩
        exact hwf.not_lt_min _ hzB
    have hprin : s.priority y = s.priority x :=
      le_antisymm (hy.min_priority x hxw) (hsel.min_priority y hy.mem)
    have hord : s.weight y = s.weight x :=
      le_antisymm (hsel.max_weight y hy.mem hprin) (hy.max_weight x hxw hprin.symm)
    rcases trichotomous_of
      (WellOrderingRel : α → _ → Prop) y x with h | h | h
    · exact absurd h (hsel.least y hy.mem hprin hord)
    · exact h
    · exact absurd h (hy.least x hxw hprin.symm hord.symm)

/-- The selected member of a nonempty multiset. -/
noncomputable def selected (w : Multiset α) (hw : w ≠ 0) :
    α :=
  (s.existsUnique_isSelected hw).choose

theorem isSelected_selected (w : Multiset α) (hw : w ≠ 0) :
    s.IsSelected w (s.selected w hw) :=
  (s.existsUnique_isSelected hw).choose_spec.1

theorem eq_selected_of_isSelected {w : Multiset α} (hw : w ≠ 0)
    {x : α} (hx : s.IsSelected w x) : x = s.selected w hw :=
  (s.existsUnique_isSelected hw).choose_spec.2 x hx

theorem selected_singleton (x : α) :
    s.selected {x} (by simp) = x := by
  refine (s.eq_selected_of_isSelected (by simp) ⟨by simp, ?_, ?_, ?_⟩).symm
  · intro y hy
    rw [Multiset.mem_singleton.mp hy]
  · intro y hy _
    rw [Multiset.mem_singleton.mp hy]
  · intro y hy _ _
    rw [Multiset.mem_singleton.mp hy]
    exact irrefl_of (WellOrderingRel : α → _ → Prop) x

open Classical in
/-- The multiplicity of the selected member. -/
noncomputable def selectedExponent (w : Multiset α) (hw : w ≠ 0) : ℕ :=
  w.count (s.selected w hw)

theorem selected_cons_of_mem {w : Multiset α} (hw : w ≠ 0)
    {y : α} (hy : y ∈ w) :
    s.selected (y ::ₘ w) Multiset.cons_ne_zero = s.selected w hw := by
  have hmem : ∀ z ∈ y ::ₘ w, z ∈ w :=
    fun z hz ↦ (Multiset.mem_cons.mp hz).elim (fun h ↦ h ▸ hy) id
  have hsel := s.isSelected_selected w hw
  refine (s.eq_selected_of_isSelected Multiset.cons_ne_zero ⟨Multiset.mem_cons_of_mem hsel.mem,
    fun z hz ↦ hsel.min_priority z (hmem z hz),
    fun z hz ↦ hsel.max_weight z (hmem z hz),
    fun z hz ↦ hsel.least z (hmem z hz)⟩).symm

open Classical in
theorem selectedExponent_eq_count (w : Multiset α) (hw : w ≠ 0) :
    s.selectedExponent w hw = w.count (s.selected w hw) := (rfl)

open Classical in
/-- The weights of distinct members at least as heavy as the selected member. -/
noncomputable def relevantValues (w : Multiset α) (hw : w ≠ 0) : Multiset Ordinal :=
  (w.toFinset.filter fun y ↦ s.weight (s.selected w hw) ≤ s.weight y).val.map
    fun y ↦ s.weight y

open Classical in
theorem relevantValues_eq_map (w : Multiset α) (hw : w ≠ 0) :
    s.relevantValues w hw = (w.toFinset.filter fun y ↦
      s.weight (s.selected w hw) ≤ s.weight y).val.map fun y ↦ s.weight y :=
  (rfl)

open Classical in
/-- Equal selections and equal relevant members give the same relevant-weight multiset. -/
theorem relevantValues_congr {w w' : Multiset α} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hsel : s.selected w hw = s.selected w' hw')
    (hmem : ∀ y, s.weight (s.selected w hw) ≤ s.weight y → (y ∈ w ↔ y ∈ w')) :
    s.relevantValues w hw = s.relevantValues w' hw' := by
  have hfilter : (w.toFinset.filter fun y ↦ s.weight (s.selected w hw) ≤ s.weight y)
      = w'.toFinset.filter fun y ↦ s.weight (s.selected w hw) ≤ s.weight y := by
    ext y
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    exact and_congr_left fun h ↦ hmem y h
  rw [relevantValues, relevantValues, ← hsel, hfilter]

/-- The distinct relevant weights, followed by the selected multiplicity. -/
noncomputable def complexity (w : Multiset α) (hw : w ≠ 0) : Multiset Ordinal × ℕ :=
  (s.relevantValues w hw, s.selectedExponent w hw)

/-- Lexicographic decrease of relevant weights in the Dershowitz--Manna order, then multiplicity. -/
def ComplexityLT : (Multiset Ordinal × ℕ) → (Multiset Ordinal × ℕ) → Prop :=
  Prod.Lex Multiset.IsDershowitzMannaLT (· < ·)

/-- The complexity order is well-founded. -/
theorem wellFounded_complexityLT : WellFounded (ComplexityLT) :=
  WellFounded.prod_lex Multiset.wellFounded_isDershowitzMannaLT wellFounded_lt

theorem complexityLT_of_relevantValues {w w' : Multiset α} {hw : w ≠ 0} {hw' : w' ≠ 0}
    {X Y Z : Multiset Ordinal} (hZ : Z ≠ 0) (hw'X : s.relevantValues w' hw' = X + Y)
    (hwX : s.relevantValues w hw = X + Z) (hYZ : ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    ComplexityLT (s.complexity w' hw') (s.complexity w hw) :=
  Prod.Lex.left _ _ ⟨X, Y, Z, hZ, hw'X, hwX, hYZ⟩

theorem complexityLT_of_selectedExponent {w w' : Multiset α} {hw : w ≠ 0} {hw' : w' ≠ 0}
    (h₁ : s.relevantValues w' hw' = s.relevantValues w hw)
    (h₂ : s.selectedExponent w' hw' < s.selectedExponent w hw) :
    ComplexityLT (s.complexity w' hw') (s.complexity w hw) := by
  rw [complexity, complexity, h₁]
  exact Prod.Lex.right _ h₂

open Classical in
/-- The multiset remaining after removing every copy of the selected member. -/
noncomputable def unselected (w : Multiset α) (hw : w ≠ 0) : Multiset α :=
  w.filter (· ≠ s.selected w hw)

open Classical in
theorem unselected_eq (w : Multiset α) (hw : w ≠ 0) :
    s.unselected w hw = w.filter (· ≠ s.selected w hw) := (rfl)

open Classical in
theorem mem_unselected {w : Multiset α} {hw : w ≠ 0}
    {y : α} :
    y ∈ s.unselected w hw ↔ y ∈ w ∧ y ≠ s.selected w hw := by
  rw [unselected]
  exact Multiset.mem_filter

open Classical in
/-- Remove one selected copy, double all other copies, and adjoin the replacement multiset. -/
noncomputable def reduced (w : Multiset α) (hw : w ≠ 0) (t : Multiset α) :
    Multiset α :=
  t + Multiset.replicate (s.selectedExponent w hw - 1) (s.selected w hw) +
    (s.unselected w hw + s.unselected w hw)

theorem reduced_eq (w : Multiset α) (hw : w ≠ 0) (t : Multiset α) :
    s.reduced w hw t = t + Multiset.replicate (s.selectedExponent w hw - 1) (s.selected w hw) +
      (s.unselected w hw + s.unselected w hw) := (rfl)

theorem mem_reduced {w : Multiset α} {hw : w ≠ 0} {t : Multiset α}
    {y : α} :
    y ∈ s.reduced w hw t ↔ y ∈ t ∨ (s.selectedExponent w hw - 1 ≠ 0 ∧ y = s.selected w hw) ∨
      (y ∈ w ∧ y ≠ s.selected w hw) := by
  rw [reduced]
  simp only [Multiset.mem_add, Multiset.mem_replicate, s.mem_unselected, or_self, or_assoc]

theorem one_le_selectedExponent (w : Multiset α) (hw : w ≠ 0) :
    1 ≤ s.selectedExponent w hw := by
  classical
  rw [s.selectedExponent_eq_count]
  exact Multiset.count_pos.mpr (s.isSelected_selected w hw).mem

open Classical in
/-- A replacement excluding the selected member reduces its multiplicity by one. -/
theorem count_selected_reduced {w : Multiset α} {hw : w ≠ 0} {t : Multiset α}
    (ht : s.selected w hw ∉ t) :
    Multiset.count (s.selected w hw) (s.reduced w hw t) = s.selectedExponent w hw - 1 := by
  rw [reduced]
  simp only [Multiset.count_add, Multiset.count_replicate_self]
  rw [Multiset.count_eq_zero.mpr ht,
    Multiset.count_eq_zero.mpr fun h ↦ (s.mem_unselected.mp h).2 rfl]
  omega

open Classical in
/-- A member distinct from the selection and absent from the replacement is doubled. -/
theorem count_reduced_of_ne {w : Multiset α} {hw : w ≠ 0} {t : Multiset α}
    {y : α} (hy : y ≠ s.selected w hw) (hyt : y ∉ t) :
    Multiset.count y (s.reduced w hw t) = 2 * Multiset.count y w := by
  rw [reduced, unselected]
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_filter,
    if_neg (Ne.symm hy), if_pos hy, Multiset.count_eq_zero.mpr hyt]
  omega

theorem selected_mem_reduced {w : Multiset α} {hw : w ≠ 0} {t : Multiset α}
    (hk : 1 < s.selectedExponent w hw) : s.selected w hw ∈ s.reduced w hw t :=
  s.mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, rfl⟩))

theorem selectedExponent_lt_of_isSelected {w : Multiset α} {hw : w ≠ 0}
    {t : Multiset α} (hw₂ : s.reduced w hw t ≠ 0)
    (ht : s.selected w hw ∉ t) (hsel : s.selected (s.reduced w hw t) hw₂ = s.selected w hw) :
    s.selectedExponent (s.reduced w hw t) hw₂ < s.selectedExponent w hw := by
  rw [s.selectedExponent_eq_count, hsel, s.count_selected_reduced ht]
  have := s.one_le_selectedExponent w hw
  omega

/-- If a selected copy remains, lighter replacements of no smaller priority preserve selection. -/
theorem isSelected_reduced (w : Multiset α) (hw : w ≠ 0) (t : Multiset α)
    (ht : ∀ u ∈ t, s.weight u < s.weight (s.selected w hw))
    (htp : ∀ u ∈ t, s.priority (s.selected w hw) ≤ s.priority u)
    (hk : 1 < s.selectedExponent w hw) :
    s.IsSelected (s.reduced w hw t) (s.selected w hw) := by
  have hsel := s.isSelected_selected w hw
  refine ⟨s.mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, rfl⟩)), ?_, ?_, ?_⟩
  · intro y hy
    rcases s.mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact htp y h
    · exact le_rfl
    · exact hsel.min_priority y hyw
  · intro y hy hyp
    rcases s.mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact (ht y h).le
    · exact le_rfl
    · exact hsel.max_weight y hyw hyp
  · intro y hy hyp hyo
    rcases s.mem_reduced.mp hy with h | ⟨-, rfl⟩ | ⟨hyw, -⟩
    · exact absurd hyo (ht y h).ne
    · exact irrefl_of (WellOrderingRel : α → _ → Prop) _
    · exact hsel.least y hyw hyp hyo

/-- Deleting the selection and introducing only lighter new members strictly lowers complexity. -/
theorem complexityLT_of_forall_lt_or_mem {w w' : Multiset α} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h : ∀ u ∈ w', s.weight u < s.weight (s.selected w hw) ∨
      (u ∈ w ∧ u ≠ s.selected w hw)) :
    ComplexityLT (s.complexity w' hw') (s.complexity w hw) := by
  classical
  set f : α → Ordinal := fun y ↦ s.weight y with hf
  set S : Finset α := w'.toFinset.filter
    (fun y ↦ s.weight (s.selected w' hw') ≤ s.weight y) with hS
  set T : Finset α :=
    w.toFinset.filter (fun y ↦ s.weight (s.selected w hw) ≤ s.weight y) with hT
  have hxT : s.selected w hw ∈ T :=
    Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr (s.isSelected_selected w hw).mem, le_rfl⟩
  set R : Finset α := T.erase (s.selected w hw) with hR
  have hkey : ∀ u ∈ S, u ∉ R → s.weight u < s.weight (s.selected w hw) := by
    intro u hu huR
    have humem : u ∈ w' := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hu).1
    rcases h u humem with hlt | ⟨huw, hux⟩
    · exact hlt
    · rw [hR, Finset.mem_erase] at huR
      have hTu : u ∉ T := fun hmem ↦ huR ⟨hux, hmem⟩
      refine lt_of_not_ge fun hle ↦ hTu ?_
      rw [hT]
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr huw, hle⟩
  have hsplit : ∀ A B : Finset α,
      A.val = (A ∩ B).val + (A \ B).val := by
    intro A B
    rw [← Finset.filter_mem_eq_inter, Finset.sdiff_eq_filter, Finset.filter_val,
      Finset.filter_val]
    exact (Multiset.filter_add_not _ _).symm
  refine s.complexityLT_of_relevantValues (X := (S ∩ R).val.map f) (Y := (S \ R).val.map f)
    (Z := f (s.selected w hw) ::ₘ (R \ S).val.map f) (by simp) ?_ ?_ ?_
  · rw [relevantValues_eq_map, ← hS, hsplit S R, Multiset.map_add]
  · rw [relevantValues_eq_map, ← hT, ← Multiset.cons_erase (s := T.val) hxT,
      ← Finset.erase_val, ← hR, Multiset.map_cons, hsplit R S, Multiset.map_add,
      Finset.inter_comm, Multiset.add_cons]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hy
    rw [Finset.mem_val, Finset.mem_sdiff] at hu
    exact ⟨f (s.selected w hw), Multiset.mem_cons_self _ _,
      hkey u hu.1 hu.2⟩

/-- Removing every selected copy strictly lowers complexity when the remainder is nonempty. -/
theorem complexityLT_unselected {w : Multiset α} (hw : w ≠ 0)
    (hr : s.unselected w hw ≠ 0) :
    ComplexityLT (s.complexity (s.unselected w hw) hr) (s.complexity w hw) :=
  s.complexityLT_of_forall_lt_or_mem hw hr fun _ hu ↦ Or.inr (s.mem_unselected.mp hu)

/-- Replacing one selected copy by lighter members of no smaller priority strictly lowers
complexity, even while doubling every other member. -/
theorem complexityLT_reduced (w : Multiset α) (hw : w ≠ 0) (t : Multiset α)
    (ht : ∀ u ∈ t, s.weight u < s.weight (s.selected w hw))
    (htp : ∀ u ∈ t, s.priority (s.selected w hw) ≤ s.priority u)
    (hw₂ : s.reduced w hw t ≠ 0) :
    ComplexityLT (s.complexity (s.reduced w hw t) hw₂) (s.complexity w hw) := by
  classical
  have htmem : s.selected w hw ∉ t := fun h ↦ absurd (ht _ h) (lt_irrefl _)
  rcases lt_or_ge 1 (s.selectedExponent w hw) with hk | hk
  · -- Case 1: the selected factor survives, so only its exponent moves.
    have hsel : s.selected (s.reduced w hw t) hw₂ = s.selected w hw :=
      (s.eq_selected_of_isSelected hw₂ (s.isSelected_reduced w hw t ht htp hk)).symm
    refine s.complexityLT_of_selectedExponent ?_
      (s.selectedExponent_lt_of_isSelected hw₂ htmem hsel)
    refine s.relevantValues_congr hw₂ hw hsel fun y hy ↦ ?_
    rw [hsel] at hy
    constructor
    · intro hmem
      rcases s.mem_reduced.mp hmem with hmem | ⟨-, rfl⟩ | ⟨hmem, -⟩
      · exact absurd hy (not_le.mpr (ht y hmem))
      · exact (s.isSelected_selected w hw).mem
      · exact hmem
    · intro hmem
      by_cases hyx : y = s.selected w hw
      · exact s.mem_reduced.mpr (Or.inr (Or.inl ⟨by omega, hyx⟩))
      · exact s.mem_reduced.mpr (Or.inr (Or.inr ⟨hmem, hyx⟩))
  · -- Case 2: the selected factor disappears, and its value is replaced by smaller ones.
    have hk1 : s.selectedExponent w hw - 1 = 0 := by
      have := s.one_le_selectedExponent w hw
      omega
    refine s.complexityLT_of_forall_lt_or_mem hw hw₂ fun u hu ↦ ?_
    rcases s.mem_reduced.mp hu with hmem | ⟨hne, -⟩ | hmem
    · exact Or.inl (ht u hmem)
    · exact absurd hk1 hne
    · exact Or.inr hmem

/-- The selected copies and the remaining factors partition the original multiset. -/
theorem replicate_selectedExponent_add_unselected (w : Multiset α) (hw : w ≠ 0) :
    Multiset.replicate (s.selectedExponent w hw) (s.selected w hw) + s.unselected w hw = w := by
  classical
  refine Multiset.ext.mpr fun y ↦ ?_
  rw [Multiset.count_add, s.unselected_eq, Multiset.count_replicate, Multiset.count_filter]
  by_cases hy : y = s.selected w hw
  · subst hy
    rw [if_pos rfl, if_neg (fun h ↦ h rfl), add_zero, s.selectedExponent_eq_count]
  · rw [if_neg (Ne.symm hy), if_pos hy, zero_add]

/-- The complexity consists of the relevant distinct-factor weights and selected multiplicity. -/
theorem complexity_eq (w : Multiset α) (hw : w ≠ 0) :
    s.complexity w hw = (s.relevantValues w hw, s.selectedExponent w hw) := (rfl)

end SelectionWeights
end Multiset
