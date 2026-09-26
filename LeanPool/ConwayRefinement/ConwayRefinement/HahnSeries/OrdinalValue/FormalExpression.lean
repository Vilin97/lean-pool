/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import Mathlib.SetTheory.Cardinal.Order

import Mathlib.Data.Multiset.DershowitzManna

/-!
# Formal expressions and their complexity

Berarducci, Definitions 9.1 and 9.3. A formal expression is a finite multiset of series of ordinal
value above one; its evaluation is the product of its factors. The selected factor has minimal
principal value, maximal ordinal value among those, and is least for a fixed well order; that rule
determines it uniquely. The relevant factors are those whose ordinal value is at least the selected
factor's, and the complexity records their values together with the multiplicity of the selected
factor.

The source writes the complexity as the ordinal `ω * [α₀, …, α_m] + k`, where
`[α₀, …, α_m] = ω ^ α₀ ⊕ ⋯ ⊕ ω ^ α_m` is chosen so that it decreases when any
`αᵢ` is replaced by finitely many strictly smaller ordinals. That last property is exactly
Mathlib's Dershowitz–Manna relation on multisets, so the complexity is kept as a pair consisting
of a multiset and a natural number, ordered lexicographically. It carries the same information
and inherits well-foundedness from Mathlib, with no ordinal to construct.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

/-- Berarducci, Definition 9.1: a formal expression is a finite multiset of series of ordinal
value above one. -/
abbrev FormalExpression (K : Type v) [Field K] := Multiset (SeriesWithOrdinalValueAboveOne K)

namespace FormalExpression

/-- The product of the factors of a formal expression. -/
def eval (w : FormalExpression K) : Series K := (w.map (·.1)).prod

theorem eval_eq (w : FormalExpression K) : eval w = (w.map (·.1)).prod := (rfl)

theorem eval_zero : (0 : FormalExpression K).eval = 1 := (rfl)

theorem eval_cons (x : SeriesWithOrdinalValueAboveOne K) (w : FormalExpression K) :
    eval (x ::ₘ w) = x.1 * eval w := by
  rw [eval, eval, Multiset.map_cons, Multiset.prod_cons]

/-- Berarducci, Definition 9.3: `x` is the selected factor of `w`. Among the factors of minimal
principal value it has maximal ordinal value, and ties are broken by a fixed well order. -/
structure IsSelected (w : FormalExpression K) (x : SeriesWithOrdinalValueAboveOne K) : Prop where
  mem : x ∈ w
  min_principalValue : ∀ y ∈ w, x.principalValue ≤ y.principalValue
  max_ordinalValue : ∀ y ∈ w, y.principalValue = x.principalValue →
    ordinalValue y.1 ≤ ordinalValue x.1
  least : ∀ y ∈ w, y.principalValue = x.principalValue → ordinalValue y.1 = ordinalValue x.1 →
    ¬ WellOrderingRel y x

theorem existsUnique_isSelected {w : FormalExpression K} (hw : w ≠ 0) :
    ∃! x, IsSelected w x := by
  classical
  have hne : w.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hw (Multiset.toFinset_eq_empty.mp h)
  obtain ⟨x₀, hx₀, hx₀min⟩ :=
    w.toFinset.exists_min_image (fun y ↦ y.principalValue) hne
  set A := w.toFinset.filter fun y ↦ y.principalValue = x₀.principalValue with hAdef
  have hAne : A.Nonempty := ⟨x₀, by simp [hAdef, hx₀]⟩
  obtain ⟨x₁, hx₁, hx₁max⟩ := A.exists_max_image (fun y ↦ ordinalValue y.1) hAne
  set B := A.filter fun y ↦ ordinalValue y.1 = ordinalValue x₁.1 with hBdef
  have hBne : (↑B : Set (SeriesWithOrdinalValueAboveOne K)).Nonempty :=
    ⟨x₁, by simp [hBdef, hx₁]⟩
  have hwf : WellFounded (WellOrderingRel (α := SeriesWithOrdinalValueAboveOne K)) :=
    (WellOrderingRel.isWellOrder (α := SeriesWithOrdinalValueAboveOne K)).wf
  set x := hwf.min _ hBne with hxdef
  have hxB : x ∈ B := hwf.min_mem _ hBne
  have hxA : x ∈ A := (Finset.mem_filter.mp hxB).1
  have hxw : x ∈ w := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hxA).1
  have hxprin : x.principalValue = x₀.principalValue := (Finset.mem_filter.mp hxA).2
  have hxord : ordinalValue x.1 = ordinalValue x₁.1 := (Finset.mem_filter.mp hxB).2
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
    have hyB : y ∈ (↑B : Set (SeriesWithOrdinalValueAboveOne K)) := by
      simp only [hBdef, hAdef, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨⟨hy, hyprin.trans hxprin⟩, hyord.trans hxord⟩
    exact hwf.not_lt_min _ hyB
  · rintro y hy
    have hsel : IsSelected w x := by
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
        have hzB : z ∈ (↑B : Set (SeriesWithOrdinalValueAboveOne K)) := by
          simp only [hBdef, hAdef, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset]
          exact ⟨⟨hz, hzprin.trans hxprin⟩, hzord.trans hxord⟩
        exact hwf.not_lt_min _ hzB
    have hprin : y.principalValue = x.principalValue :=
      le_antisymm (hy.min_principalValue x hxw) (hsel.min_principalValue y hy.mem)
    have hord : ordinalValue y.1 = ordinalValue x.1 :=
      le_antisymm (hsel.max_ordinalValue y hy.mem hprin) (hy.max_ordinalValue x hxw hprin.symm)
    rcases trichotomous_of
      (WellOrderingRel : SeriesWithOrdinalValueAboveOne K → _ → Prop) y x with h | h | h
    · exact absurd h (hsel.least y hy.mem hprin hord)
    · exact h
    · exact absurd h (hy.least x hxw hprin.symm hord.symm)

/-- The selected factor of a nonempty formal expression. -/
noncomputable def selected (w : FormalExpression K) (hw : w ≠ 0) :
    SeriesWithOrdinalValueAboveOne K :=
  (existsUnique_isSelected hw).choose

theorem isSelected_selected (w : FormalExpression K) (hw : w ≠ 0) :
    IsSelected w (selected w hw) :=
  (existsUnique_isSelected hw).choose_spec.1

theorem eq_selected_of_isSelected {w : FormalExpression K} (hw : w ≠ 0)
    {x : SeriesWithOrdinalValueAboveOne K} (hx : IsSelected w x) : x = selected w hw :=
  (existsUnique_isSelected hw).choose_spec.2 x hx

/-- A one-factor expression selects that factor. -/
theorem selected_singleton (x : SeriesWithOrdinalValueAboveOne K) :
    selected {x} (by simp) = x := by
  refine (eq_selected_of_isSelected (by simp) ⟨by simp, ?_, ?_, ?_⟩).symm
  · intro y hy
    rw [Multiset.mem_singleton.mp hy]
  · intro y hy _
    rw [Multiset.mem_singleton.mp hy]
  · intro y hy _ _
    rw [Multiset.mem_singleton.mp hy]
    exact irrefl_of (WellOrderingRel : SeriesWithOrdinalValueAboveOne K → _ → Prop) x

open Classical in
/-- Berarducci, Definition 9.3: the selected exponent is the multiplicity of the selected
factor. -/
noncomputable def selectedExponent (w : FormalExpression K) (hw : w ≠ 0) : ℕ :=
  w.count (selected w hw)

/-- Adjoining another copy of a factor already present does not change the selected factor. -/
theorem selected_cons_of_mem {w : FormalExpression K} (hw : w ≠ 0)
    {y : SeriesWithOrdinalValueAboveOne K} (hy : y ∈ w) :
    selected (y ::ₘ w) Multiset.cons_ne_zero = selected w hw := by
  have hmem : ∀ z ∈ y ::ₘ w, z ∈ w :=
    fun z hz ↦ (Multiset.mem_cons.mp hz).elim (fun h ↦ h ▸ hy) id
  have hsel := isSelected_selected w hw
  refine (eq_selected_of_isSelected Multiset.cons_ne_zero ⟨Multiset.mem_cons_of_mem hsel.mem,
    fun z hz ↦ hsel.min_principalValue z (hmem z hz),
    fun z hz ↦ hsel.max_ordinalValue z (hmem z hz),
    fun z hz ↦ hsel.least z (hmem z hz)⟩).symm

open Classical in
theorem selectedExponent_eq_count (w : FormalExpression K) (hw : w ≠ 0) :
    selectedExponent w hw = w.count (selected w hw) := (rfl)

open Classical in
/-- Berarducci, Definition 9.3: the ordinal values of the relevant factors, namely those whose
ordinal value is at least that of the selected factor. The source indexes these by the distinct
factors, so multiplicities are discarded. -/
noncomputable def relevantValues (w : FormalExpression K) (hw : w ≠ 0) : Multiset Ordinal :=
  (w.toFinset.filter fun y ↦ ordinalValue (selected w hw).1 ≤ ordinalValue y.1).val.map
    fun y ↦ (ordinalValue y.1).val

open Classical in
theorem relevantValues_eq_map (w : FormalExpression K) (hw : w ≠ 0) :
    relevantValues w hw = (w.toFinset.filter fun y ↦
      ordinalValue (selected w hw).1 ≤ ordinalValue y.1).val.map fun y ↦ (ordinalValue y.1).val :=
  (rfl)

open Classical in
/-- The relevant values see only the selected factor and which factors of value at least its own
are present, so duplicating or deleting other factors does not change them. -/
theorem relevantValues_congr {w w' : FormalExpression K} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hsel : selected w hw = selected w' hw')
    (hmem : ∀ y, ordinalValue (selected w hw).1 ≤ ordinalValue y.1 → (y ∈ w ↔ y ∈ w')) :
    relevantValues w hw = relevantValues w' hw' := by
  have hfilter : (w.toFinset.filter fun y ↦ ordinalValue (selected w hw).1 ≤ ordinalValue y.1)
      = w'.toFinset.filter fun y ↦ ordinalValue (selected w hw).1 ≤ ordinalValue y.1 := by
    ext y
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    exact and_congr_left fun h ↦ hmem y h
  rw [relevantValues, relevantValues, ← hsel, hfilter]

/-- Berarducci, Definition 9.3: the complexity of a formal expression, as the pair of the multiset
of relevant-factor values and the selected exponent. -/
noncomputable def complexity (w : FormalExpression K) (hw : w ≠ 0) : Multiset Ordinal × ℕ :=
  (relevantValues w hw, selectedExponent w hw)

/-- The complexity order: the Dershowitz–Manna order on the relevant values, refined by the
selected exponent. This is the order of Berarducci, Definition 9.2. -/
def ComplexityLT : (Multiset Ordinal × ℕ) → (Multiset Ordinal × ℕ) → Prop :=
  Prod.Lex Multiset.IsDershowitzMannaLT (· < ·)

theorem wellFounded_complexityLT : WellFounded (ComplexityLT) :=
  WellFounded.prod_lex Multiset.wellFounded_isDershowitzMannaLT wellFounded_lt

/-- A Dershowitz–Manna step on the relevant values, presented by its witnesses: the values of `w'`
are those of `w` with the nonempty part `Z` replaced by members of `Y`, each below some member of
`Z`. -/
theorem complexityLT_of_relevantValues {w w' : FormalExpression K} {hw : w ≠ 0} {hw' : w' ≠ 0}
    {X Y Z : Multiset Ordinal} (hZ : Z ≠ 0) (hw'X : relevantValues w' hw' = X + Y)
    (hwX : relevantValues w hw = X + Z) (hYZ : ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    ComplexityLT (complexity w' hw') (complexity w hw) :=
  Prod.Lex.left _ _ ⟨X, Y, Z, hZ, hw'X, hwX, hYZ⟩

theorem complexityLT_of_selectedExponent {w w' : FormalExpression K} {hw : w ≠ 0} {hw' : w' ≠ 0}
    (h₁ : relevantValues w' hw' = relevantValues w hw)
    (h₂ : selectedExponent w' hw' < selectedExponent w hw) :
    ComplexityLT (complexity w' hw') (complexity w hw) := by
  rw [complexity, complexity, h₁]
  exact Prod.Lex.right _ h₂

end FormalExpression

end Berarducci
