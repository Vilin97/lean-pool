/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.Polish
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
/-!
# Generic Satisfaction Measurability for Carrier-Parametric Structure Spaces

This file proves that satisfaction of Lω₁ω formulas is measurable on
`StructureSpaceOn L α` for any encodable carrier α. This generalizes the
ℕ-specific results in `SatisfactionBorel.lean`.

## Main Definitions

- `ModelsOfBoundedOn`: The set of codes in `StructureSpaceOn L α` where a bounded
  formula is realized.
- `ModelsOfOn`: The set of codes where a sentence is realized.

## Main Results

- `modelsOfBoundedOn_measurableSet`: Satisfaction of any bounded Lω₁ω formula is
  measurable on `StructureSpaceOn L α`.
- `modelsOfOn_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
-/

universe u v u'

namespace FirstOrder

namespace Language

open Structure MeasureTheory

variable {L : Language.{u, v}}

/-- In a relational language, every term is a variable. -/
theorem Term.eq_var_of_isRelational [L.IsRelational] {β : Type*} (t : L.Term β) :
    ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f => exact (IsEmpty.false f).elim

section Measurability

variable [L.IsRelational] {α : Type*}

/-- The set of codes in `StructureSpaceOn L α` where a bounded formula is realized,
given variable assignments. -/
private def ModelsOfBoundedOn
    {β : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    Set (StructureSpaceOn L α) :=
  {c | @BoundedFormulaω.Realize L α (StructureSpaceOn.toStructure c) β n φ v xs}

/-- The set of codes in `StructureSpaceOn L α` where a sentence is realized. -/
def ModelsOfOn (φ : L.Sentenceω) : Set (StructureSpaceOn L α) :=
  ModelsOfBoundedOn φ Empty.elim Fin.elim0

private theorem modelsOfBoundedOn_falsum {β : Type u'} {n : ℕ}
    (v : β → α) (xs : Fin n → α) :
    ModelsOfBoundedOn (L := L) (α := α) BoundedFormulaω.falsum v xs = ∅ := by
  ext c; simp [ModelsOfBoundedOn]

private theorem modelsOfBoundedOn_imp {β : Type u'} {n : ℕ}
    (φ ψ : L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    ModelsOfBoundedOn (α := α) (φ.imp ψ) v xs =
    (ModelsOfBoundedOn (α := α) φ v xs)ᶜ ∪ (ModelsOfBoundedOn (α := α) ψ v xs) := by
  ext c
  simp only [ModelsOfBoundedOn, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
  exact Iff.intro (fun h => by tauto) (fun h => by tauto)

private theorem modelsOfBoundedOn_all {β : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω β (n + 1)) (v : β → α) (xs : Fin n → α) :
    ModelsOfBoundedOn (α := α) φ.all v xs =
    ⋂ (m : α), ModelsOfBoundedOn (α := α) φ v (Fin.snoc xs m) := by
  ext c; simp only [ModelsOfBoundedOn, Set.mem_ofPred_eq, Set.mem_iInter]; rfl

private theorem modelsOfBoundedOn_iSup {β : Type u'} {n : ℕ}
    (φs : ℕ → L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    ModelsOfBoundedOn (α := α) (BoundedFormulaω.iSup φs) v xs =
    ⋃ (i : ℕ), ModelsOfBoundedOn (α := α) (φs i) v xs := by
  ext c; simp only [ModelsOfBoundedOn, Set.mem_ofPred_eq, Set.mem_iUnion]; rfl

private theorem modelsOfBoundedOn_iInf {β : Type u'} {n : ℕ}
    (φs : ℕ → L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    ModelsOfBoundedOn (α := α) (BoundedFormulaω.iInf φs) v xs =
    ⋂ (i : ℕ), ModelsOfBoundedOn (α := α) (φs i) v xs := by
  ext c; simp only [ModelsOfBoundedOn, Set.mem_ofPred_eq, Set.mem_iInter]; rfl

/-- Satisfaction of any bounded Lω₁ω formula in a countable relational language
is measurable on the carrier-parametric structure space. -/
private theorem modelsOfBoundedOn_measurableSet [Countable α]
    {β : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    MeasurableSet (ModelsOfBoundedOn (α := α) φ v xs) := by
  induction φ with
  | falsum =>
    rw [modelsOfBoundedOn_falsum]; exact MeasurableSet.empty
  | @equal _ t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    by_cases h : Sum.elim v xs x₁ = Sum.elim v xs x₂
    · convert MeasurableSet.univ (α := StructureSpaceOn L α)
      ext c
      simp only [Set.mem_ofPred_eq, ModelsOfBoundedOn, Set.mem_univ, iff_true]
      let := StructureSpaceOn.toStructure c
      simp [BoundedFormulaω.Realize, Term.realize, h]
    · convert MeasurableSet.empty (α := StructureSpaceOn L α)
      ext c
      simp only [Set.mem_ofPred_eq, ModelsOfBoundedOn, Set.mem_empty_iff_false, iff_false]
      intro hc
      apply h
      let := StructureSpaceOn.toStructure c
      simp [BoundedFormulaω.Realize, Term.realize] at hc
      exact hc
  | @rel _ l R ts =>
    choose xs' hxs' using fun i => Term.eq_var_of_isRelational (ts i)
    set tup : Fin l → α := fun i => Sum.elim v xs (xs' i)
    have htup : ∀ (c : StructureSpaceOn L α),
        letI := StructureSpaceOn.toStructure c
        (fun i => (ts i).realize (Sum.elim v xs)) = tup := by
      intro c
      let := StructureSpaceOn.toStructure c
      funext i
      simp [hxs' i, Term.realize_var, tup]
    convert measurableSet_relHoldsOn (L := L) ⟨⟨l, R⟩, tup⟩ using 1
    ext c
    simp only [Set.mem_ofPred_eq, ModelsOfBoundedOn]
    constructor
    · intro hc
      let := StructureSpaceOn.toStructure c
      have hrel : @Structure.RelMap L α (StructureSpaceOn.toStructure c) l R
          (fun i => (ts i).realize (Sum.elim v xs)) := hc
      rw [StructureSpaceOn.relMap_toStructure] at hrel
      rwa [htup] at hrel
    · intro hc
      let := StructureSpaceOn.toStructure c
      show @Structure.RelMap L α (StructureSpaceOn.toStructure c) l R
          (fun i => (ts i).realize (Sum.elim v xs))
      rw [StructureSpaceOn.relMap_toStructure, htup]
      exact hc
  | imp φ ψ ih_φ ih_ψ =>
    rw [modelsOfBoundedOn_imp]; exact (ih_φ xs).compl.union (ih_ψ xs)
  | all φ ih =>
    rw [modelsOfBoundedOn_all]; exact MeasurableSet.iInter (fun m => ih (Fin.snoc xs m))
  | iSup φs ih =>
    rw [modelsOfBoundedOn_iSup]; exact MeasurableSet.iUnion (fun i => ih i xs)
  | iInf φs ih =>
    rw [modelsOfBoundedOn_iInf]; exact MeasurableSet.iInter (fun i => ih i xs)

/-- Satisfaction of any Lω₁ω sentence in a countable relational language
is measurable on the carrier-parametric structure space. -/
theorem modelsOfOn_measurableSet [Countable α]
    (φ : L.Sentenceω) :
    MeasurableSet (ModelsOfOn (α := α) φ) :=
  modelsOfBoundedOn_measurableSet φ Empty.elim Fin.elim0

end Measurability

end Language

end FirstOrder
