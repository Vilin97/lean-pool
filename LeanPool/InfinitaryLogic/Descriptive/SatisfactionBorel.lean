/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorelOn
/-!
# Satisfaction of Lω₁ω Formulas is Borel

This file proves that for a countable relational language L, the set of codes in
`StructureSpace L` satisfying a given Lω₁ω sentence is measurable (Borel).

## Main Definitions

- `ModelsOfBounded`: The set of codes where a bounded formula is realized.
- `ModelsOf`: The set of codes where a sentence is realized.

## Main Results

- `modelsOfBounded_measurableSet`: Satisfaction of any bounded Lω₁ω formula is measurable.
- `modelsOf_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
-/

universe u v u'

namespace FirstOrder

namespace Language

open Structure MeasureTheory

variable {L : Language.{u, v}}

section Measurability

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The set of codes where a bounded formula is realized, given variable assignments. -/
def ModelsOfBounded
    {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    Set (StructureSpace L) :=
  {c | @BoundedFormulaω.Realize L ℕ c.toStructure α n φ v xs}

/-- The set of codes where a sentence is realized. -/
def ModelsOf (φ : L.Sentenceω) : Set (StructureSpace L) :=
  ModelsOfBounded φ Empty.elim Fin.elim0

omit [Countable (Σ l, L.Relations l)] in
private theorem modelsOfBounded_falsum {α : Type u'} {n : ℕ}
    (v : α → ℕ) (xs : Fin n → ℕ) :
    ModelsOfBounded (L := L) BoundedFormulaω.falsum v xs = ∅ := by
  ext c; simp [ModelsOfBounded]

omit [Countable (Σ l, L.Relations l)] in
private theorem modelsOfBounded_imp {α : Type u'} {n : ℕ}
    (φ ψ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    ModelsOfBounded (φ.imp ψ) v xs =
    (ModelsOfBounded φ v xs)ᶜ ∪ (ModelsOfBounded ψ v xs) := by
  ext c
  simp only [ModelsOfBounded, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
  exact Iff.intro (fun h => by tauto) (fun h => by tauto)

omit [Countable (Σ l, L.Relations l)] in
private theorem modelsOfBounded_all {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α (n + 1)) (v : α → ℕ) (xs : Fin n → ℕ) :
    ModelsOfBounded φ.all v xs =
    ⋂ (m : ℕ), ModelsOfBounded φ v (Fin.snoc xs m) := by
  ext c; simp only [ModelsOfBounded, Set.mem_ofPred_eq, Set.mem_iInter]; rfl

omit [Countable (Σ l, L.Relations l)] in
private theorem modelsOfBounded_iSup {α : Type u'} {n : ℕ}
    (φs : ℕ → L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    ModelsOfBounded (BoundedFormulaω.iSup φs) v xs =
    ⋃ (i : ℕ), ModelsOfBounded (φs i) v xs := by
  ext c; simp only [ModelsOfBounded, Set.mem_ofPred_eq, Set.mem_iUnion]; rfl

omit [Countable (Σ l, L.Relations l)] in
private theorem modelsOfBounded_iInf {α : Type u'} {n : ℕ}
    (φs : ℕ → L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    ModelsOfBounded (BoundedFormulaω.iInf φs) v xs =
    ⋂ (i : ℕ), ModelsOfBounded (φs i) v xs := by
  ext c; simp only [ModelsOfBounded, Set.mem_ofPred_eq, Set.mem_iInter]; rfl

omit [Countable (Σ l, L.Relations l)] in
/-- Satisfaction of any bounded Lω₁ω formula in a countable relational language
is measurable on the structure space. -/
theorem modelsOfBounded_measurableSet
    {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    MeasurableSet (ModelsOfBounded φ v xs) := by
  induction φ with
  | falsum =>
    rw [modelsOfBounded_falsum]; exact MeasurableSet.empty
  | @equal _ t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    -- Equality of variables is determined by the assignment, not the code.
    -- ModelsOfBounded is univ when the variable values agree, ∅ otherwise.
    by_cases h : Sum.elim v xs x₁ = Sum.elim v xs x₂
    · convert MeasurableSet.univ (α := StructureSpace L)
      ext c
      simp only [Set.mem_ofPred_eq, ModelsOfBounded, Set.mem_univ, iff_true]
      let := c.toStructure
      simp [BoundedFormulaω.Realize, Term.realize, h]
    · convert MeasurableSet.empty (α := StructureSpace L)
      ext c
      simp only [Set.mem_ofPred_eq, ModelsOfBounded, Set.mem_empty_iff_false, iff_false]
      intro hc
      apply h
      let := c.toStructure
      simp [BoundedFormulaω.Realize, Term.realize] at hc
      exact hc
  | @rel _ l R ts =>
    -- Each term ts i is a variable; extract the variable index for each i
    -- so the realized tuple is Sum.elim v xs applied to those indices (code-independent).
    choose xs' hxs' using fun i => Term.eq_var_of_isRelational (ts i)
    -- xs' i is the variable index for the i-th term; ts i = var (xs' i)
    -- The realized tuple tup i = Sum.elim v xs (xs' i) is code-independent.
    set tup : Fin l → ℕ := fun i => Sum.elim v xs (xs' i)
    -- The realized tuple equals tup since each term is a variable
    have htup : ∀ (c : StructureSpace L),
        letI := c.toStructure
        (fun i => (ts i).realize (Sum.elim v xs)) = tup := by
      intro c
      let := c.toStructure
      funext i
      simp [hxs' i, Term.realize_var, tup]
    convert measurableSet_relHolds (L := L) ⟨⟨l, R⟩, tup⟩ using 1
    ext c
    simp only [Set.mem_ofPred_eq, ModelsOfBounded]
    constructor
    · intro hc
      let := c.toStructure
      have hrel : @Structure.RelMap L ℕ c.toStructure l R
          (fun i => (ts i).realize (Sum.elim v xs)) := hc
      rw [StructureSpace.relMap_toStructure] at hrel
      rwa [htup] at hrel
    · intro hc
      let := c.toStructure
      show @Structure.RelMap L ℕ c.toStructure l R
          (fun i => (ts i).realize (Sum.elim v xs))
      rw [StructureSpace.relMap_toStructure, htup]
      exact hc
  | imp φ ψ ih_φ ih_ψ =>
    rw [modelsOfBounded_imp]; exact (ih_φ xs).compl.union (ih_ψ xs)
  | all φ ih =>
    rw [modelsOfBounded_all]; exact MeasurableSet.iInter (fun m => ih (Fin.snoc xs m))
  | iSup φs ih =>
    rw [modelsOfBounded_iSup]; exact MeasurableSet.iUnion (fun i => ih i xs)
  | iInf φs ih =>
    rw [modelsOfBounded_iInf]; exact MeasurableSet.iInter (fun i => ih i xs)

omit [Countable (Σ l, L.Relations l)] in
/-- Satisfaction of any Lω₁ω sentence in a countable relational language
is measurable on the structure space. -/
theorem modelsOf_measurableSet (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) :=
  modelsOfBounded_measurableSet φ Empty.elim Fin.elim0

end Measurability

end Language

end FirstOrder
