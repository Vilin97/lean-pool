/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# The first-order image inside `Lω₁ω`

`IsFirstOrder φ` says `φ` is `toLω` of an ordinary first-order formula — i.e. it contains no
infinitary node.

The point of the API is the **exact constructor equations**, especially

* `isFirstOrder_imp_iff` / `isFirstOrder_all_iff` — structural, both directions;
* `not_isFirstOrder_iInf` / `not_isFirstOrder_iSup` — the two negative facts.

Without these, every consumer that needs "this fragment contains no infinitary formula" re-does the
same `cases … <;> simp [toLω]` inversion. With them the HF fragment's closure fields become
one-liners.
-/

namespace FirstOrder.Language

universe u v u'

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

/-- `φ` is the `toLω`-image of a first-order formula: it has no infinitary node. -/
def BoundedFormulaω.IsFirstOrder (φ : L.BoundedFormulaω α n) : Prop :=
  ∃ φ₀ : L.BoundedFormula α n, φ₀.toLω = φ

namespace BoundedFormulaω







@[simp] theorem isFirstOrder_imp_iff {φ ψ : L.BoundedFormulaω α n} :
    (φ.imp ψ).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder := by
  constructor
  · rintro ⟨φ₀, hφ₀⟩
    cases φ₀ with
    | imp a b =>
      rw [BoundedFormula.toLω] at hφ₀
      cases hφ₀
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | all => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨a.imp b, rfl⟩

@[simp] theorem isFirstOrder_all_iff {φ : L.BoundedFormulaω α (n + 1)} :
    φ.all.IsFirstOrder ↔ φ.IsFirstOrder := by
  constructor
  · rintro ⟨φ₀, hφ₀⟩
    cases φ₀ with
    | all a =>
      rw [BoundedFormula.toLω] at hφ₀
      cases hφ₀
      exact ⟨a, rfl⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | imp => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  · rintro ⟨a, rfl⟩
    exact ⟨a.all, rfl⟩

/-- **No infinitary conjunction is first-order.**  This is the fact HF's closure fields need. -/
@[simp] theorem not_isFirstOrder_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    ¬ (BoundedFormulaω.iInf φs).IsFirstOrder := by
  rintro ⟨φ₀, hφ₀⟩
  cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])

/-- **No infinitary disjunction is first-order.** -/
@[simp] theorem not_isFirstOrder_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    ¬ (BoundedFormulaω.iSup φs).IsFirstOrder := by
  rintro ⟨φ₀, hφ₀⟩
  cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])

end BoundedFormulaω

end FirstOrder.Language
