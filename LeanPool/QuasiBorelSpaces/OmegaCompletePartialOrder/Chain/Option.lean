/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Option.Instances
import Mathlib.Data.Nat.Find
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Option`.
-/


variable {A : Type*} [Preorder A]

namespace OmegaCompletePartialOrder.Chain.Option

/-- A chain of `none`s. -/
def none : Chain (Option A) where
  toOrderHom := ⟨fun _ ↦ .none, monotone_const⟩

@[simp]
lemma none_coe {n} : none (A := A) n = .none := by rfl

/--
Lifts a chain of values to a chain of `some`s,
with the specified number of leading `none`s.
-/
def some (i : ℕ) (c : Chain A) : Chain (Option A) where
  toFun n := if n < i then .none else c (n - i)
  monotone' n₁ n₂ hn := by
    dsimp only
    by_cases hn₁ : n₁ < i
    · grind
    · by_cases hn₂ : n₂ < i
      · grind
      · simp only [hn₁, ↓reduceIte, hn₂, Option.some_le_some]
        apply (OrderHomClass.mono c)
        grind

@[simp]
lemma some_coe (i n : ℕ) (c : Chain A)
    : some i c n = if n < i then .none else .some (c (n - i)) := by
  rfl

/--
Given a proof that a `Chain` contains a `some` value, we can construct a `Chain`
that only contains the `some` values.
-/
noncomputable def project (c : Chain (Option A)) (h : ∃ n, (c n).isSome) : Chain A :=
  have : Nonempty A := ⟨Option.get _ (Nat.find_spec h)⟩
  ⟨fun n ↦ (c (Nat.find h + n)).getD this.some, by
    intro i j hij
    dsimp only
    have hhij := (OrderHomClass.mono c) (by grind : Nat.find h + i ≤ Nat.find h + j)
    have hhi := (OrderHomClass.mono c) (by grind : Nat.find h ≤ Nat.find h + i)
    have hhj := (OrderHomClass.mono c) (by grind : Nat.find h ≤ Nat.find h + j)
    have hh := Nat.find_spec h
    cases hi : c (Nat.find h + i) with
    | none =>
      simp only [hi, Option.le_none] at hhi
      simp only [Option.isSome_iff_exists, hhi, Option.isSome_none, Bool.false_eq_true] at hh
    | some x =>
    cases hj : c (Nat.find h + j) with
    | none =>
      simp only [hj, Option.le_none] at hhj
      simp only [Option.isSome_iff_exists, hhj, Option.isSome_none, Bool.false_eq_true] at hh
    | some y =>
    simp only [hi, hj, Option.some_le_some] at hhij
    simp only [Option.getD_some, hhij]⟩

@[simp]
lemma project_coe
    (c : Chain (Option A)) (h : ∃ n, (c n).isSome) (n : ℕ)
    : project c h n
    = have : Nonempty A := ⟨Option.get _ (Nat.find_spec h)⟩
      (c (Nat.find h + n)).getD this.some := by
  rfl

/-- Turns a `Chain` of `Option`s into an equivalent `Option`al `Chain`. -/
noncomputable def distrib (c : Chain (Option A)) : Option (Chain A) :=
  open Classical in
  if h : ∃n, (c n).isSome
  then .some (project c h)
  else .none

@[simp]
lemma distrib_none : distrib (none : Chain (Option A)) = .none := by
  simp only [distrib, none_coe, Option.isSome_none, Bool.false_eq_true, exists_const, ↓reduceDIte]

@[simp]
lemma distrib_some (i : ℕ) (c : Chain A) : distrib (some i c) = .some c := by
  simp only [
    distrib, some_coe, Option.isSome_ite', not_lt,
    Option.dite_none_right_eq_some, Option.some.injEq]
  use ⟨i, le_rfl⟩
  ext n
  simp only [project_coe, some_coe, Option.isSome_ite', not_lt]
  have : Nat.find (⟨i, le_rfl⟩ : ∃ n, (i ≤ ·) n) = i := by
    simp only [Nat.find_eq_iff, le_refl, not_le, imp_self, implies_true, and_self]
  grind

@[elab_as_elim]
lemma distrib_cases
    {p : Chain (Option A) → Prop}
    (none : p none)
    (some : ∀ i c, p (some i c))
    (c : Chain (Option A)) : p c := by
  classical
  let ix := if h : ∃n, (c n).isSome then Nat.find h else 0
  suffices c = Option.elim (distrib c) Option.none (Option.some ix) by
    rw [this]
    cases hc : distrib c with
    | none => apply none
    | some _ => apply some
  ext n
  by_cases h : ∃n, (c n).isSome
  · simp only [
      distrib, h, ↓reduceDIte, Option.elim_some, some_coe, project_coe,
      Option.ite_none_left_eq_some, not_lt, Option.some.injEq, ix]
    by_cases hn : Nat.find h ≤ n
    · simp only [hn, Nat.add_sub_cancel', true_and]
      cases hc : c n with
      | none =>
        exfalso
        have := (OrderHomClass.mono c) hn
        cases hc' : c (Nat.find h) with
        | none => grind
        | some val => grind
      | some val => simp only [Option.some.injEq, Option.getD_some]
    · simp only [hn, false_and, iff_false]
      simp only [
        Nat.find_le_iff, not_exists, not_and, Bool.not_eq_true,
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hn
      simp only [le_refl, hn, reduceCtorEq, not_false_eq_true]
  · simp only [distrib, h, ↓reduceDIte, Option.elim_none, none_coe, reduceCtorEq, iff_false]
    grind

end OmegaCompletePartialOrder.Chain.Option
