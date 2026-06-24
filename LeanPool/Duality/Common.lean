/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Defs

/-!
# LeanPool.Duality.Common
-/

section finset_sums
variable {α β : Type*}

lemma Finset.subtype_univ_sum_eq_subtype_univ_sum {p q : α → Prop} (hpq : p = q)
    [Fintype { a : α // p a }] [Fintype { a : α // q a }] [AddCommMonoid β]
    {f : { a : α // p a } → β} {g : { a : α // q a } → β}
    (hfg : ∀ a : α, ∀ hpa : p a, ∀ hqa : q a, f ⟨a, hpa⟩ = g ⟨a, hqa⟩) :
    Finset.univ.sum f = Finset.univ.sum g := by
  subst hpq
  convert rfl
  rename_i x _
  obtain ⟨a, ha⟩ := x
  exact (hfg a ha ha).symm

lemma Finset.univ_sum_of_zero_when_not [Fintype α] [AddCommMonoid β]
    {f : α → β} (p : α → Prop) [DecidablePred p] (hpf : ∀ a : α, ¬(p a) → f a = 0) :
    Finset.univ.sum f = Finset.univ.sum (fun a : { a : α // p a } => f a.val) := by
  classical
  trans (Finset.univ.filter p).sum f
  · symm
    apply Finset.sum_subset_zero_on_sdiff
    · apply Finset.subset_univ
    · simpa
    · intros
      rfl
  · apply Finset.sum_subtype
    simp

end finset_sums


section logic_with_neq
variable {P Q : Prop}

lemma or_of_neq (hpq : P ≠ Q) : P ∨ Q := by tauto

lemma not_and_of_neq (hpq : P ≠ Q) : ¬(P ∧ Q) := by tauto

lemma neq_of_iff_neg (hpq : P ↔ ¬Q) : P ≠ Q := by tauto

lemma neg_iff_neg (hpq : P ↔ Q) : ¬P ↔ ¬Q := by tauto

end logic_with_neq


section notations

/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr


end notations


section miscellaneous

lemma le_of_nneg_add {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b c : α} (habc : a + b = c) (ha : 0 ≤ a) : b ≤ c := by aesop

/-- `change h to t` rewrites the hypothesis `h` to the definitionally equal type `t`. -/
macro "change " h:ident " to " t:term : tactic => `(tactic| change $t at $h:ident)

/-- `aeply t` is shorthand for `intro <;> apply t <;> aesop`, useful for proving universally
    quantified goals where each instance is dispatched by `aesop` after applying `t`. -/
macro "aeply" t:term : tactic => `(tactic| intro <;> apply $t <;> aesop)

end miscellaneous
