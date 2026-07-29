/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {α β E : Type*} [AddCommMonoid E] [TopologicalSpace E]
  [ContinuousAdd E]

/-- An extend by zero used in the Odlyzko-bound argument. -/
noncomputable def extendByZero (e : α → β) (f : α → E) (b : β) : E :=
  Function.extend e f 0 b

omit [TopologicalSpace E] [ContinuousAdd E] in
lemma extendByZero_apply (e : α → β) (he : Function.Injective e)
    (f : α → E) (a : α) :
    extendByZero e f (e a) = f a := by
  exact he.extend_apply f 0 a

omit [TopologicalSpace E] [ContinuousAdd E] in
lemma extendByZero_eq_zero_of_not_mem_range (e : α → β) (f : α → E)
    {b : β} (hb : b ∉ Set.range e) :
    extendByZero e f b = 0 := by
  exact Function.extend_apply' (f := e) f 0 b hb

omit [ContinuousAdd E] in
theorem hasSum_extendByZero (e : α → β) (he : Function.Injective e)
    {f : α → E} {a : E} (hf : HasSum f a) :
    HasSum (extendByZero e f) a := by
  unfold extendByZero
  simp_all

omit [ContinuousAdd E] in
theorem summable_extendByZero (e : α → β) (he : Function.Injective e)
    {f : α → E} (hf : Summable f) :
    Summable (extendByZero e f) := by
  unfold extendByZero
  simp_all

end NumberField.Odlyzko
