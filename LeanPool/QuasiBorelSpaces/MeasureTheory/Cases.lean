/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Cases

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Cases`.
-/


open scoped MeasureTheory

namespace MeasureTheory

variable
  {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {I : Type*} [Countable I]

lemma measurable_cases
    {ix : A → I} {f : I → A → B}
    (hix : Measurable[_, ⊤] ix) (hf : ∀ i, Measurable (f i))
    : Measurable (fun x ↦ f (ix x) x) := by
  intro s hs
  have : ((fun x ↦ f (ix x) x) ⁻¹' s) = ⋃i, { x | ix x ∈ ({i} : Set I) } ∩ { x | f i x ∈ s } := by
    ext
    simp only [
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq, exists_eq_left']
  rw [this]
  refine MeasurableSet.iUnion fun i ↦ MeasurableSet.inter ?_ ?_
  · exact hix MeasurableSpace.measurableSet_top
  · exact hf i hs


@[fun_prop]
lemma measurable_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : Measurable p)
    : Measurable (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply measurable_cases (f := fun p _ ↦ decide p) hp
  simp only [measurable_const, implies_true]

@[fun_prop]
lemma measurable_dite
    {p : A → Prop} (hp₁ : Measurable p) (hp₂ : DecidablePred p)
    {f : (x : A) → p x → B} (hf : Measurable fun x : Subtype p ↦ f x.val x.property)
    {g : (x : A) → ¬p x → B} (hg : Measurable fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property)
    : Measurable (fun x ↦ if h : p x then f x h else g x h) := by
  let f' (x : Subtype p) := f x.val x.property
  let g' (x : Subtype fun x ↦ ¬p x) := g x.val x.property
  change Measurable fun x ↦ if h : x ∈ { x | p x } then f' ⟨x, h⟩ else g' ⟨x, h⟩
  apply Measurable.dite
  · exact hf
  · exact hg
  · simp only [measurableSet_setOf]
    exact hp₁

end MeasureTheory
