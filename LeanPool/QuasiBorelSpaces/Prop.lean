/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Pi
import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.Prod
import LeanPool.QuasiBorelSpaces.Subtype

/-!
# LeanPool.QuasiBorelSpaces.Prop

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Prop`.
-/


variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {I : Sort*} [Countable I]

namespace QuasiBorelSpace.Prop

example : DiscreteQuasiBorelSpace Prop := inferInstance

@[fun_prop]
lemma isHom_ite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : A → B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ if p x then f x else g x) := by
  classical
  have (x : A) : inst x = Classical.dec _ := by subsingleton
  conv => enter [1, x]; rw [this]
  apply isHom_cases (f := fun b x ↦ if b then f x else g x) hp
  intro
  split_ifs <;> assumption

@[fun_prop]
lemma isHom_not
    {f : A → Prop} (hf : IsHom f)
    : IsHom (fun x ↦ ¬f x) := by
  fun_prop

@[fun_prop]
lemma isHom_and
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∧ g x) := by
  fun_prop

@[fun_prop]
lemma isHom_or
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∨ g x) := by
  fun_prop

lemma isHom_imp
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x → g x) := by
  exact isHom_comp' (f := fun x ↦ x.1 → x.2) (g := fun x ↦ (f x, g x))
    (by simp only [isHom_of_discrete_countable]) (by fun_prop)

@[fun_prop]
lemma isHom_iff
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ↔ g x) := by
  fun_prop

lemma isHom_forall
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∀i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.forall
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

@[fun_prop]
lemma isHom_exists
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∃i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.exists
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

@[fun_prop]
lemma isHom_dite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : (x : A) → p x → B} (hf : IsHom fun x : Subtype p ↦ f x.val x.property)
    {g : (x : A) → ¬p x → B} (hg : IsHom fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property)
    : IsHom (fun x ↦ if h : p x then f x h else g x h) := by
  classical
  have : inst = fun x ↦ Classical.dec _ := by subsingleton
  subst this
  wlog hp : Nonempty (Subtype p)
  · simp only [nonempty_subtype, not_exists] at hp
    simp only [hp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hp x⟩ : Subtype fun x ↦ ¬p x) := by fun_prop
    apply isHom_comp' hg this
  wlog hnp : Nonempty (Subtype fun x ↦ ¬p x)
  · simp only [nonempty_subtype, not_exists, Decidable.not_not] at hnp
    simp only [hnp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hnp x⟩ : Subtype p) := by fun_prop
    apply isHom_comp' hf this
  let f' := fun x : Subtype p ↦ f x.val x.property
  let g' := fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property
  let k q x :=
      if q
      then f' (if h : p x then ⟨x, h⟩ else Classical.arbitrary _)
      else g' (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary _)
  have {x}
      : (if h : p x then f x h else g x h)
      = if p x
        then f' (if h :  p x then ⟨x, h⟩ else Classical.arbitrary _)
        else g' (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary _) := by
    grind
  simp only [this]
  apply isHom_ite
  · fun_prop
  · apply isHom_comp' hf
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite <;> fun_prop
  · apply isHom_comp' hg
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite <;> fun_prop

@[fun_prop]
lemma isHom_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : IsHom p)
    : IsHom (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply isHom_cases (f := fun p _ ↦ decide p) <;> fun_prop

end QuasiBorelSpace.Prop
