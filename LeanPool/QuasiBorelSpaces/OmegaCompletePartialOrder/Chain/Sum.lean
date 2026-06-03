/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Sum.Order
import Mathlib.Order.OmegaCompletePartialOrder


/-!
# Chain utilities for coproducts of ωCPOs

This file provides utilities for working with chains in sum types,
which are used to construct the ωCPO instance for coproducts.
-/

namespace OmegaCompletePartialOrder.Chain.Sum

variable {A B : Type*}
variable [Preorder A] [Preorder B]

/-- Left injection for chains of sums. -/
def inl (c : Chain A) : Chain (A ⊕ B) := c.map ⟨.inl, Sum.inl_mono⟩

@[simp]
lemma inl_coe (c : Chain A) (n : ℕ) : inl (B := B) c n = .inl (c n) := by rfl

/-- Right injection for chains of sums. -/
def inr (c : Chain B) : Chain (A ⊕ B) := c.map ⟨.inr, Sum.inr_mono⟩

@[simp]
lemma inr_coe (c : Chain B) (n : ℕ) : inr (A := A) c n = .inr (c n) := by rfl

/-- Projects left values out of a chain. -/
def projl [hA : Inhabited A] (c : Chain (A ⊕ B)) : Chain A where
  toFun n := Sum.elim id (fun _ ↦ default) (c n)
  monotone' := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    have hc := (OrderHomClass.mono c) (Nat.le_add_right n 1)
    cases hn : c n with
    | inl x =>
      cases hn₁ : c (n + 1) with
      | inl y =>
        simp only [hn, hn₁, Sum.inl_le_inl_iff] at hc
        simp only [Sum.elim_inl, id_eq, hc]
      | inr y => simp only [hn, hn₁, Sum.not_inl_le_inr] at hc
    | inr x =>
      cases hn₁ : c (n + 1) with
      | inl y => simp only [hn, hn₁, Sum.not_inr_le_inl] at hc
      | inr y => simp only [Sum.elim_inr, le_refl]

@[simp]
lemma projl_coe [Inhabited A] (c : Chain (A ⊕ B)) (n : ℕ) :
    projl c n = Sum.elim id (fun _ ↦ default) (c n) := by
  rfl

/-- Projects right values out of a chain. -/
def projr [hB : Inhabited B] (c : Chain (A ⊕ B)) : Chain B :=
  projl (c.map
    ⟨ Sum.swap
    , by
      intro x y h
      cases h with
      | inl h => simp only [Sum.swap_inl, ge_iff_le, Sum.inr_le_inr_iff, h]
      | inr h => simp only [Sum.swap_inr, ge_iff_le, Sum.inl_le_inl_iff, h]
    ⟩)

@[simp]
lemma projr_coe [Inhabited B] (c : Chain (A ⊕ B)) (n : ℕ) :
    projr c n = Sum.elim (fun _ ↦ default) id (c n) := by
  cases h : c n with
  | inl _ =>
      simp only [
        projr, projl_coe, coe_map, OrderHom.coe_mk, Function.comp_apply, h, Sum.swap_inl,
        Sum.elim_inr, Sum.elim_inl]
  | inr _ =>
      simp only [
        projr, projl_coe, coe_map, OrderHom.coe_mk, Function.comp_apply, h, Sum.swap_inr,
        Sum.elim_inl, id_eq, Sum.elim_inr]

/-- Splits a chain of sums into a sum of chains. -/
def distrib (c : Chain (A ⊕ B)) : Chain A ⊕ Chain B :=
  Sum.elim
    (fun d ↦
      let : Inhabited A := ⟨d⟩
      .inl (projl c))
    (fun d ↦
      let : Inhabited B := ⟨d⟩
      .inr (projr c))
    (c 0)

@[simp]
lemma distrib_inl (c : Chain A) : distrib (inl (B := B) c) = .inl c := by rfl

@[simp]
lemma distrib_inr (c : Chain B) : distrib (inr (A := A) c) = .inr c := by rfl

@[elab_as_elim]
lemma distrib_cases
    {p : Chain (A ⊕ B) → Prop}
    (inl : ∀ c, p (inl c))
    (inr : ∀ c, p (inr c))
    (c : Chain (A ⊕ B)) : p c := by
  suffices this : c = Sum.elim Sum.inl Sum.inr (distrib c) by
    rw [this]
    cases distrib c with
    | inl _ => apply inl
    | inr _ => apply inr
  apply Chain.ext
  funext n
  dsimp only [distrib]
  have := (OrderHomClass.mono c) (Nat.zero_le n)
  cases h₀ : c 0 with
  | inl x =>
    cases hₙ : c n with
    | inl y =>
      simp only [h₀, hₙ, Sum.inl_le_inl_iff] at this
      simp only [Sum.elim_inl]
      rw [inl_coe]
      simp only [projl_coe, hₙ, Sum.elim_inl, id_eq]
    | inr y => simp only [h₀, hₙ, Sum.not_inl_le_inr] at this
  | inr x =>
    cases hₙ : c n with
    | inl y => simp only [h₀, hₙ, Sum.not_inr_le_inl] at this
    | inr y =>
      simp only [h₀, hₙ] at this
      simp only [Sum.elim_inr]
      rw [inr_coe]
      simp only [projr_coe, hₙ, Sum.elim_inr, id_eq]

end OmegaCompletePartialOrder.Chain.Sum
