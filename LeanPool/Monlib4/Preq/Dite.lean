/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
 # Some stuff on dites
-/

theorem ite_eq_ite_iff {α : Type _} (a b c : α) :
    (∀ {p : Prop} [hp : Decidable p], @ite α p hp a c
      = @ite α p hp b c) ↔ a = b :=
  by
  constructor
  · intro h
    exact h (p := True)
  · intro h
    simp [h]

theorem ite_eq_ite_iff_of_pi {n α : Type _} [DecidableEq n] (a b c : n → α) :
    (∀ i j : n, ite (i = j) (a i) (c i) = ite (i = j) (b i) (c i)) ↔ a = b :=
  by
  constructor
  · intro h
    funext i
    specialize h i i
    simpa using h
  · intro h
    rw [h]
    intro i j
    rfl


-- theorem dite_add_dite {α : Type _} [Add α] (P : Prop) [Decidable P]
--     (a b : P → α) (c d : ¬P → α) :
--     ((dite P (fun x => a x) fun x => c x) + dite P (fun x => b x) fun x => d x) =
--       dite P (fun x => a x + b x) fun x => c x + d x :=
--   by
--   rw [eq_comm]
--   simp only [dite_eq_iff']
--   constructor
--   · intro h
--     simp only [h, dif_pos]
--   · intro h
--     simp only [h, dif_neg, not_false_iff]

theorem hMul_dite {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (a * dite P (fun x => b x) fun x => c x) = dite P (fun x => a * b x) fun x => a * c x :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_hMul {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (dite P (fun x => b x) fun x => c x) * a = dite P (fun x => b x * a) fun x => c x * a :=
  by
  rw [eq_comm]
  simp only [dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_boole_add {α : Type _} [AddZeroClass α] (P : Prop) [Decidable P] (a b : P → α) :
    (dite P (fun x => a x + b x) fun _ => 0) =
      (dite P (fun x => a x) fun _ => 0) + dite P (fun x => b x) fun _ => 0 :=
  by rw [dite_add_dite, add_zero]

theorem dite_boole_smul {α β : Type _} [Zero α] [SMulZeroClass β α] (P : Prop) [Decidable P]
    (a : P → α) (r : β) :
    (dite P (fun x => r • a x) fun _ => 0) = r • dite P (fun x => a x) fun _ => 0 := by
  rw [smul_dite, smul_zero]

theorem star_dite (P : Prop) [Decidable P] {α : Type _} [InvolutiveStar α] (a : P → α)
    (b : ¬P → α) :
    star (dite P (fun i => a i) fun i => b i) = dite P (fun i => star (a i)) fun i => star (b i) :=
  by
  rw [eq_comm, dite_eq_iff']
  constructor
  · intro h
    simp only [h, dif_pos]
  · intro h
    simp only [h, dif_neg, not_false_iff]

theorem dite_tmul {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : P → N₁) (x₂ : N₂) :
    (dite P (fun h => x₁ h) fun _ => 0) ⊗ₜ[R] x₂ = dite P (fun h => x₁ h ⊗ₜ[R] x₂) fun _ => 0 := by
  split_ifs <;> simp

theorem tmul_dite {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : N₁) (x₂ : P → N₂) :
    (x₁ ⊗ₜ[R] dite P (fun h => x₂ h) fun _ => 0) = dite P (fun h => x₁ ⊗ₜ[R] x₂ h) fun _ => 0 := by
  split_ifs <;> simp

theorem LinearMap.apply_dite {R H₁ H₂ : Type _} [Semiring R] [AddCommMonoid H₁] [AddCommMonoid H₂]
    [Module R H₁] [Module R H₂] (f : H₁ →ₗ[R] H₂) (P : Prop) [Decidable P] (a : P → H₁)
    (b : ¬P → H₁) :
    f (dite P (fun h => a h) fun h => b h) = dite P (fun h => f (a h)) fun h => f (b h) := by
  split_ifs <;> simp

lemma dite_apply' {i β : Type*} {α : i → Type*} (P : Prop) [Decidable P]
  {j : i} (f : P → (β → α j)) [Zero (α j)] (a : β) :
  (if h : P then (f h) else 0) a = if h : P then f h a else 0 :=
by aesop
