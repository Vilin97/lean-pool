/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Functors out of the natural numbers from step data

A sequence of objects and one-step transition morphisms assembles
into a functor from `ℕ` — the shape of the Key Lemma's
δ-multiplication colimit.  The map on an arbitrary inequality is
defined by recursion on its length, with the composition law
proved once and the one-step computation exposed as a simp lemma.
-/

namespace RS

open CategoryTheory

universe v u

variable {D : Type u}

/-- The morphism of a chain along an inequality, by recursion on
its length. -/
noncomputable def chainMap [Category.{v} D]
    (B : ℕ → D) (δ : ∀ n, B n ⟶ B (n + 1)) :
    ∀ {m n : ℕ}, m ≤ n → (B m ⟶ B n) := fun {m} {_} h =>
  Nat.leRecOn h (fun {k} f => f ≫ δ k) (𝟙 (B m))

@[simp]
theorem chainMap_self [Category.{v} D]
    (B : ℕ → D) (δ : ∀ n, B n ⟶ B (n + 1))
    (n : ℕ) : chainMap B δ (le_refl n) = 𝟙 (B n) :=
  Nat.leRecOn_self _

theorem chainMap_succ_of_le [Category.{v} D]
    (B : ℕ → D)
    (δ : ∀ n, B n ⟶ B (n + 1)) {m n : ℕ} (h : m ≤ n)
    (h' : m ≤ n + 1) :
    chainMap B δ h' = chainMap B δ h ≫ δ n :=
  Nat.leRecOn_succ h _

@[simp]
theorem chainMap_le_succ [Category.{v} D]
    (B : ℕ → D)
    (δ : ∀ n, B n ⟶ B (n + 1)) (n : ℕ) :
    chainMap B δ (Nat.le_succ n) = δ n := by
  rw [chainMap_succ_of_le B δ (le_refl n), chainMap_self,
    Category.id_comp]

theorem chainMap_trans [Category.{v} D]
    (B : ℕ → D) (δ : ∀ n, B n ⟶ B (n + 1))
    {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    chainMap B δ (h₁.trans h₂) =
      chainMap B δ h₁ ≫ chainMap B δ h₂ := by
  induction n, h₂ using Nat.le_induction with
  | base =>
    rw [chainMap_self, Category.comp_id]
  | succ n hmn ih =>
    rw [chainMap_succ_of_le B δ hmn,
      chainMap_succ_of_le B δ (h₁.trans hmn), ih,
      Category.assoc]

/-- The functor out of `ℕ` assembled from objects and one-step
transitions. -/
noncomputable def chainFunctor [Category.{v} D]
    (B : ℕ → D)
    (δ : ∀ n, B n ⟶ B (n + 1)) : ℕ ⥤ D where
  obj := B
  map f := chainMap B δ (leOfHom f)
  map_id n := chainMap_self B δ n
  map_comp f g :=
    chainMap_trans B δ (leOfHom f) (leOfHom g)

@[simp]
theorem chainFunctor_obj [Category.{v} D]
    (B : ℕ → D) (δ : ∀ n, B n ⟶ B (n + 1))
    (n : ℕ) : (chainFunctor B δ).obj n = B n :=
  rfl

@[simp]
theorem chainFunctor_map_le_succ [Category.{v} D]
    (B : ℕ → D)
    (δ : ∀ n, B n ⟶ B (n + 1)) (n : ℕ) :
    (chainFunctor B δ).map (homOfLE (Nat.le_succ n)) = δ n :=
  chainMap_le_succ B δ n

end RS
