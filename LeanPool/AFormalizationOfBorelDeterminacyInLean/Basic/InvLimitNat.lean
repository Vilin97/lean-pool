/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.MiscCat
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.InvLimitNat

Auxiliary declarations for the Borel determinacy formalization.
-/


open CategoryTheory

universe u u1 u2
section «Preorder»
variable {X Y : Type u} [Preorder X] [Preorder Y] {x y : X}
lemma eq_homOfLE (f : x ⟶ y) : f = homOfLE (leOfHom f) := by apply Subsingleton.elim
@[simp] lemma map_eq_homOfLE (F : X ⥤ Y) (f : x ⟶ y) :
  F.map f = homOfLE (leOfHom (F.map f)) := by apply Subsingleton.elim
end «Preorder»

variable {C : Type u2} [Category.{u1, u2} C]
lemma heq_eqToHom {a b c d : C} (ab : a = b) (bc : b = c) (cd : c = d) :
  HEq (eqToHom ab) (eqToHom cd) := by
  subst ab bc cd; rfl
lemma left_eqToHom_iff_heq {W X Y : C} (f : W ⟶ X) (g : Y ⟶ X) (h : W = Y) :
  f = eqToHom h ≫ g ↔ HEq f g := by cases h; simp
lemma congr_comp {a b b' c d : C} (f : c ⟶ d) {g : b ⟶ c} {g' : b' ⟶ c} {h : a ⟶ b} {h' : a ⟶ b'}
  (H : h ≫ g = h' ≫ g') : h ≫ g ≫ f = h' ≫ g' ≫ f := by
  replace H := congr_fun (congr_arg CategoryStruct.comp H) f
  conv at H => simp
  exact H
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def recComp m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) : F (m + n) ⟶ F m := by
  induction n with
  | zero => exact 𝟙 (F m)
  | succ n ih => exact f (m + n) ≫ ih
lemma recComp_induction (p : ∀ ⦃c d⦄, (c ⟶ d) → Prop) (pid : ∀ c, p (𝟙 c))
  (pcomp : ∀ {c d e} (f : c ⟶ d) (g : d ⟶ e), p f → p g → p (f ≫ g)) m n {F : ℕ → C}
  (f : ∀ n, F (n + 1) ⟶ F n) (h : ∀ n, p (f (m + n))) : p (recComp m n f) := by
  induction n with
  | zero => exact pid _
  | succ n ih => exact pcomp _ _ (h _) ih
lemma recComp_iso m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : ∀ n, IsIso (f (m + n))) :
  IsIso (recComp m n f) := by
  apply recComp_induction <;> (intros; infer_instance)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def recCompOfLE {m n} (h : m ≤ n) {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) : F n ⟶ F m :=
  eqToHom (by simp [h]) ≫ recComp m (n - m) f
@[simp] lemma recComp.eq_zero m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : n = 0) :
  recComp m n f = eqToHom (by subst h; rfl) := by subst h; rfl
@[simp] lemma recCompOfLE.refl n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) :
  recCompOfLE (le_refl n) f = 𝟙 (F n) := by simp [recCompOfLE]
@[simp] lemma recComp.sum m n p {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) :
  recComp (m + n) p f ≫ recComp m n f
  = eqToHom (by simp [Nat.add_assoc]) ≫ recComp m (n + p) f := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [recComp, Nat.recAux, Category.assoc] at *
    rw [ih]
    apply congr_comp
    symm
    apply (IsIso.eq_inv_comp _).mp
    simp only [Nat.add_eq, inv_eqToHom]
    apply (conj_eqToHom_iff_heq _ _ _ _).mpr
    all_goals
      congr 1
      simp [Nat.add_assoc]
@[simp] lemma recComp.eq_sum m n p q {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n)
  (h : p = m + n) :
  recComp p q f ≫ eqToHom (by rw [h]) ≫ recComp m n f
  = eqToHom (by rw [h]; congr 1; simp [Nat.add_assoc]) ≫ (recComp m (n + q) f) := by subst h; simp
@[simp] lemma recCompOfLE.trans m n p {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n)
  (h1 : m ≤ n) (h2 : n ≤ p) :
  recCompOfLE h2 f ≫ recCompOfLE h1 f = recCompOfLE (le_trans h1 h2) f := by
  conv => simp [recCompOfLE]
  rw [recComp.eq_sum]
  · simp only [eqToHom_trans_assoc]
    apply (IsIso.eq_inv_comp _).mp
    · simp only [inv_eqToHom, eqToHom_trans_assoc]
      apply (left_eqToHom_iff_heq _ _ _).mpr
      · congr
        omega
      · omega
@[simp] lemma recComp.eq_one m n {F : ℕ → C} (f : ∀ n, F (n + 1) ⟶ F n) (h : n = 1) :
  eqToHom (by rw [h]) ≫ recComp m n f = f m := by subst h; simp [recComp]
@[simp] lemma recComp.functor m n (F : ℕᵒᵖ ⥤ C) :
  recComp m n (F := F.obj ∘ Opposite.op) (fun n ↦ F.map (homOfLE (Nat.le_succ n)).op)
  = F.map (homOfLE (Nat.le_add_right m n)).op := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [recComp, Nat.recAux, Function.comp_apply, Nat.succ_eq_add_one,
      homOfLE_leOfHom] at *
    rw [ih, ← F.map_comp]
    congr 1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def natFreeCat : (ℕᵒᵖ ⥤ C) ≃ ((O : ℕ → C) × (∀ n, O (n + 1) ⟶ O n)) where
  toFun F := ⟨F.obj ∘ Opposite.op, fun n ↦ F.map (homOfLE (Nat.le_succ n)).op⟩
  invFun := fun ⟨O, F⟩ ↦ {
    obj := O ∘ Opposite.unop
    map := @fun m n ↦ fun h ↦
      eqToHom (by simp [leOfHom h.unop]) ≫ (recComp n.unop (m.unop-n.unop) F)
    map_comp := by
      intros m n k h1 h2; conv => simp [leOfHom h2.unop]
      congr 1
      · simp [Nat.add_sub_sub_of_le, leOfHom h1.unop, leOfHom h2.unop,
          leOfHom (h1 ≫ h2).unop]
      · apply heq_eqToHom
        all_goals
          simp [leOfHom (h1 ≫ h2).unop]
      · congr
        simp [Nat.add_sub_sub_of_le, leOfHom h1.unop, leOfHom h2.unop]
  }
  left_inv F := by
    apply CategoryTheory.Functor.ext
    · intros m n h
      conv => simp
      symm
      apply (left_eqToHom_iff_heq _ _ _).mpr
      congr 1
      · simp [leOfHom h.unop]
      · apply Subsingleton.helim
        congr
        all_goals simp [leOfHom h.unop]
    · intro _
      rfl
  right_inv _ := by ext <;> simp
@[simp] lemma natFreeCat_apply_symm_apply (x : (O : ℕ → C) × (∀ n, O (n + 1) ⟶ O n)) :
  (natFreeCat (natFreeCat.symm x)).2 = x.2 := by
  congr; rw [Equiv.apply_symm_apply]

variable {C : Type u2} [Category.{u1, u2} C]
lemma isIso_map_nat (F : ℕᵒᵖ ⥤ C) {m}
  (hF : ∀ n ≥ m, IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
  ∀ {c d : ℕᵒᵖ} (f : c ⟶ d), d.1 ≥ m → IsIso (F.map f) := by
  rintro ⟨c⟩ ⟨d⟩ ⟨f⟩ h; obtain ⟨k, rfl⟩ := le_iff_exists_add.mp (leOfHom f)
  erw [← recComp.functor]; have hf : ∃ h, f = homOfLE h := ⟨_, eq_homOfLE f⟩
  obtain ⟨hf, rfl⟩ := hf; apply recComp_iso; intro _; apply hF; omega
lemma nat_add_initial {F : ℕᵒᵖ ⥤ C} {s : Limits.Cone F} (hs : Limits.IsLimit s)
  n (hn : ∀ k ≥ n, IsIso (F.map (homOfLE (Nat.le_succ k)).op)) k (hk : n ≤ k) :
  IsIso (s.π.app (Opposite.op k)) := by
  apply Functor.IsEventuallyConstantTo.isIso_π_of_isLimit _ hs
  intro c f
  apply isIso_map_nat
  · exact hn
  · exact hk
