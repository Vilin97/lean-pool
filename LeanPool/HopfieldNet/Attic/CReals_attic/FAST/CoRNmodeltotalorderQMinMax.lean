/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.Normed.Field.Lemmas

-- (*
-- Copyright © 2006-2008 Russell O’Connor

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- From Coq Require Import QArith_base.
-- Require Import CoRN.order.TotalOrder.

-- (**
-- ** Example of a Total Order: <Q, Qle, Qmin, Qmax>
-- *)

-- Definition Qlt_le_dec_fast x y : {x < y} + {y <= x}.
-- Proof.
--  change ({x ?= y = Lt}+{y<=x}).
--  cut (x ?= y <> Lt -> y <= x).
--   destruct (x?=y); intros H; (right; abstract(apply H; discriminate)) || (left; reflexivity).
--  refine (Qnot_lt_le _ _).
-- Defined.
set_option linter.unusedVariables false
/--
Decidable comparison for rationals: either `x < y` or `y ≤ x`.
-/
def Qlt_le_dec_fast (x y : ℚ) : (x < y) ∨  (y ≤ x) :=
  match lt_trichotomy x y with
  | Or.inl hlt => Or.inl hlt
  | Or.inr (Or.inl heq) => Or.inr (le_of_eq heq.symm)
  | Or.inr (Or.inr hgt) => Or.inr (le_of_lt hgt)

open Rat

-- Definition Qle_total x y : {x <= y} + {y <= x} :=
-- match Qlt_le_dec_fast x y with
-- | left p => left _ (Qlt_le_weak _ _ p)
-- | right p => right _ p
-- end.

/--
Total order for rationals: either `x ≤ y` or `y ≤ x`.
-/
def Qle_total (x y : ℚ) : (x ≤ y) ∨ (y ≤ x) :=
  match Qlt_le_dec_fast x y with
  | Or.inl hlt => Or.inl (le_of_lt hlt)
  | Or.inr hle => Or.inr hle

-- Lemma Qeq_le_def : forall x y, x == y <-> x <= y /\ y <= x.
-- Proof.
--  intros.
--  split.
--   intros H; rewrite -> H.
--   firstorder using Qle_refl.
--  firstorder using Qle_antisym.
-- Qed.

/--
For rationals, equality is equivalent to mutual ≤.
-/
theorem Qeq_le_def (x y : ℚ) : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · intro h
    rw [h]
    exact ⟨le_refl y, le_refl y⟩
  · intro ⟨hxy, hyx⟩
    exact le_antisymm hxy hyx

-- Definition Qmonotone : (Q -> Q) -> Prop := Default.monotone Qle.
-- Definition Qantitone : (Q -> Q) -> Prop := Default.antitone Qle.
-- Definition Qmin : Q -> Q -> Q := Default.min Q Qle Qle_total.
-- Definition Qmax : Q -> Q -> Q := Default.max Q Qle Qle_total.

/--
A function on rationals is monotone if it preserves ≤.
-/
def Qmonotone (f : ℚ → ℚ) : Prop := ∀ {x y : ℚ}, x ≤ y → f x ≤ f y

/--
A function on rationals is antitone if it reverses ≤.
-/
def Qantitone (f : ℚ → ℚ) : Prop := ∀ {x y : ℚ}, x ≤ y → f y ≤ f x

/--
Minimum of two rationals.
-/
def Qmin (x y : ℚ) : ℚ := if x ≤ y then x else y

/--
Maximum of two rationals.
-/
def Qmax (x y : ℚ) : ℚ := if x ≤ y then y else x

-- Definition Qmin_case :
--  forall x y (P : Q -> Type), (Qle x y -> P x) -> (Qle y x -> P y) -> P (Qmin x y) :=
--  Default.min_case Q Qle Qle_total.
-- Definition Qmax_case :
--  forall x y (P : Q -> Type), (Qle y x -> P x) -> (Qle x y -> P y) -> P (Qmax x y) :=
--  Default.max_case Q Qle Qle_total.

/--
Case analysis for `Qmin`: given `x y : ℚ` and a predicate `P : ℚ → Sort*`,
if `x ≤ y` then `P x`, else if `y ≤ x` then `P y`, so `P (Qmin x y)`.
-/
def Qmin_case {P : ℚ → Sort*} (x y : ℚ)
  (h₁ : x ≤ y → P x) (h₂ : y ≤ x → P y) : P (Qmin x y) :=
  if h : x ≤ y then by
    dsimp [Qmin]; rw [if_pos h]; exact h₁ h
  else by
    dsimp [Qmin]; rw [if_neg h]; exact h₂ (le_of_not_ge h)

/--
Case analysis for `Qmax`: given `x y : ℚ` and a predicate `P : ℚ → Sort*`,
if `y ≤ x` then `P x`, else if `x ≤ y` then `P y`, so `P (Qmax x y)`.
-/
def Qmax_case {P : ℚ → Sort*} (x y : ℚ)
  (h₁ : y ≤ x → P x) (h₂ : x ≤ y → P y) : P (Qmax x y) :=
  if h : x ≤ y then by
    dsimp [Qmax]; rw [if_pos h]; exact h₂ h
  else by
    dsimp [Qmax]; rw [if_neg h]; exact h₁ (le_of_not_ge h)


-- Definition QTotalOrder : TotalOrder.
--  apply makeTotalOrder with Q Qeq Qle Qmonotone Qantitone Qmin Qmax.
-- Proof.
--           apply Qeq_le_def.
--          apply Qle_refl.
--         apply Qle_trans.
--        apply Qle_total.
--       firstorder using PartialOrder.Default.monotone_def.
--      firstorder using PartialOrder.Default.antitone_def.
--     apply (TotalOrder.Default.min_def1 Q Qeq Qle Qeq_le_def Qle_total).
--    apply (TotalOrder.Default.min_def2 Q Qeq Qle Qeq_le_def Qle_total).
--   apply (TotalOrder.Default.max_def1 Q Qeq Qle Qeq_le_def Qle_total).
--  apply (TotalOrder.Default.max_def2 Q Qeq Qle Qeq_le_def Qle_total).
-- Defined.

-- Compatibility of Qmin with ≤: Qmin is monotone in both arguments.
/--
If `w ≤ y` and `x ≤ z`, then `Qmin w x ≤ Qmin y z`.
-/
theorem Qmin_le_compat {w x y z : ℚ} (h₁ : w ≤ y) (h₂ : x ≤ z) : Qmin w x ≤ Qmin y z := by
  dsimp [Qmin]
  split_ifs with hw hx
  simp_all only
  exact Preorder.le_trans w x z hw h₂
  · simp only [not_le] at hw
    have hw' : x ≤ w := by {
      rw [le_iff_lt_or_eq]
      left
      exact hw
    }
    exact le_trans hw' h₁
  · exact h₂

-- Let Qto := QTotalOrder.

-- Definition Qmin_lb_l : forall x y : Q, Qmin x y <= x := @meet_lb_l Qto.
-- Definition Qmin_lb_r : forall x y : Q, Qmin x y <= y := @meet_lb_r Qto.
-- Definition Qmin_glb : forall x y z : Q, z <= x -> z <= y -> z <= (Qmin x y) :=
--  @meet_glb Qto.
-- Definition Qmin_comm : forall x y : Q, Qmin x y == Qmin y x := @meet_comm Qto.
-- Definition Qmin_assoc : forall x y z : Q, Qmin x (Qmin y z) == Qmin (Qmin x y) z:=
--  @meet_assoc Qto.
-- Definition Qmin_idem : forall x : Q, Qmin x x == x := @meet_idem Qto.
-- Definition Qle_min_l : forall x y : Q, x <= y <-> Qmin x y == x := @le_meet_l Qto.
-- Definition Qle_min_r : forall x y : Q, y <= x <-> Qmin x y == y := @le_meet_r Qto.
-- Definition Qmin_irred : forall x y: Q, {Qmin x y == x} + {Qmin x y == y} := @meet_irred Qto.
-- Definition Qmin_monotone_r : forall a : Q, Qmonotone (Qmin a) :=
--  @meet_monotone_r Qto.
-- Definition Qmin_monotone_l : forall a : Q, Qmonotone (fun x => Qmin x a) :=
--  @meet_monotone_l Qto.
-- Definition Qmin_le_compat :
--  forall w x y z : Q, w <= y -> x <= z -> Qmin w x <= Qmin y z :=
--  @meet_le_compat Qto.


/--
A total order structure for rationals, with min and max.
-/
structure QTotalOrder where
  eq : ℚ → ℚ → Prop := (· = ·)
  le : ℚ → ℚ → Prop := (· ≤ ·)
  monotone : (ℚ → ℚ) → Prop := Qmonotone
  antitone : (ℚ → ℚ) → Prop := Qantitone
  min : ℚ → ℚ → ℚ := Qmin
  max : ℚ → ℚ → ℚ := Qmax

-- The rest of the structure (lemmas, properties) can be added as needed.

/--
`Qmax` is monotone in both arguments: if `w ≤ y` and `x ≤ z`, then `Qmax w x ≤ Qmax y z`.
-/
theorem Qmax_le_compat {w x y z : ℚ} (h₁ : w ≤ y) (h₂ : x ≤ z) : Qmax w x ≤ Qmax y z := by
  dsimp [Qmax]
  split_ifs with hw hx
  -- Case 1: w ≤ x, y ≤ z
  · exact h₂
  -- Case 2: w ≤ x, ¬(y ≤ z)
  · have zy : z < y := lt_of_not_ge hx
    exact le_trans h₂ (le_of_lt zy)
  -- Case 3: ¬(w ≤ x), y ≤ z
  · (expose_names; exact Preorder.le_trans w y z h₁ h)
  -- Case 4: ¬(w ≤ x), ¬(y ≤ z)
  · exact h₁

/-- `Qmin x y ≤ x`. -/
theorem Qmin_lb_l (x y : ℚ) : Qmin x y ≤ x := by
  dsimp [Qmin]
  split_ifs with h
  · exact Preorder.le_refl x
  · exact le_of_not_ge h

/-- `Qmin x y ≤ y`. -/
theorem Qmin_lb_r (x y : ℚ) : Qmin x y ≤ y := by
  dsimp [Qmin]
  split_ifs with h
  · exact le_trans h (le_refl y)
  · exact le_refl y

/-- If `z ≤ x` and `z ≤ y`, then `z ≤ Qmin x y`. -/
theorem Qmin_glb (x y z : ℚ) (hzx : z ≤ x) (hzy : z ≤ y) : z ≤ Qmin x y := by
  dsimp [Qmin]
  split_ifs with h
  · exact hzx
  · exact hzy

/-- `Qmin x y = Qmin y x`. -/
theorem Qmin_comm (x y : ℚ) : Qmin x y = Qmin y x := by
  dsimp [Qmin]
  split
  · simp_all
    intros h1
    refine (Qeq_le_def x y).mpr ?_
    simp_all only [and_self]
  · simp_all
    intros h1
    refine (Qeq_le_def y x).mpr ?_
    constructor
    · rw [le_iff_lt_or_eq]
      left
      (expose_names; exact h)
    · rw [le_iff_lt_or_eq]
      left
      exact h1

/-- `Qmin x (Qmin y z) = Qmin (Qmin x y) z`. -/
theorem Qmin_assoc (x y z : ℚ) : Qmin x (Qmin y z) = Qmin (Qmin x y) z := by
  dsimp [Qmin]
  repeat split_ifs <;> try {exact rfl}
  · linarith
  · linarith

/-- `Qmin x x = x`. -/
theorem Qmin_idem (x : ℚ) : Qmin x x = x := by
  dsimp [Qmin]
  rw [if_pos (le_refl x)]

/-- `x ≤ y ↔ Qmin x y = x`. -/
theorem Qle_min_l (x y : ℚ) : x ≤ y ↔ Qmin x y = x := by
  dsimp [Qmin]
  constructor
  · intro h; rw [if_pos h]
  · intro h
    by_cases hxy : x ≤ y
    · exact hxy
    · rw [if_neg hxy] at h; exact (h ▸ (by {
    subst h
    simp_all only [le_refl, not_true_eq_false]}))

/-- `y ≤ x ↔ Qmin x y = y`. -/
theorem Qle_min_r (x y : ℚ) : y ≤ x ↔ Qmin x y = y := by
  dsimp [Qmin]
  constructor
  · intro h
    by_cases hxy : x ≤ y
    · rw [if_pos hxy]
      exact le_antisymm hxy h ▸ rfl
    · rw [if_neg hxy]
  · intro h
    by_cases hxy : x ≤ y
    · rw [if_pos hxy] at h
      rw [h]
    · rw [if_neg hxy] at h
      exact le_of_not_ge hxy

/-- `Qmin x y = x` or `Qmin x y = y`. -/
def Qmin_irred (x y : ℚ) : Qmin x y = x ∨ Qmin x y = y := by
  dsimp [Qmin]
  by_cases h : x ≤ y
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- For any `a`, `Qmin a` is monotone. -/
theorem Qmin_monotone_r (a : ℚ) : Qmonotone (Qmin a) :=
  fun {x y} hxy => by
    dsimp [Qmin]
    split_ifs with ha1 ha2
    · exact Preorder.le_refl a
    · exact Preorder.le_trans a x y ha1 hxy
    · exact le_of_not_ge ha1
    · exact hxy

/-- For any `a`, `fun x ↦ Qmin x a` is monotone. -/
theorem Qmin_monotone_l (a : ℚ) : Qmonotone (fun x => Qmin x a) :=
  fun {x y} hxy => by
    dsimp [Qmin]
    split_ifs with hxa hya
    · exact hxy
    · exact hxa
    · simp only [not_le] at *
      linarith
    · exact Preorder.le_refl a

/-- If `w ≤ y` and `x ≤ z`, then `Qmin w x ≤ Qmin y z`. -/
theorem Qmin_le_compat' (w x y z : ℚ) (h₁ : w ≤ y) (h₂ : x ≤ z) :
    Qmin w x ≤ Qmin y z := by
  dsimp [Qmin]
  split_ifs with hw hx hy
  · exact h₁
  · exact Preorder.le_trans w x z hw h₂
  · simp only [not_le] at hw
    rw [le_iff_lt_or_eq]
    left
    calc _ < w := hw
         _ ≤ y := h₁
  · exact h₂

-- Definition Qmax_ub_l : forall x y : Q, x <= Qmax x y := @join_ub_l Qto.
-- Definition Qmax_ub_r : forall x y : Q, y <= Qmax x y := @join_ub_r Qto.
-- Definition Qmax_lub : forall x y z : Q, x <= z -> y <= z -> (Qmax x y) <= z :=
--  @join_lub Qto.
-- Definition Qmax_comm : forall x y : Q, Qmax x y == Qmax y x := @join_comm Qto.
-- Definition Qmax_assoc : forall x y z : Q, Qmax x (Qmax y z) == Qmax (Qmax x y) z:=
--  @join_assoc Qto.
-- Definition Qmax_idem : forall x : Q, Qmax x x == x := @join_idem Qto.
-- Definition Qle_max_l : forall x y : Q, y <= x <-> Qmax x y == x := @le_join_l Qto.
-- Definition Qle_max_r : forall x y : Q, x <= y <-> Qmax x y == y := @le_join_r Qto.
-- Definition Qmax_irred : forall x y: Q, {Qmax x y == x} + {Qmax x y == y} := @join_irred Qto.
-- Definition Qmax_monotone_r : forall a : Q, Qmonotone (Qmax a) :=
--  @join_monotone_r Qto.
-- Definition Qmax_monotone_l : forall a : Q, Qmonotone (fun x => Qmax x a) :=
--  @join_monotone_l Qto.
-- Definition Qmax_le_compat :
--  forall w x y z : Q, w<=y -> x<=z -> Qmax w x <= Qmax y z :=
--  @join_le_compat Qto.

/-- `x ≤ Qmax x y`. -/
theorem Qmax_ub_l (x y : ℚ) : x ≤ Qmax x y := by
  dsimp [Qmax]
  split_ifs with h
  · exact h
  · simp_all only [not_le, le_refl]

/-- `y ≤ Qmax x y`. -/
theorem Qmax_ub_r (x y : ℚ) : y ≤ Qmax x y := by
  dsimp [Qmax]
  split_ifs with h
  · exact le_refl y
  · linarith

/-- If `x ≤ z` and `y ≤ z`, then `Qmax x y ≤ z`. -/
theorem Qmax_lub (x y z : ℚ) (hxz : x ≤ z) (hyz : y ≤ z) : Qmax x y ≤ z := by
  dsimp [Qmax]
  split_ifs with h
  · exact hyz
  · exact hxz

/-- `Qmax x y = Qmax y x`. -/
theorem Qmax_comm (x y : ℚ) : Qmax x y = Qmax y x := by
  dsimp [Qmax]
  split_ifs with hxy hyx
  · linarith
  · linarith
  · linarith
  · linarith

/-- `Qmax x (Qmax y z) = Qmax (Qmax x y) z`. -/
theorem Qmax_assoc (x y z : ℚ) : Qmax x (Qmax y z) = Qmax (Qmax x y) z := by
  dsimp [Qmax]
  repeat split_ifs <;> try {exact rfl}
  · linarith
  · linarith

/-- `Qmax x x = x`. -/
theorem Qmax_idem (x : ℚ) : Qmax x x = x := by
  dsimp [Qmax]
  rw [if_pos (le_refl x)]

/-- `y ≤ x ↔ Qmax x y = x`. -/
theorem Qle_max_l (x y : ℚ) : y ≤ x ↔ Qmax x y = x := by
  dsimp [Qmax]
  constructor
  · intro h
    by_cases hxy : x ≤ y
    · rw [if_pos hxy]
      exact le_antisymm hxy h ▸ rfl
    · rw [if_neg hxy]
  · intro h
    by_cases hxy : x ≤ y
    · rw [if_pos hxy] at h
      rw [h]
    · rw [if_neg hxy] at h
      exact le_of_not_ge hxy

/-- `x ≤ y ↔ Qmax x y = y`. -/
theorem Qle_max_r (x y : ℚ) : x ≤ y ↔ Qmax x y = y := by
  dsimp [Qmax]
  constructor
  · intro h; rw [if_pos h]
  · intro h
    by_cases hxy : x ≤ y
    · exact hxy
    · rw [if_neg hxy] at h; exact (h ▸ (by {
    subst h
    simp_all only [le_refl, not_true_eq_false]}))

/-- `Qmax x y = x` or `Qmax x y = y`. -/
def Qmax_irred (x y : ℚ) : Qmax x y = x ∨ Qmax x y = y := by
  dsimp [Qmax]
  by_cases h : x ≤ y
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-- For any `a`, `Qmax a` is monotone. -/
theorem Qmax_monotone_r (a : ℚ) : Qmonotone (Qmax a) :=
  fun {x y} hxy => by
    dsimp [Qmax]
    split_ifs with ha1 ha2
    · exact hxy
    · linarith
    · simp only [not_le] at *
      linarith
    · exact Preorder.le_refl a

/-- For any `a`, `fun x ↦ Qmax x a` is monotone. -/
theorem Qmax_monotone_l (a : ℚ) : Qmonotone (fun x => Qmax x a) :=
  fun {x y} hxy => by
    dsimp [Qmax]
    split_ifs with hxa hya
    · exact Preorder.le_refl a
    · simp_all
      linarith
    · linarith
    · exact hxy

/-- If `w ≤ y` and `x ≤ z`, then `Qmax w x ≤ Qmax y z`. -/
theorem Qmax_le_compat' (w x y z : ℚ) (h₁ : w ≤ y) (h₂ : x ≤ z) :
    Qmax w x ≤ Qmax y z := Qmax_le_compat h₁ h₂

-- Definition Qmin_max_absorb_l_l : forall x y : Q, Qmin x (Qmax x y) == x :=
--  @meet_join_absorb_l_l Qto.
-- Definition Qmax_min_absorb_l_l : forall x y : Q, Qmax x (Qmin x y) == x :=
--  @join_meet_absorb_l_l Qto.
-- Definition Qmin_max_absorb_l_r : forall x y : Q, Qmin x (Qmax y x) == x :=
--  @meet_join_absorb_l_r Qto.
-- Definition Qmax_min_absorb_l_r : forall x y : Q, Qmax x (Qmin y x) == x :=
--  @join_meet_absorb_l_r Qto.
-- Definition Qmin_max_absorb_r_l : forall x y : Q, Qmin (Qmax x y) x == x :=
--  @meet_join_absorb_r_l Qto.
-- Definition Qmax_min_absorb_r_l : forall x y : Q, Qmax (Qmin x y) x == x :=
--  @join_meet_absorb_r_l Qto.
-- Definition Qmin_max_absorb_r_r : forall x y : Q, Qmin (Qmax y x) x == x :=
--  @meet_join_absorb_r_r Qto.
-- Definition Qmax_min_absorb_r_r : forall x y : Q, Qmax (Qmin y x) x == x :=
--  @join_meet_absorb_r_r Qto.

/-- `Qmin x (Qmax x y) = x`. -/
theorem Qmin_max_absorb_l_l (x y : ℚ) : Qmin x (Qmax x y) = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmax x (Qmin x y) = x`. -/
theorem Qmax_min_absorb_l_l (x y : ℚ) : Qmax x (Qmin x y) = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmin x (Qmax y x) = x`. -/
theorem Qmin_max_absorb_l_r (x y : ℚ) : Qmin x (Qmax y x) = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmax x (Qmin y x) = x`. -/
theorem Qmax_min_absorb_l_r (x y : ℚ) : Qmax x (Qmin y x) = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmin (Qmax x y) x = x`. -/
theorem Qmin_max_absorb_r_l (x y : ℚ) : Qmin (Qmax x y) x = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmax (Qmin x y) x = x`. -/
theorem Qmax_min_absorb_r_l (x y : ℚ) : Qmax (Qmin x y) x = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmin (Qmax y x) x = x`. -/
theorem Qmin_max_absorb_r_r (x y : ℚ) : Qmin (Qmax y x) x = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

/-- `Qmax (Qmin y x) x = x`. -/
theorem Qmax_min_absorb_r_r (x y : ℚ) : Qmax (Qmin y x) x = x := by
  dsimp [Qmin, Qmax]; repeat split_ifs <;> linarith

-- Definition Qmin_max_eq : forall x y : Q, Qmin x y == Qmax x y -> x == y :=
--  @meet_join_eq Qto.

-- Definition Qmax_min_distr_r : forall x y z : Q,
--  Qmax x (Qmin y z) == Qmin (Qmax x y) (Qmax x z) :=
--  @join_meet_distr_r Qto.
-- Definition Qmax_min_distr_l : forall x y z : Q,
--  Qmax (Qmin y z) x == Qmin (Qmax y x) (Qmax z x) :=
--  @join_meet_distr_l Qto.
-- Definition Qmin_max_distr_r : forall x y z : Q,
--  Qmin x (Qmax y z) == Qmax (Qmin x y) (Qmin x z) :=
--  @meet_join_distr_r Qto.
-- Definition Qmin_max_distr_l : forall x y z : Q,
--  Qmin (Qmax y z) x == Qmax (Qmin y x) (Qmin z x) :=
--  @meet_join_distr_l Qto.

-- (*I don't know who wants modularity laws, but here they are *)
-- Definition Qmax_min_modular_r : forall x y z : Q,
--  Qmax x (Qmin y (Qmax x z)) == Qmin (Qmax x y) (Qmax x z) :=
--  @join_meet_modular_r Qto.
-- Definition Qmax_min_modular_l : forall x y z : Q,
--  Qmax (Qmin (Qmax x z) y) z == Qmin (Qmax x z) (Qmax y z) :=
--  @join_meet_modular_l Qto.
-- Definition Qmin_max_modular_r : forall x y z : Q,
--  Qmin x (Qmax y (Qmin x z)) == Qmax (Qmin x y) (Qmin x z) :=
--  @meet_join_modular_r Qto.
-- Definition Qmin_max_modular_l : forall x y z : Q,
--  Qmin (Qmax (Qmin x z) y) z == Qmax (Qmin x z) (Qmin y z) :=
--  @meet_join_modular_l Qto.


/-- If `Qmin x y = Qmax x y`, then `x = y`. -/
theorem Qmin_max_eq (x y : ℚ) (h : Qmin x y = Qmax x y) : x = y := by
  rw [Qmin_comm, Qmax_comm] at h
  cases' Qmin_irred x y with hminx hminy
  · simp only [Qmin, Qmax, ite_eq_left_iff, not_le] at *
    aesop
  · simp only [Qmin, Qmax] at *
    aesop

/-- `Qmax x (Qmin y z) = Qmin (Qmax x y) (Qmax x z)`. -/
theorem Qmax_min_distr_r (x y z : ℚ) : Qmax x (Qmin y z) = Qmin (Qmax x y) (Qmax x z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmax (Qmin y z) x = Qmin (Qmax y x) (Qmax z x)`. -/
theorem Qmax_min_distr_l (x y z : ℚ) : Qmax (Qmin y z) x = Qmin (Qmax y x) (Qmax z x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin x (Qmax y z) = Qmax (Qmin x y) (Qmin x z)`. -/
theorem Qmin_max_distr_r (x y z : ℚ) : Qmin x (Qmax y z) = Qmax (Qmin x y) (Qmin x z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin (Qmax y z) x = Qmax (Qmin y x) (Qmin z x)`. -/
theorem Qmin_max_distr_l (x y z : ℚ) : Qmin (Qmax y z) x = Qmax (Qmin y x) (Qmin z x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmax x (Qmin y (Qmax x z)) = Qmin (Qmax x y) (Qmax x z)`. -/
theorem Qmax_min_modular_r (x y z : ℚ) : Qmax x (Qmin y (Qmax x z)) = Qmin (Qmax x y) (Qmax x z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmax (Qmin (Qmax x z) y) z = Qmin (Qmax x z) (Qmax y z)`. -/
theorem Qmax_min_modular_l (x y z : ℚ) : Qmax (Qmin (Qmax x z) y) z = Qmin (Qmax x z) (Qmax y z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin x (Qmax y (Qmin x z)) = Qmax (Qmin x y) (Qmin x z)`. -/
theorem Qmin_max_modular_r (x y z : ℚ) : Qmin x (Qmax y (Qmin x z)) = Qmax (Qmin x y) (Qmin x z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin (Qmax (Qmin x z) y) z = Qmax (Qmin x z) (Qmin y z)`. -/
theorem Qmin_max_modular_l (x y z : ℚ) : Qmin (Qmax (Qmin x z) y) z = Qmax (Qmin x z) (Qmin y z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith


-- Definition Qmin_max_disassoc : forall x y z : Q, Qmin (Qmax x y) z <= Qmax x (Qmin y z) :=
--  @meet_join_disassoc Qto.

-- Lemma Qplus_monotone_r : forall a, Qmonotone (Qplus a).
-- Proof. do 2 red. intros. now apply Qplus_le_r. Qed.
-- Lemma Qplus_monotone_l : forall a, Qmonotone (fun x => Qplus x a).
-- Proof. do 2 red. intros. now apply Qplus_le_l. Qed.
-- Definition Qmin_plus_distr_r : forall x y z : Q, x + Qmin y z == Qmin (x+y) (x+z)  :=
--  fun a => @monotone_meet_distr Qto _ (Qplus_monotone_r a).
-- Definition Qmin_plus_distr_l : forall x y z : Q, Qmin y z + x == Qmin (y+x) (z+x) :=
--  fun a => @monotone_meet_distr Qto _ (Qplus_monotone_l a).
-- Definition Qmax_plus_distr_r : forall x y z : Q, x + Qmax y z == Qmax (x+y) (x+z)  :=
--  fun a => @monotone_join_distr Qto _ (Qplus_monotone_r a).
-- Definition Qmax_plus_distr_l : forall x y z : Q, Qmax y z + x == Qmax (y+x) (z+x) :=
--  fun a => @monotone_join_distr Qto _ (Qplus_monotone_l a).
-- Definition Qmin_minus_distr_l : forall x y z : Q, Qmin y z - x == Qmin (y-x) (z-x) :=
--  (fun x => Qmin_plus_distr_l (-x)).
-- Definition Qmax_minus_distr_l : forall x y z : Q, Qmax y z - x == Qmax (y-x) (z-x) :=
--  (fun x => Qmax_plus_distr_l (-x)).


/-- `Qmin (Qmax x y) z ≤ Qmax x (Qmin y z)`. -/
theorem Qmin_max_disassoc (x y z : ℚ) : Qmin (Qmax x y) z ≤ Qmax x (Qmin y z) := by
  dsimp [Qmin, Qmax]
  repeat split_ifs <;> linarith

/-- For any `a`, `Qplus a` is monotone. -/
theorem Qplus_monotone_r (a : ℚ) : Qmonotone (fun x => a + x) :=
  fun {x y} hxy => add_le_add_left hxy a

/-- For any `a`, `fun x ↦ x + a` is monotone. -/
theorem Qplus_monotone_l (a : ℚ) : Qmonotone (fun x => x + a) :=
  fun {x y} hxy => add_le_add_right hxy a

/-- `x + Qmin y z = Qmin (x + y) (x + z)`. -/
theorem Qmin_plus_distr_r (x y z : ℚ) : x + Qmin y z = Qmin (x + y) (x + z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin y z + x = Qmin (y + x) (z + x)`. -/
theorem Qmin_plus_distr_l (x y z : ℚ) : Qmin y z + x = Qmin (y + x) (z + x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `x + Qmax y z = Qmax (x + y) (x + z)`. -/
theorem Qmax_plus_distr_r (x y z : ℚ) : x + Qmax y z = Qmax (x + y) (x + z) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmax y z + x = Qmax (y + x) (z + x)`. -/
theorem Qmax_plus_distr_l (x y z : ℚ) : Qmax y z + x = Qmax (y + x) (z + x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmin y z - x = Qmin (y - x) (z - x)`. -/
theorem Qmin_minus_distr_l (x y z : ℚ) : Qmin y z - x = Qmin (y - x) (z - x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `Qmax y z - x = Qmax (y - x) (z - x)`. -/
theorem Qmax_minus_distr_l (x y z : ℚ) : Qmax y z - x = Qmax (y - x) (z - x) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `-(Qmin x y) = Qmax (-x) (-y)`. -/
theorem Qmin_max_de_morgan (x y : ℚ) : -(Qmin x y) = Qmax (-x) (-y) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith

/-- `-(Qmax x y) = Qmin (-x) (-y)`. -/
theorem Qmax_min_de_morgan (x y : ℚ) : -(Qmax x y) = Qmin (-x) (-y) := by
  dsimp [Qmax, Qmin]
  repeat split_ifs <;> linarith





-- Lemma Qminus_antitone : forall a : Q, Qantitone (fun x => a - x).
-- Proof.
--  change (forall a x y : Q, x <= y -> a + - y <= a + - x).
--  intros.
--  apply Qplus_le_compat; firstorder using Qle_refl, Qopp_le_compat.
-- Qed.

-- Definition Qminus_min_max_antidistr_r : forall x y z : Q, x - Qmin y z == Qmax (x-y) (x-z) :=
--  fun a => @antitone_meet_join_distr Qto _ (Qminus_antitone a).
-- Definition Qminus_max_min_antidistr_r : forall x y z : Q, x - Qmax y z == Qmin (x-y) (x-z) :=
--  fun a => @antitone_join_meet_distr Qto _ (Qminus_antitone a).

-- Lemma Qmult_pos_monotone_r : forall a, (0 <= a) -> Qmonotone (Qmult a).
-- Proof.
--  intros a Ha b c H.
--  do 2 rewrite -> (Qmult_comm a).
--  apply Qmult_le_compat_r; auto with *.
-- Qed.

-- Lemma Qmult_pos_monotone_l : forall a, (0 <= a) -> Qmonotone (fun x => x*a).
-- Proof.
--  intros a Ha b c H.
--  apply Qmult_le_compat_r; auto with *.
-- Qed.

-- Definition Qmin_mult_pos_distr_r : forall x y z : Q, 0 <= x -> x * Qmin y z == Qmin (x*y) (x*z)  :=
--  fun x y z H => @monotone_meet_distr Qto _ (Qmult_pos_monotone_r _ H) y z.
-- Definition Qmin_mult_pos_distr_l : forall x y z : Q, 0 <= x -> Qmin y z * x == Qmin (y*x) (z*x) :=
--  fun x y z H => @monotone_meet_distr Qto _ (Qmult_pos_monotone_l x H) y z.
-- Definition Qmax_mult_pos_distr_r : forall x y z : Q, 0 <= x -> x * Qmax y z == Qmax (x*y) (x*z)  :=
--  fun x y z H => @monotone_join_distr Qto _ (Qmult_pos_monotone_r x H) y z.
-- Definition Qmax_mult_pos_distr_l : forall x y z : Q, 0 <= x -> Qmax y z * x == Qmax (y*x) (z*x) :=
--  fun x y z H => @monotone_join_distr Qto _ (Qmult_pos_monotone_l x H) y z.

-- End QTotalOrder.
-- (* begin hide *)
-- #[global]
-- Hint Resolve Qmin_lb_l: qarith.
-- #[global]
-- Hint Resolve Qmin_lb_r: qarith.
-- #[global]
-- Hint Resolve Qmin_glb: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_l: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_r: qarith.
-- #[global]
-- Hint Resolve Qmax_lub: qarith.
-- (* end hide *)


-- Lemma Qminus_antitone : forall a : Q, Qantitone (fun x => a - x).
-- Proof.
--  change (forall a x y : Q, x <= y -> a + - y <= a + - x).
--  intros.
--  apply Qplus_le_compat; firstorder using Qle_refl, Qopp_le_compat.
-- Qed.

-- Definition Qminus_min_max_antidistr_r : forall x y z : Q, x - Qmin y z == Qmax (x-y) (x-z) :=
--  fun a => @antitone_meet_join_distr Qto _ (Qminus_antitone a).
-- Definition Qminus_max_min_antidistr_r : forall x y z : Q, x - Qmax y z == Qmin (x-y) (x-z) :=
--  fun a => @antitone_join_meet_distr Qto _ (Qminus_antitone a).

-- Lemma Qmult_pos_monotone_r : forall a, (0 <= a) -> Qmonotone (Qmult a).
-- Proof.
--  intros a Ha b c H.
--  do 2 rewrite -> (Qmult_comm a).
--  apply Qmult_le_compat_r; auto with *.
-- Qed.

-- Lemma Qmult_pos_monotone_l : forall a, (0 <= a) -> Qmonotone (fun x => x*a).
-- Proof.
--  intros a Ha b c H.
--  apply Qmult_le_compat_r; auto with *.
-- Qed.



/-- For any `a`, `fun x ↦ a - x` is antitone. -/
theorem Qminus_antitone (a : ℚ) : Qantitone (fun x => a - x) :=
  fun {x y} hxy => by linarith

/-- `x - Qmin y z = Qmax (x - y) (x - z)`. -/
theorem Qminus_min_max_antidistr_r (x y z : ℚ) : x - Qmin y z = Qmax (x - y) (x - z) := by
  dsimp [Qmin, Qmax]
  split_ifs <;> linarith

/-- `x - Qmax y z = Qmin (x - y) (x - z)`. -/
theorem Qminus_max_min_antidistr_r (x y z : ℚ) : x - Qmax y z = Qmin (x - y) (x - z) := by
  dsimp [Qmin, Qmax]
  split_ifs <;> linarith

/-- For any `a ≥ 0`, `fun x ↦ a * x` is monotone. -/
def Qmult_pos_monotone_r (a : ℚ) (ha : 0 ≤ a) : Qmonotone (fun x => a * x) := by {
  intros x
  exact fun {y} a_1 ↦ mul_le_mul_of_nonneg_left a_1 ha
}
  --fun hxy => mul_le_mul_of_nonneg_left hxy ha

/-- For any `a ≥ 0`, `fun x ↦ x * a` is monotone. -/
def Qmult_pos_monotone_l (a : ℚ) (ha : 0 ≤ a) : Qmonotone (fun x => x * a) :=
  fun {x y} hxy => mul_le_mul_of_nonneg_right hxy ha


-- Definition Qmin_mult_pos_distr_r : forall x y z : Q, 0 <= x -> x * Qmin y z == Qmin (x*y) (x*z)  :=
--  fun x y z H => @monotone_meet_distr Qto _ (Qmult_pos_monotone_r _ H) y z.
-- Definition Qmin_mult_pos_distr_l : forall x y z : Q, 0 <= x -> Qmin y z * x == Qmin (y*x) (z*x) :=
--  fun x y z H => @monotone_meet_distr Qto _ (Qmult_pos_monotone_l x H) y z.
-- Definition Qmax_mult_pos_distr_r : forall x y z : Q, 0 <= x -> x * Qmax y z == Qmax (x*y) (x*z)  :=
--  fun x y z H => @monotone_join_distr Qto _ (Qmult_pos_monotone_r x H) y z.
-- Definition Qmax_mult_pos_distr_l : forall x y z : Q, 0 <= x -> Qmax y z * x == Qmax (y*x) (z*x) :=
--  fun x y z H => @monotone_join_distr Qto _ (Qmult_pos_monotone_l x H) y z.


/-- If `0 ≤ x`, then `x * Qmin y z = Qmin (x * y) (x * z)`. -/
theorem Qmin_mult_pos_distr_r (x y z : ℚ) (hx : 0 ≤ x) : x * Qmin y z = Qmin (x * y) (x * z) := by
  sorry

/-- If `0 ≤ x`, then `Qmin y z * x = Qmin (y * x) (z * x)`. -/
theorem Qmin_mult_pos_distr_l (x y z : ℚ) (hx : 0 ≤ x) : Qmin y z * x = Qmin (y * x) (z * x) := by
  sorry

/-- If `0 ≤ x`, then `x * Qmax y z = Qmax (x * y) (x * z)`. -/
theorem Qmax_mult_pos_distr_r (x y z : ℚ) (hx : 0 ≤ x) : x * Qmax y z = Qmax (x * y) (x * z) := by
  sorry

/-- If `0 ≤ x`, then `Qmax y z * x = Qmax (y * x) (z * x)`. -/
theorem Qmax_mult_pos_distr_l (x y z : ℚ) (hx : 0 ≤ x) : Qmax y z * x = Qmax (y * x) (z * x) := by
  sorry


-- End QTotalOrder.
-- (* begin hide *)
-- #[global]
-- Hint Resolve Qmin_lb_l: qarith.
-- #[global]
-- Hint Resolve Qmin_lb_r: qarith.
-- #[global]
-- Hint Resolve Qmin_glb: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_l: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_r: qarith.
-- #[global]
-- Hint Resolve Qmax_lub: qarith.
-- (* end hide *)


-- End QTotalOrder.
-- (* begin hide *)
-- #[global]
-- Hint Resolve Qmin_lb_l: qarith.
-- #[global]
-- Hint Resolve Qmin_lb_r: qarith.
-- #[global]
-- Hint Resolve Qmin_glb: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_l: qarith.
-- #[global]
-- Hint Resolve Qmax_ub_r: qarith.
-- #[global]
-- Hint Resolve Qmax_lub: qarith.
-- (* end hide *)
