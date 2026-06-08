/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- Note: there are 3 approaches to formalize two-sorted first-order logic:
-- a) add symbols isStr(x), isNum(x) to vocabulary and encode
--    two-sorted logic as first-order logic. This bypasses Lean automation
--    and will be cumbersome to work with in the long run
-- b) This is what we'd use here:
--    use the fact that some of interesting theories (such as V^i family)
--    are finitely axiomatizable - so we don't have to formalize the two-sorted
--    comprehension axiom scheme; we can write meta tactic to prove a given
--    comprehension instance from the 12 canonical comprehension instances
--    that we define below (slightly ugly)
-- c) extend Mathlib.ModelTheory to work with many-sorted languages
--    long term, this will be necessary. For now, this is probably weeks
--    of work which we can skip until making sure that we'll get to any
--    interesting result at all

import Lean

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.SimpRw

import LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
import LeanPool.FormalizationOfBoundedArithmetic.IOPEN
import LeanPool.FormalizationOfBoundedArithmetic.IDelta0
import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.Complexity
import LeanPool.FormalizationOfBoundedArithmetic.Algebra
import LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
import LeanPool.FormalizationOfBoundedArithmetic.Register

/-!
# LeanPool.FormalizationOfBoundedArithmetic.V0
-/

open FirstOrder Language
open HasTypesIs
open HasEmptySet
open HasLen


-- page 129, CN10: Finite axiomatizability of V0
/--
Two-sorted V0-style models used by this development.

This is a strengthened bundled API: besides the finite V0 comprehension axioms,
it includes induction, order, and algebraic laws as fields so later files can
build the string-addition theory over a compact typeclass interface.
-/
class V0Model
  (num : Type) (str : outParam Type)
  extends
  HasLen str num,
  Membership num str,
  BASICModel num
where
  -- axiom for empty string; 4.4.1 Two-Sorted Free Variable Normal Form
  -- E : len (empty : str) = (0 : num)
  -- B1 : ∀ x : num,       x + 1 ≠ 0
  -- B2 : ∀ x y : num, x + 1 = y + 1 -> x = y
  -- B3 : ∀ x : num,       x + 0 = x
  -- B4 : ∀ x y : num, x + (y + 1) = (x + y) + 1
  -- B5 : ∀ x : num,       x * 0 = 0
  -- B6 : ∀x y : num, x * (y + 1) = (x * y) + x
  -- B7 : ∀x y : num, x <= y -> y <= x -> x = y
  -- B8 : ∀x y : num, x <= x + y
  B9 : ∀ x : num,       0 <= x
  B10: ∀ x y : num, x <= y ∨ y <= x
  B11: ∀ x y : num, x <= y <-> x < (y + 1)
  B12: ∀ {x : num},       x ≠ 0 -> (∃ y : num, (y <= x ∧ (y + 1) = x))
  L1 : ∀ {X : str}, ∀ {y : num}, y ∈ X -> (y < (len X))
  L2 : ∀ {X : str}, ∀ {y : num}, (y + 1) = len X -> y ∈ X

  SE : ∀ {X Y: str},
    len X = (len Y : num)
    -> (∀ y : num, ((y < len X) -> (y ∈ X <-> y ∈ Y)))
    -> X = Y

  comp1 : ∀ b1 b2 : num, ∃ Y : str, (len Y ≤ ⟨b1, b2⟩ ∧ (∀ x1 < b1, ∀ x2 < b2,
    ⟨x1, x2⟩ ∈ Y ↔ (x1 = x2)
  ))

  -- φ2(x1,x2,x3) ≡ x3 = x1
  comp2 : ∀ b1 b2 b3 : num, ∃ Y : str, len Y ≤ ⟨b1, b2, b3⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2, ∀ x3 < b3,
      ⟨x1, x2, x3⟩ ∈ Y ↔ (x3 = x1)

  -- φ3(x1,x2,x3) ≡ x3 = x2
  comp3 : ∀ b1 b2 b3 : num, ∃ Y : str, len Y ≤ ⟨b1, b2, b3⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2, ∀ x3 < b3,
      ⟨x1, x2, x3⟩ ∈ Y ↔ (x3 = x2)

  -- φ4[Q1,Q2](x1,x2) ≡ ∃y ≤ x1 (Q1(x1,y) ∧ Q2(y,x2))
  comp4 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x1 < b1, ∀ x2 < b2,
      ⟨x1, x2⟩ ∈ Y ↔ (∃ y : num, y ≤ x1 ∧ (⟨x1, y⟩ ∈ Q1 ∧ ⟨y, x2⟩ ∈ Q2))

  -- φ5[a](x,y) ≡ y = a
  comp5 : ∀ a : num, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔ (y = a)

  -- φ6[Q1,Q2](x,y) ≡ ∃z1 ≤ y ∃z2 ≤ y (Q1(x,z1) ∧ Q2(x,z2) ∧ y = z1 + z2)
  comp6 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔
        (∃ z1 : num, z1 ≤ y ∧
         ∃ z2 : num, z2 ≤ y ∧
           (⟨x, z1⟩ ∈ Q1 ∧ ⟨x, z2⟩ ∈ Q2 ∧ y = z1 + z2))

  -- φ7[Q1,Q2](x,y) ≡ ∃z1 ≤ y ∃z2 ≤ y (Q1(x,z1) ∧ Q2(x,z2) ∧ y = z1 · z2)
  comp7 : ∀ Q1 Q2 : str, ∀ b1 b2 : num, ∃ Y : str, len Y ≤ ⟨b1, b2⟩ ∧
    ∀ x < b1, ∀ y < b2,
      ⟨x, y⟩ ∈ Y ↔
        (∃ z1 : num, z1 ≤ y ∧
         ∃ z2 : num, z2 ≤ y ∧
           (⟨x, z1⟩ ∈ Q1 ∧ ⟨x, z2⟩ ∈ Q2 ∧ y = z1 * z2))

  -- φ8[Q1,Q2,c](x) ≡ ∃y1 ≤ c ∃y2 ≤ c (Q1(x,y1) ∧ Q2(x,y2) ∧ y1 ≤ y2)
  comp8 : ∀ Q1 Q2 : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔
        (∃ y1 : num, y1 ≤ c ∧
         ∃ y2 : num, y2 ≤ c ∧
           (⟨x, y1⟩ ∈ Q1 ∧ ⟨x, y2⟩ ∈ Q2 ∧ y1 ≤ y2))

  -- φ9[X,Q,c](x) ≡ ∃y ≤ c (Q(x,y) ∧ X(y))
  comp9 : ∀ X Q : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (∃ y : num, y ≤ c ∧ (⟨x, y⟩ ∈ Q ∧ y ∈ X))

  -- φ10[Q](x) ≡ ¬Q(x)
  comp10 : ∀ Q : str, ∀ b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ ¬ (x ∈ Q)

  -- φ11[Q1,Q2](x) ≡ Q1(x) ∧ Q2(x)
  comp11 : ∀ Q1 Q2 : str, ∀ b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (x ∈ Q1 ∧ x ∈ Q2)

  -- φ12[Q,c](x) ≡ ∀y ≤ c Q(x,y)
  comp12 : ∀ Q : str, ∀ c b : num, ∃ Y : str, len Y ≤ b ∧
    ∀ x < b,
      x ∈ Y ↔ (∀ y : num, y ≤ c → ⟨x, y⟩ ∈ Q)

  xmin_comp_ax : ∀ X : str, ∃ Y : str,
    len Y ≤ len X ∧ ∀ z < len X, z ∈ Y ↔ ∀ y ≤ z, y ∉ X

  comp_xind_ax : ∀ X : str, ∀ z : num, ∃ Y : str,
    len Y ≤ z + 1 ∧ ∀ y < z + 1, y ∈ Y ↔ y ∉ X

  prop_induction_ax : ∀ P : num → Prop,
    P 0 → (∀ i : num, P i → P (i + 1)) → ∀ i : num, P i

  open_induction_ax {n} {a : Type} [IsEnum a]
    (phi : peano.BoundedFormula ((Vars1 n) ⊕ a) 0) :
    phi.IsOpen -> (mkInductionSentence phi).Realize num

  delta0_induction_ax {n} {a : Type} [IsEnum a]
    (phi : peano.BoundedFormula ((Vars1 n) ⊕ a) 0) :
    phi.IsDelta0 -> (mkInductionSentence phi).Realize num

  -- le_refl : ∀ x : num, x <= x
  le_trans : ∀ x y z : num, x <= y -> y <= z -> x <= z
  zero_add : ∀ x : num, 0 + x = x
  add_left_cancel : ∀ x : num, IsAddLeftRegular x
  add_right_cancel : ∀ x : num, IsAddRightRegular x
  add_assoc : ∀ x y z : num, (x + y) + z = x + (y + z)
  le_total : ∀ (a b : num), a ≤ b ∨ b ≤ a
  /-- Decidability of the order relation on numbers. -/
  toDecidableLE : DecidableLE num
  exists_add_of_le : ∀ {a b : num}, a ≤ b → ∃ c, b = a + c
  add_le_add_left : ∀ (a b : num), a ≤ b → ∀ (c : num), c + a ≤ c + b
  le_antisymm : ∀ (a b : num), a ≤ b → b ≤ a → a = b
  add_comm : ∀ (a b : num), a + b = b + a

namespace V0Model


variable {num str} [M : V0Model num str]
open V0Model BASICModel


instance : PartialOrder num where
  le_refl := BASICModel.le_refl
  le_trans := V0Model.le_trans
  le_antisymm := by apply B7

instance : AddZeroClass num where
  zero_add := zero_add
  add_zero := by apply B3

instance : IsLeftCancelAdd num where
  add_left_cancel := add_left_cancel

instance : IsRightCancelAdd num where
  add_right_cancel := add_right_cancel

instance : AddMonoid num where
  add_assoc := add_assoc
  nsmul := nsmulRec

instance : LinearOrder num where
  le_total := le_total
  toDecidableLE := toDecidableLE

instance : CanonicallyOrderedAdd num where
  exists_add_of_le := exists_add_of_le
  le_self_add := by apply B8
  le_add_self := by
    intro a b
    rw [add_comm]
    apply B8

instance : AddCommMonoid num where
  add_comm := add_comm

instance : PartialOrder num where
  le_antisymm := le_antisymm

instance : IsOrderedAddMonoid num where
  add_le_add_left := by
    intro a b h c
    rw [add_comm a c, add_comm b c]
    exact V0Model.add_le_add_left a b h c


theorem xmin_comp (X : str) :
    ∃ Y : str, (len Y : num) ≤ len X ∧ ∀ z < len X, z ∈ Y ↔ ∀ y ≤ z, y ∉ X :=
by
  exact M.xmin_comp_ax X

lemma ex_elt_of_len_pos :
    ∀ {X : str}, (0 : num) < (len X) -> ∃ x, x ∈ X ∧ x + 1 = len X := by
  intro X h_len
  obtain ⟨len_pred, h_le, h_eq⟩ := B12 (by
    exact Ne.symm (ne_of_lt h_len)
  )
  exists len_pred
  constructor
  · apply L2
    exact h_eq
  · exact h_eq

lemma lt_succ : ∀ (x : num), x < x + 1 := by
  intro x
  rw [lt_iff_le_and_ne]
  constructor
  · apply B8
  · intro h
    conv at h => lhs; rw [<- add_zero x]
    rw [add_left_cancel_iff] at h
    apply @M.B1 0
    calc
      (0 : num) + 1 = 0 + 0 := congrArg (fun y => (0 : num) + y) h.symm
      _ = 0 := B3 0

lemma len_not_in : ∀ {X : str}, len X ∉ X := by
  intro X h
  apply (L1 h).right
  rfl

-- Exercise V.1.1
lemma not_lt_zero
  : ∀ {x : num}, ¬ x < 0 :=
by
  intro x
  rw [not_lt_iff_eq_or_lt]
  exact eq_zero_or_pos x

instance : CanonicallyOrderedAdd num where
  le_self_add := by
    intro a b
    conv => lhs; rw [<- M.B3 a]
    apply add_le_add
    · apply _root_.le_refl
    · apply M.B9
  le_add_self := by
    intro a b
    rw [add_comm]
    apply B8

theorem xmin :
  ∀ {X : str}, (0 : num) < len X -> ∃ x < len X, x ∈ X ∧ ∀ y < x, y ∉ X :=
by
  intro X h_lenX
  obtain ⟨Y, h_Y⟩ := xmin_comp X (num := num)
  exists (len Y)
  by_cases h : (0 : num) < len Y
  · obtain ⟨y, hy_in, hy_eq⟩ := ex_elt_of_len_pos h
    constructor
    · -- len Y < len X
      cases le_iff_eq_or_lt.mp h_Y.left with
      | inl h_lenY_eq_lenX =>
        exfalso
        have h_X_empty : ∀ x < len X, x ∉ X := by
          have aux := h_Y.right y
          rw [<- h_lenY_eq_lenX] at aux
          specialize aux (L1 hy_in)
          intro x h_x_lt
          apply aux.mp hy_in
          rw [B11, hy_eq]
          rw [h_lenY_eq_lenX]
          exact h_x_lt
        have h_X_empty' : ¬∃ x < len X, x ∈ X := by
          refine not_exists_of_forall_not ?_
          intro x hx
          apply h_X_empty x hx.left hx.right
        apply h_X_empty'
        obtain ⟨wit, h_wit⟩ := ex_elt_of_len_pos (X := X) (by
          rw [h_lenY_eq_lenX] at h
          exact h
        )
        exists wit
        constructor
        · apply L1 h_wit.left
        · exact h_wit.left
      | inr h_lenY_lt_lenX =>
        assumption
    · constructor
      · -- len Y ∈ X
        rw [le_iff_eq_or_lt] at h_Y
        cases h_Y.left with
        | inl h =>
          exfalso
          rw [<- h] at h_lenX
          conv at h_Y => right; rw [<- h]
          have aux := (h_Y.right y (M.L1 hy_in)).mp hy_in y (_root_.le_refl _)
          apply aux
          apply L2
          rw [<- h]
          exact hy_eq
        | inr h =>
          have aux := (not_congr <| h_Y.right (len Y) h).mp len_not_in
          simp only [not_forall, not_not] at aux
          obtain ⟨x, h_x_le, h_x_X⟩ := aux
          rw [le_iff_eq_or_lt] at h_x_le
          cases h_x_le with
          | inl h =>
            rw [<- h]
            exact h_x_X
          | inr h =>
            -- first, obtain hypothesis for last y of Y
            have len_Y_ne_zero : (len Y : num) ≠ 0 := by
              intro h'
              rw [h'] at h
              apply not_lt_zero h
            have len_Y_pos : 0 < (len Y : num) := by
              cases (eq_zero_or_pos (len Y : num)) with
              | inl h =>
                exfalso
                apply len_Y_ne_zero
                exact h
              | inr h =>
                exact h
            obtain ⟨y, hy_in, hy_eq⟩ := ex_elt_of_len_pos len_Y_pos
            clear len_Y_ne_zero len_Y_pos h_lenX
            rename_i h_lenY_lt_lenX
            have h_y_lt_lenX : y < (len X) := by
              apply lt_trans _ h_lenY_lt_lenX
              apply L1 hy_in
            -- then show that if last of Y holds, but (len Y) does not,
            -- then some bit had to be set in X
            false_or_by_contra
            · rename_i h_lenY_notin_X
              have h := (h_Y.right (len Y) h_lenY_lt_lenX).mpr
              apply @len_not_in num _ _ Y
              apply h
              intro y2 h_y2
              rw [le_iff_eq_or_lt] at h_y2
              cases h_y2 with
              | inl h_y2 =>
                rw [h_y2]
                apply (h_Y.right (len Y) h_lenY_lt_lenX).mp
                · apply h
                  intro y3 hy3
                  rw [le_iff_eq_or_lt] at hy3
                  cases hy3 with
                  | inl hy3 =>
                    rw [hy3]
                    exact h_lenY_notin_X
                  | inr hy3 =>
                    apply (h_Y.right y h_y_lt_lenX).mp hy_in
                    rw [B11, hy_eq]
                    exact hy3
                · rfl
              | inr h_y2 =>
                clear h
                apply (h_Y.right y h_y_lt_lenX).mp hy_in
                rw [B11, hy_eq]
                exact h_y2
      · -- ∀ z < len Y, z ∉ X
        intro z h_z h_zX
        -- notice: Y is of the form 11111..1 - if we get any 0 in Y,
        -- it means that a bit in X was set. so, we won't get any further
        -- bits set in Y!
        have h_y_lt_lenX : y < len X := by
          apply lt_of_lt_of_le (L1 hy_in) h_Y.left
        have h_X := (h_Y.right y h_y_lt_lenX).mp hy_in z
        apply h_X
        · rw [B11, hy_eq]
          exact h_z
        · exact h_zX
  · have Y_empty : len Y = (0 : num) := by
      have h1 := B9 (num := num) (len Y)
      rw [le_iff_eq_or_lt] at h1
      cases h1 with
      | inl h1 => exact h1.symm
      | inr h1 => exfalso; apply h; exact h1
    constructor
    · rw [Y_empty]
      exact h_lenX
    · constructor
      · -- len Y ∈ X
        false_or_by_contra
        rename_i h_contr
        have zero_in_Y : (0 : num) ∈ Y := by
          apply (h_Y.right 0 h_lenX).mpr
          intro y hy
          have y_zero := B7 hy (M.B9 _)
          rw [y_zero, <- Y_empty]
          exact h_contr
        rw [<- Y_empty] at zero_in_Y
        exact len_not_in zero_in_Y
      · -- ∀ y < len Y, y ∉ X
        intro y hy
        exfalso
        rw [Y_empty] at hy
        exact not_lt_zero hy


lemma comp_xind :
    ∀ X : str, ∀ z : num, ∃ Y : str, len Y <= z + 1 ∧
      ∀ y < z + 1, (y ∈ Y ↔ y ∉ X) := by
  intro X z
  exact M.comp_xind_ax X z

lemma len_ne_zero_of_in : ∀ {x : num}, ∀ {X : str},
  x ∈ X -> len X ≠ (0 : num) :=
by
  intro x X h
  have h2 := L1 h
  apply ne_of_gt
  apply lt_of_le_of_lt _ h2
  exact B9 x

theorem xind :
  ∀ {X : str}, ∀ {z : num},
  0 ∈ X
  -> (∀ y < z, y ∈ X -> y + 1 ∈ X)
  -> z ∈ X :=
by
  intro X z h_base h_y
  false_or_by_contra
  rename_i h_z
  obtain ⟨Y, h_Y_le, h_Y⟩ := comp_xind X z
  have h_z_in_Y : z ∈ Y := by
    rw [h_Y]
    · exact h_z
    · exact lt_succ z
  have h_Y_pos : (0 : num) < len Y := by
    rw [lt_iff_le_and_ne]
    constructor
    · apply B9
    · exact Ne.symm (len_ne_zero_of_in h_z_in_Y)
  obtain ⟨y0, h_y0⟩ := xmin h_Y_pos
  have h_y0_ne_zero : y0 ≠ 0 := by
    have h_0_notin_Y : 0 ∉ Y := by
      rw [h_Y]
      · rw [@not_not]
        exact h_base
      · constructor
        · apply B9
        · rw [le_iff_eq_or_lt]
          intro contr
          cases contr with
          | inl contr =>
            apply M.B1 contr
          | inr contr =>
            apply M.not_lt_zero contr
    intro contr
    apply h_0_notin_Y
    rw [<-contr]
    exact h_y0.2.1
  obtain ⟨x0, h_x0⟩ := B12 h_y0_ne_zero
  have h_x0_in : x0 ∈ X := by
    apply not_not.mp
    rw [<- h_Y]
    · apply h_y0.2.2
      rw [<- h_x0.2]
      exact lt_succ x0
    · apply lt_of_lt_of_le _ h_Y_le
      apply lt_trans _ h_y0.1
      rw [<- h_x0.2]
      exact lt_succ x0
  have h_succ_x0_notin : x0 + 1 ∉ X := by
    rw [h_x0.2]
    rw [<- h_Y]
    · exact h_y0.2.1
    · apply lt_of_lt_of_le _ h_Y_le
      exact h_y0.1
  apply h_succ_x0_notin
  apply h_y
  · have aux : y0 < z + 1 := by
      apply lt_of_lt_of_le _ h_Y_le
      apply L1
      exact h_y0.2.1
    rw [<- B11] at aux
    apply lt_of_lt_of_le _ aux
    rw [<- h_x0.2]
    apply lt_succ
  · exact h_x0_in


theorem ind_of_comp (P : num -> Prop) :
  (∀ y : num, ∃ Y : str, (len Y : num) ≤ y ∧ ∀ z < y, z ∈ Y ↔ P z)
  -> (P 0 -> (∀ x, P x -> P (x + 1)) -> ∀ x, P x) :=
by
  intro hcomp pbase pstep z
  obtain ⟨X, hX⟩ := hcomp (z + 1)
  have hX0 : 0 ∈ X := by
    rw [hX.2]
    · exact pbase
    · rw [<- B11]
      exact B9 z
  have hXstep : ∀ y < z, y ∈ X -> y + 1 ∈ X := by
    intro y hyz hyX
    rw [hX.2]
    · apply pstep
      rw [<- hX.2]
      · exact hyX
      · rw [<- B11]
        exact hyz.1
    · exact (add_lt_add_iff_right 1).mpr hyz
  have hzX : z ∈ X := by
    apply xind
    · exact hX0
    · exact hXstep
  rw [<- hX.2]
  · exact hzX
  · exact lt_succ z

/-- Named alias emphasizing that this induction theorem uses the strengthened `V0Model` bundle. -/
theorem ind_strengthened_v0 (P : num -> Prop) :
  (∀ y : num, ∃ Y : str, (len Y : num) ≤ y ∧ ∀ z < y, z ∈ Y ↔ P z)
  -> (P 0 -> (∀ x, P x -> P (x + 1)) -> ∀ x, P x) :=
  ind_of_comp P


instance : IDelta0Model num where
  open_induction phi h_open := M.open_induction_ax phi h_open
  delta0_induction phi h_delta0 := M.delta0_induction_ax phi h_delta0

end V0Model

-- Corollary V.1.8
-- T, extending V0, if proves Comp for set of formulas Phi,
-- then also proves Ind, Min and Max for Phi.
-- theorem ind_of_comp : ∀ x : num, comp x ->

-- variable {num} {str : outParam Type} [V0Model num str]


/-- Types equipped with a successor operation. -/
class HasSucc (α : Type*) where
  /-- Successor operation. -/
  succ : α -> α

/-- Carry predicate for binary string addition below position `i`. -/
def Carry {num str} [V0Model num str] (i : num) (X Y : str) :=
  ∃ k < i, (k ∈ X ∧ k ∈ Y ∧ ∀ j < i, (k < j → (j ∈ X ∨ j ∈ Y)))

/-- Extension of `V0` with string successor and string addition. -/
class V0ExtModel
  (num : Type) (str : outParam Type)
  extends
  Zero str, HasSucc str, Add str,
  V0Model (num := num) (str := str)
where
  ax_empty : ∀ {z : num}, z ∈ (0 : str) ↔ z < 0
  ax_succ : ∀ {X : str}, ∀ {i : num}, i ∈ HasSucc.succ X ↔
    (i ≤ len X
      ∧ ((i ∈ X ∧ ∃ j < i, j ∉ X)
          ∨ (i ∉ X ∧ ∀ j < i, j ∈ X)
        )
    )

  ax_add : ∀ {X Y : str}, ∀ {i : num}, i ∈ X + Y ↔
    (i < len X + len Y ∧ (Xor (Xor (i ∈ X) (i ∈ Y)) (Carry i X Y)))



-- Exercise V.4.19

-- namespace V0ExtModel
variable {num str : Type} [M : V0ExtModel num str]

open V0ExtModel V0Model BASICModel


lemma len_empty : len (0 : str) = (0 : num) := by
  false_or_by_contra
  rename_i h
  obtain ⟨pred, pred_le, pred_eq⟩ := B12 (num := num) h
  have witness := L2 pred_eq
  have aux := @ax_empty _ _ M pred
  apply @not_lt_zero _ _ _ pred
  apply aux.mp
  exact witness

/-- Majority predicate on three propositions. -/
def Maj (P Q R : Prop) :=
  (P ∧ Q ∧ ¬ R) ∨ (P ∧ ¬ Q ∧ R) ∨ (¬ P ∧ Q ∧ R) ∨ (P ∧ Q ∧ R)

lemma Maj_true2 {P Q R : Prop} : Q -> (Maj P Q R <-> P ∨ R) := by
  intro h
  unfold Maj
  tauto
lemma Maj_true3 {P Q R : Prop} : R -> (Maj P Q R <-> P ∨ Q) := by
  intro h
  unfold Maj
  tauto



open IDelta0Model

lemma carry_rec1 : ∀ {X Y : str}, ∀ {i : num},
  Carry i X Y -> (i ∈ X ∨ i ∈ Y) -> Carry (i + 1) X Y :=
by
  intro X Y i h ixy
  obtain ⟨c, c_lt, cx, cy, cprev⟩ := h
  exists c
  refine ⟨?_, cx, cy, ?_⟩
  · rw [<- B11]
    exact c_lt.1
  intro j
  by_cases j = i
  · rename_i hji
    intro _ hcj
    rw [hji]
    cases ixy with
    | inl ix => left; exact ix
    | inr iy => right; exact iy
  · rename_i hji
    intro hlt hcj
    exact cprev j (lt_of_le_of_ne (by rw [B11]; exact hlt) hji) hcj

lemma not_lt_self : ∀ (i : num), ¬ i < i := by
  intro i h
  rw [<- lt_self_iff_false i]
  exact h

lemma carry_rec2 : ∀ {X Y : str}, ∀ {i : num},
  i ∈ X ∧ i ∈ Y -> Carry (i + 1) X Y :=
by
  intro X Y i h_XY
  obtain ⟨h_X, h_Y⟩ := h_XY
  unfold Carry
  exists i
  refine ⟨lt_succ i, h_X, h_Y, ?_⟩
  intro j hj hi
  rw [<- B11] at hj
  exfalso
  apply not_lt_self i
  exact lt_of_lt_of_le hi hj

-- Exercise V.4.18
lemma carry_rec : ∀ {X Y : str}, ∀ {i : num},
  (¬ Carry (0 : num) X Y) ∧ (Carry (i + 1) X Y ↔ Maj (Carry i X Y) (i ∈ X) (i ∈ Y)) := by
  intro X Y i
  constructor
  · intro h
    obtain ⟨_, lt, _⟩ := h
    exact V0Model.not_lt_zero lt
  · constructor
    · intro h
      obtain ⟨pos, lt, inX, inY, prevs⟩ := h
      by_cases h_pos : i = pos
      · rw [h_pos]
        unfold Maj
        right; right
        rw [<- or_and_right]
        constructor
        · exact em' (Carry pos X Y)
        · constructor <;> assumption
      · rw [<- B11] at lt
        have hlt : pos < i := lt_of_le_of_ne lt (Ne.symm h_pos)
        clear h_pos lt
        have h_pos := prevs i (by rw [<- B11]) hlt
        rcases h_pos with h_iX | h_iY
        · rw [Maj_true2 h_iX]
          left
          unfold Carry
          exists pos
          refine ⟨hlt, inX, inY, ?_⟩
          intro j hj
          apply prevs
          apply lt_trans hj
          exact lt_succ i
        · rw [Maj_true3 h_iY]
          left
          unfold Carry
          exists pos
          refine ⟨hlt, inX, inY, ?_⟩
          intro j hj
          apply prevs
          apply lt_trans hj
          exact lt_succ i
    · intro h
      rcases h with ⟨hC, hX, _⟩ | ⟨hC, _, hY⟩ | h_notCarry | h_all
      · apply carry_rec1 hC (.inl hX)
      · apply carry_rec1 hC (.inr hY)
      · apply carry_rec2 h_notCarry.2
      · apply carry_rec2 h_all.2

lemma exists_of_len_lt :
    ∀ {X Y : str}, (len X : num) < len Y ->
      ∃ z, z ∈ Y ∧ z ∉ X ∧ z + 1 = len Y := by
  intro X Y h_lt
  have h_len_ne_zero : len Y ≠ (0 : num) := by
    intro h_len_zero
    rw [h_len_zero] at h_lt
    exact V0Model.not_lt_zero h_lt
  obtain ⟨len_pred, pred_le, pred_eq⟩ := B12 (num := num) h_len_ne_zero
  have pred_in := L2 pred_eq
  rw [lt_iff_le_not_ge] at h_lt
  exists len_pred
  refine ⟨pred_in, ?_, pred_eq⟩
  intro h_in_X
  apply h_lt.2
  rw [B11]
  rw [<- pred_eq]
  rw [add_lt_add_iff_right]
  apply L1
  exact h_in_X

lemma exists_of_len_lt' :
    ∀ {X : str}, ∀ {i : num}, i < len X ->
      ∃ z, z ∈ X ∧ i ≤ z ∧ z + 1 = len X := by
  intro X i h_lt
  have h_len_ne_zero : len X ≠ (0 : num) := by
    intro h_len_zero
    rw [h_len_zero] at h_lt
    exact V0Model.not_lt_zero h_lt
  obtain ⟨len_pred, pred_le, pred_eq⟩ := B12 (num := num) h_len_ne_zero
  have pred_in := L2 pred_eq
  rw [lt_iff_le_not_ge] at h_lt
  exists len_pred
  refine ⟨pred_in, ?_, pred_eq⟩
  rw [B11]
  rw [pred_eq]
  constructor
  · exact h_lt.1
  · intro h
    apply h_lt.2
    exact h

lemma len_pos_of_exists : ∀ {i : num} {X : str}, i ∈ X -> len X > (0 : num) := by
  intro i X iX
  exact lt_of_le_of_lt zero_le (L1 iX)




lemma xor3_split {P Q R : Prop} :
    Xor (Xor P Q) R <->
      (P ∧ ¬Q ∧ ¬R) ∨ (¬ P ∧ Q ∧ ¬ R) ∨ (¬ P ∧ ¬ Q ∧ R) ∨ (P ∧ Q ∧ R) := by
  unfold Xor
  tauto






lemma carry_lt_add_len :
    ∀ {X Y : str} {i : num},
      Carry i X Y ->
      i < len X + len Y := by
  intro X Y i h_Carry
  obtain ⟨k, h_k_lt_i, h_kX, h_kY, h_kprop⟩ := h_Carry
  have h_i_ne_zero : i ≠ 0 := by
    intro h_i_zero
    rw [h_i_zero] at h_k_lt_i
    exact V0Model.not_lt_zero h_k_lt_i
  obtain ⟨pred_i, hpred_i_le, hpred_i_eq⟩ := B12 h_i_ne_zero
  have h_len_X_pos : (0 : num) < len X := len_pos_of_exists h_kX
  have h_len_Y_pos : (0 : num) < len Y := len_pos_of_exists h_kY
  have h_pred_or : pred_i ∈ X ∨ pred_i ∈ Y := by
    by_cases h_k_eq_pred : k = pred_i
    · subst h_k_eq_pred
      exact Or.inl h_kX
    · have h_pred_lt_i : pred_i < i := by
        simpa [hpred_i_eq] using (lt_succ pred_i)
      have h_k_le_pred : k ≤ pred_i := by
        rw [B11, hpred_i_eq]
        exact h_k_lt_i
      have h_k_lt_pred : k < pred_i := lt_of_le_of_ne h_k_le_pred h_k_eq_pred
      exact h_kprop pred_i h_pred_lt_i h_k_lt_pred
  rcases h_pred_or with h_predX | h_predY
  · have h_i_le_lenX : i ≤ len X := by
      rw [<- hpred_i_eq, B11]
      exact (add_lt_add_iff_right 1).mpr (L1 h_predX)
    exact lt_of_le_of_lt h_i_le_lenX (lt_add_of_pos_right (len X) h_len_Y_pos)
  · have h_i_le_lenY : i ≤ len Y := by
      rw [<- hpred_i_eq, B11]
      exact (add_lt_add_iff_right 1).mpr (L1 h_predY)
    exact lt_of_le_of_lt h_i_le_lenY (by
      simpa [_root_.add_comm] using (lt_add_of_pos_right (len Y) h_len_X_pos))


lemma str_eq_of_mem_iff : ∀ {X Y : str}, (∀ y : num, y ∈ X ↔ y ∈ Y) -> X = Y := by
  intro X Y h_mem
  have h_len : len X = (len Y : num) := by
    rcases lt_trichotomy (len X : num) (len Y : num) with h_lt | h_eq | h_gt
    · exfalso
      obtain ⟨z, h_z_in_Y, h_z_notin_X, _⟩ := exists_of_len_lt (X := X) (Y := Y) h_lt
      exact h_z_notin_X ((h_mem z).mpr h_z_in_Y)
    · exact h_eq
    · exfalso
      obtain ⟨z, h_z_in_X, h_z_notin_Y, _⟩ := exists_of_len_lt (X := Y) (Y := X) h_gt
      exact h_z_notin_Y ((h_mem z).mp h_z_in_X)
  exact M.SE h_len (fun y _ => h_mem y)
