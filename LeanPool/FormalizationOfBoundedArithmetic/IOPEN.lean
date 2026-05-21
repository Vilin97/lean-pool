/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- for a quick demo, jump straight to `theorem add_assoc`
import Mathlib.Tactic.Core
import Mathlib.Logic.Basic
import Mathlib.Tactic

import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Semantics

import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.Semantics
import LeanPool.FormalizationOfBoundedArithmetic.Complexity
import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
import LeanPool.FormalizationOfBoundedArithmetic.SimpRules

open FirstOrder Language BoundedFormula

/-- Models of BASIC arithmetic satisfying open induction. -/
class IOPENModel (num : Type*) extends BASICModel num where
  open_induction {n} {a : Type} [IsEnum a]
    (phi : peano.BoundedFormula ((Vars1 n) ⊕ a) 0) :
    phi.IsOpen -> (mkInductionSentence phi).Realize num

namespace IOPENModel

universe u v
variable {M : Type u} [iopen : IOPENModel M]


-- page 36 of draft (47 of pdf)
-- Example 3.8 The following formulas (and their universal closures) are theorems of IOPEN:
open BASICModel Formula Term

open Lean Elab Tactic

theorem forall_swap_231 {α β γ} {p : α -> β -> γ -> Prop}
  : (∀ x y z, p x y z) <-> (∀ z x y, p x y z) :=
  ⟨fun f z x y  => f x y z, fun f y z x => f x y z⟩

-- O1. (x + y) + z = x + (y + z) (Associativity of +)
-- proof: induction on z
theorem add_assoc
  : ∀ x y z : M, (x + y) + z = x + (y + z) :=
by
  -- TODO: how to make Lean infer these formulas?
  let phi : peano.Formula (Vars3 .z .x .y) :=
    ((x + y) + z) =' (x + (y + z))
  have ind := iopen.open_induction <| display3 .z phi
  unfold phi at ind
  simp_complexity at ind
  simp_induction at ind
  rw [forall_swap_231]
  apply ind ?base ?step
  · intro x y
    rw [B3 (x + y)]
    rw [B3 y]
  · intro z hInd x y
    rw [B4]
    rw [B4]
    rw [B4]
    rw [<- (B2 (x + y + z) (x + (y + z)))]
    rw [hInd]

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
-- proof: induction on x
lemma add_zero_comm
  : ∀ x : M, x + 0 = 0 + x :=
by
  have ind := iopen.open_induction <| display1
    (((x + 0) =' (0 + x)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step
  · trivial
  · intro a ha
    rw [← add_assoc]
    rw [← ha]
    rw [B3]
    rw [B3]

-- this is necessary to prove axiom `C` from BasicExt
lemma zero_add
  : ∀ x : M, 0 + x = x :=
by
  intro a
  rw [<- add_zero_comm]
  exact B3 a

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
theorem add_one_comm
  : ∀ x : M, x + 1 = 1 + x :=
by
  have ind := iopen.open_induction <| display1
    (((x + 1) =' (1 + x)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step
  · calc
      (0 : M) + 1 = 1 := zero_add 1
      _ = 1 + 0 := (B3 1).symm
  · intro a ha
    rw [<- add_assoc]
    rw [ha]

-- O2. x + y = y + x (Commutativity of +)
-- proof : induction on y, first establishing the special cases y = 0 and y = 1
theorem add_comm
  : ∀ x y : M, x + y = y + x :=
by
  have ind := iopen.open_induction <| display2 .y
    (((x + y) =' (y + x)) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    exact add_zero_comm x
  · intro a hInd b
    rw [<- add_assoc]
    rw [hInd]
    rw [add_assoc]
    calc
      a + (b + 1) = a + (1 + b) := by rw [add_one_comm b]
      _ = a + 1 + b := by rw [<- add_assoc]

-- O3. x · (y + z) = (x · y) + (x · z) (Distributive law)
  -- proof: induction on z
theorem mul_add
  : ∀ x y z : M, x * (y + z) = (x * y) + (x * z) :=
by
  have ind := iopen.open_induction <| display3 .z
     ((x * (y + z)) =' ((x * y) + (x * z)) : Formula _ (Vars3 .z .x .y))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_swap_231]
  apply ind ?base ?step
  · intro a b
    rw [B3]
    rw [B5]
    rw [B3]
  · intro b hInd_b a2 a3
    rw [add_comm]
    rw [add_assoc]
    rw [add_comm]
    rw [hInd_b]
    conv => lhs; left; rw [add_comm]; rw [B6]
    rw [B6]
    conv => rhs; right; rw [add_comm]
    rw [add_assoc]

theorem mul_one
  : ∀ x : M, x * 1 = x :=
by
  intro x
  calc
    x * 1 = x * ((0 : M) + 1) := by rw [zero_add 1]
    _ = x * 0 + x := B6
    _ = 0 + x := congrArg (fun y => y + x) B5
    _ = x := zero_add x

-- O4. (x · y) · z = x · (y · z) (Associativity of ·)
  -- proof: induction on z, using O3
theorem mul_assoc
  : ∀ x y z : M, (x * y) * z = x * (y * z) :=
  by
    have ind := iopen.open_induction <| display3 .z
      ((((x * y) * z) =' (x * (y * z))) : Formula _ (Vars3 .z .x .y))
    simp_complexity at ind
    simp_induction at ind
    rw [forall_swap_231]
    apply ind ?base ?step
    · intro x y
      rw [B5]
      rw [B5]
      rw [B5]
    · intro x hInd_x y z
      rw [mul_add]
      rw [mul_add]
      calc
        y * z * x + y * z * 1 = y * (z * x) + y * z := by
          rw [hInd_x]
          rw [mul_one]
        _ = y * (z * x) + y * (z * 1) := by rw [mul_one]
        _ = y * (z * x + z * 1) := (mul_add y (z * x) (z * 1)).symm

lemma zero_mul
  : ∀ x : M, 0 * x = 0 :=
by
  have ind := iopen.open_induction <| display1
    (((0 * x) =' 0) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step
  · rw [B5]
  · intro x hInd_0_x
    rw [B6]
    rw [hInd_0_x]
    rw [B3]

lemma one_mul
  : ∀ x : M, 1 * x = x :=
by
  have ind := iopen.open_induction <| display1
    (((1 * x) =' x) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step
  · rw [B5]
  · intro x hInd_1_x
    rw [B6]
    rw [hInd_1_x]

lemma mul_add_1_left
  : ∀ x y : M, (x + 1) * y = x * y + y :=
by
  have ind := iopen.open_induction <| display2 .y
    (((x + 1) * y) =' ((x * y) + y) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    rw [B5]
    rw [B5]
    rw [B3]
  · intro y hInd_y x
    rw [B6]
    rw [B6]
    rw [hInd_y]
    conv => lhs; rw [add_assoc]; right; rw [<- add_assoc]; left; rw [add_comm]
    conv => rhs; rw [add_assoc]; right; rw [<- add_assoc]

-- O5. x · y = y · x (Commutativity of ·)
theorem mul_comm
  : ∀ x y : M, x * y = y * x :=
by
  have ind := iopen.open_induction <| display2 .y
    (((x * y) =' (y * x)) : Formula _ (Vars2 .y .x))
  simp_complexity at ind
  simp_induction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    exact (B5 (x := x)).trans (zero_mul x).symm
  · intro x hInd_x y
    rw [B6]
    calc
      y * x + y = x * y + y := by rw [hInd_x]
      _ = (x + 1) * y := (mul_add_1_left x y).symm

example : Nonempty (True ∧ True) :=
  ⟨⟨⟨⟩, ⟨⟩⟩⟩

-- O6. x + z = y + z → x = y (Cancellation law for +)
namespace add_cancel_right

theorem mp
  : ∀ {x y z : M}, x + z = y + z → x = y :=
  by
    have ind := iopen.open_induction <| display3 .z
      (((x + z) =' (y + z) ⟹ (x =' y)) : Formula _ (Vars3 .z .x .y))
    simp_complexity at ind
    simp_induction at ind
    rw [forall_swap_231]
    apply ind ?base ?step
    · intro x y
      rw [B3]
      rw [B3]
      intro h
      exact h
    · intro x hInd_x y z
      conv => lhs; lhs; right; rw [add_comm]
      conv => lhs; rhs; right; rw [add_comm]
      rw [<- add_assoc]
      rw [<- add_assoc]
      intro h
      apply B2
      apply hInd_x
      exact h

end add_cancel_right

theorem add_cancel_right
  : ∀ {x y z : M}, x + z = y + z <-> x = y :=
by
  intro x y z
  constructor
  · exact add_cancel_right.mp
  · intro h
    rw [h]

theorem add_cancel_left
  : ∀ {x y z : M}, z + x = z + y <-> x = y :=
by
  intro x y z
  constructor
  · conv => rw [add_comm]; lhs; rhs; rw [add_comm]
    apply add_cancel_right.mp
  · intro h
    rw [h]

-- O7. 0 ≤ x
theorem zero_le
  : ∀ x : M, 0 ≤ x :=
by
  intro x
  rw [<- B3 x]
  rw [add_comm]
  apply B8

-- O8. x ≤ 0 → x = 0
theorem le_zero_eq
  : ∀ x : M, x ≤ 0 → x = 0 :=
by
  intro x h
  apply B7
  · exact h
  · apply zero_le

-- O9. x ≤ x
-- This is proved already as BASICModel.le_refl (doesn't need induction)
-- theorem le_refl
--   : ∀ x : M, x ≤ x :=
-- by
--   intro x
--   conv => right; rw [<- B3 x]
--   apply B8

-- O10. x ≠ x + 1
theorem ne_succ
  : ∀ x : M, x ≠ x + 1 :=
by
  have ind := iopen.open_induction <| display1
    ((x ≠' (x + 1)) : Formula _ (Vars1 .x))
  simp_complexity at ind
  simp_induction at ind
  apply ind ?base ?step
  · intro h
    -- TODO: why this self is necessary?
    exact (B1 (self := iopen.toBASICModel)) h.symm
  · intro a h hq
    apply h
    apply B2
    exact hq

theorem add_mul
  : ∀ x y z : M, (x + y) * z = x * z + y * z :=
by
  intro x y z
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm]
  conv => lhs; rhs; rw [mul_comm]

end IOPENModel
