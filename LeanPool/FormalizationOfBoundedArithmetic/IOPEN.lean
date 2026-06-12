/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- for a quick demo, jump straight to `theorem add_assoc`
import Mathlib.Tactic.Core
import Mathlib.Logic.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
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

/-!
# LeanPool.FormalizationOfBoundedArithmetic.IOPEN
-/

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
  simpComplexity at ind
  simpInduction at ind
  rw [forall_swap_231]
  apply ind ?base ?step
  · intro x y
    change (x + y) + 0 = x + (y + 0)
    exact (B3 (x + y)).trans (congrArg (fun t => x + t) (B3 y).symm)
  · intro z hInd x y
    change (x + y) + (z + 1) = x + (y + (z + 1))
    calc
      (x + y) + (z + 1) = ((x + y) + z) + 1 := B4 (x := x + y) (y := z)
      _ = (x + (y + z)) + 1 := congrArg (fun t => t + 1) (hInd x y)
      _ = x + ((y + z) + 1) := (B4 (x := x) (y := y + z)).symm
      _ = x + (y + (z + 1)) := congrArg (fun t => x + t) (B4 (x := y) (y := z)).symm

-- lemma for O2; "induction on y, first establishing the special cases y = 0 and y = 1..."
-- proof: induction on x
lemma add_zero_comm
  : ∀ x : M, x + 0 = 0 + x :=
by
  have ind := iopen.open_induction <| display1
    (((x + 0) =' (0 + x)) : Formula _ (Vars1 .x))
  simpComplexity at ind
  simpInduction at ind
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
  simpComplexity at ind
  simpInduction at ind
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
  simpComplexity at ind
  simpInduction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    exact add_zero_comm x
  · intro a hInd b
    change b + (a + 1) = (a + 1) + b
    have hInd' : b + a = a + b := by
      exact hInd b
    calc
      b + (a + 1) = (b + a) + 1 := B4 (x := b) (y := a)
      _ = (a + b) + 1 := congrArg (fun t => t + 1) hInd'
      _ = a + (b + 1) := (B4 (x := a) (y := b)).symm
      _ = a + (1 + b) := congrArg (fun t => a + t) (add_one_comm b)
      _ = (a + 1) + b := (add_assoc a 1 b).symm

-- O3. x · (y + z) = (x · y) + (x · z) (Distributive law)
  -- proof: induction on z
theorem mul_add
  : ∀ x y z : M, x * (y + z) = (x * y) + (x * z) :=
by
  have ind := iopen.open_induction <| display3 .z
     ((x * (y + z)) =' ((x * y) + (x * z)) : Formula _ (Vars3 .z .x .y))
  simpComplexity at ind
  simpInduction at ind
  rw [forall_swap_231]
  apply ind ?base ?step
  · intro a b
    change a * (b + 0) = a * b + a * 0
    exact (congrArg (fun t => a * t) (B3 b)).trans
      ((B3 (a * b)).symm.trans (congrArg (fun t => a * b + t) (B5 (x := a)).symm))
  · intro b hInd_b a2 a3
    change a2 * (a3 + (b + 1)) = a2 * a3 + a2 * (b + 1)
    have hInd' : a2 * (a3 + b) = a2 * a3 + a2 * b := by
      exact hInd_b a2 a3
    calc
      a2 * (a3 + (b + 1)) = a2 * ((a3 + b) + 1) :=
        congrArg (fun t => a2 * t) (B4 (x := a3) (y := b))
      _ = a2 * (a3 + b) + a2 := B6 (x := a2) (y := a3 + b)
      _ = (a2 * a3 + a2 * b) + a2 := congrArg (fun t => t + a2) hInd'
      _ = a2 * a3 + (a2 * b + a2) := add_assoc (a2 * a3) (a2 * b) a2
      _ = a2 * a3 + a2 * (b + 1) :=
        congrArg (fun t => a2 * a3 + t) (B6 (x := a2) (y := b)).symm

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
    simpComplexity at ind
    simpInduction at ind
    rw [forall_swap_231]
    apply ind ?base ?step
    · intro x y
      change (x * y) * 0 = x * (y * 0)
      calc
        (x * y) * 0 = 0 := B5 (x := x * y)
        _ = x * 0 := (B5 (x := x)).symm
        _ = x * (y * 0) := congrArg (fun t => x * t) (B5 (x := y)).symm
    · intro x hInd_x y z
      change (y * z) * (x + 1) = y * (z * (x + 1))
      have hInd' : (y * z) * x = y * (z * x) := by
        exact hInd_x y z
      calc
        (y * z) * (x + 1) = (y * z) * x + y * z := B6 (x := y * z) (y := x)
        _ = y * (z * x) + y * z := congrArg (fun t => t + y * z) hInd'
        _ = y * (z * x) + y * (z * 1) :=
          congrArg (fun t => y * (z * x) + t) (congrArg (fun t => y * t) (mul_one z).symm)
        _ = y * (z * x + z * 1) := (mul_add y (z * x) (z * 1)).symm
        _ = y * (z * x + z) := congrArg (fun t => y * (z * x + t)) (mul_one z)
        _ = y * (z * (x + 1)) := congrArg (fun t => y * t) (B6 (x := z) (y := x)).symm

lemma zero_mul
  : ∀ x : M, 0 * x = 0 :=
by
  have ind := iopen.open_induction <| display1
    (((0 * x) =' 0) : Formula _ (Vars1 .x))
  simpComplexity at ind
  simpInduction at ind
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
  simpComplexity at ind
  simpInduction at ind
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
  simpComplexity at ind
  simpInduction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    change (x + 1) * 0 = x * 0 + 0
    exact (B5 (x := x + 1)).trans ((B5 (x := x)).symm.trans (B3 (x * 0)).symm)
  · intro y hInd_y x
    change (x + 1) * (y + 1) = x * (y + 1) + (y + 1)
    have hInd' : (x + 1) * y = x * y + y := by
      exact hInd_y x
    calc
      (x + 1) * (y + 1) = (x + 1) * y + (x + 1) := B6 (x := x + 1) (y := y)
      _ = (x * y + y) + (x + 1) := congrArg (fun t => t + (x + 1)) hInd'
      _ = x * y + (y + (x + 1)) := add_assoc (x * y) y (x + 1)
      _ = x * y + ((y + x) + 1) :=
        congrArg (fun t => x * y + t) (B4 (x := y) (y := x))
      _ = x * y + ((x + y) + 1) :=
        congrArg (fun t => x * y + (t + 1)) (add_comm y x)
      _ = x * y + (x + (y + 1)) :=
        congrArg (fun t => x * y + t) (B4 (x := x) (y := y)).symm
      _ = (x * y + x) + (y + 1) := (add_assoc (x * y) x (y + 1)).symm
      _ = x * (y + 1) + (y + 1) :=
        congrArg (fun t => t + (y + 1)) (B6 (x := x) (y := y)).symm

-- O5. x · y = y · x (Commutativity of ·)
theorem mul_comm
  : ∀ x y : M, x * y = y * x :=
by
  have ind := iopen.open_induction <| display2 .y
    (((x * y) =' (y * x)) : Formula _ (Vars2 .y .x))
  simpComplexity at ind
  simpInduction at ind
  rw [forall_comm]
  apply ind ?base ?step
  · intro x
    exact (B5 (x := x)).trans (zero_mul x).symm
  · intro x hInd_x y
    change y * (x + 1) = (x + 1) * y
    have hInd' : y * x = x * y := by
      exact hInd_x y
    calc
      y * (x + 1) = y * x + y := B6 (x := y) (y := x)
      _ = x * y + y := congrArg (fun t => t + y) hInd'
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
    simpComplexity at ind
    simpInduction at ind
    rw [forall_swap_231]
    apply ind ?base ?step
    · intro x y
      change x + 0 = y + 0 → x = y
      intro h
      exact (B3 x).symm.trans (h.trans (B3 y))
    · intro x hInd_x y z
      change y + (x + 1) = z + (x + 1) → y = z
      intro h
      apply hInd_x
      apply B2
      calc
        (y + x) + 1 = y + (x + 1) := (B4 (x := y) (y := x)).symm
        _ = z + (x + 1) := h
        _ = (z + x) + 1 := B4 (x := z) (y := x)

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
  simpComplexity at ind
  simpInduction at ind
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
