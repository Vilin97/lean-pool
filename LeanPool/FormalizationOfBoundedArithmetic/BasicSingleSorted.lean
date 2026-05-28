/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Mathlib.ModelTheory.Semantics
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano

open FirstOrder FirstOrder.Language

universe u

-- Section 3.1 Peano Arithmetic; draft page 34 (45 of pdf)
-- semi-bundled design! inspired by mathlib Ring
-- extending peano.Structure instead of One, Add, ... is needed to .Realize
/-- Single-sorted models of the BASIC arithmetic axioms. -/
class BASICModel (num : Type u) extends
  peano.Structure.{u} num
where
  B1 : ∀ {x : num}, (x + 1) ≠ 0
  B2 : ∀ x y : num, (x + 1) = (y + 1) -> x = y
  B3 : ∀ x : num, x + 0 = x
  B4 : ∀ {x y : num}, x + (y + 1) = (x + y) + 1
  B5 : ∀ {x : num}, x * 0 = 0
  B6 : ∀ {x y : num}, x * (y + 1) = x * y + x
  -- le_antisymm
  B7 : ∀ {x y : num}, x <= y -> y <= x -> x = y
  -- le_self_add
  B8 : ∀ {x y : num}, x <= x + y


/-- BASIC models with the additional axiom `(0 : num) + 1 = 1`. -/
class BASICModelExt (num : Type u) extends BASICModel num where
-- skip this axiom by default
-- we will use induction anyway for IDelta0, and it is problematic
-- when defining 2-BASIC axioms and V^i later on

-- it is interesting because BASICModelExt alone implies all
-- true quantifier-free sentences over `peano` language!
-- (source: Logical Foundations, release, p. 40 (p. 58 of PDF))
  C : (0 : num) + 1 = 1

-- instance (M : Type*) [BASICModel M] : Zero M where
--   zero := 0

-- instance (M : Type*) [BASICModel M] : Add M where
--   add x y := x + y

-- instance (M : Type*) [BASICModel M] : Mul M where
--   mul x y := x * y

-- instance (M : Type*) [BASICModel M] : LE M where
--   le x y := x <= y

-- instance (M : Type*) [BASICModel M] : LT M where
--   lt x y := x <= y ∧ x ≠ y

variable {M} [BASICModel M]

/-- Interpret natural-number literals in a BASIC model by iterating successor. -/
def natToM : Nat -> M
| 0 => 0
| 1 => 1
| n + 1 => natToM n + 1

instance (n) : OfNat M n where
  ofNat := natToM n

/-- Pairing function used to encode two numbers as one number. -/
def pair (x y : M) := (x + y) * (x + y + 1) + (1 + 1) * y

/-- Pairing notation for two numbers. -/
notation "⟨" i "," j "⟩" => pair i j

/-- Pairing notation for three numbers. -/
notation "⟨" i "," j "," k "⟩" => pair (pair i j) k

namespace BASICModel

variable {M : Type u} [iopen : BASICModel M]

-- this is axctually O9. x ≤ x from Logical Foundations
theorem le_refl : ∀ a : M, a <= a := by
  intro x
  conv => right; rw [<- B3 x]
  apply B8

theorem zero_ne_add_one : ∀ x : M, x + 1 ≠ 0 := by apply B1
theorem one_add_right_regular : IsAddRightRegular (1 : M) := by apply B2


end BASICModel
