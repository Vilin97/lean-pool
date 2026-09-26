/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Doubling
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29

/-!
# The odd line of the doubling

The ℤ/2-graded doubling of a tensor category always contains an
odd line: the monoidal unit placed in odd degree squares to the
unit and self-braids by `−1`.  This is Deligne's device for the
general case of 2.11, where the category itself need not contain
such an object.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- **The odd line of the doubling**: the unit in odd degree. -/
noncomputable def doubledOddLine
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A] [HasBinaryBiproducts A]
    [HasZeroObject A] : OddLine (Doubled A) where
  obj := Doubled.oddUnit
  sq := Doubled.oddUnitSq
  braid_neg := Doubled.braiding_oddUnit

end RS
