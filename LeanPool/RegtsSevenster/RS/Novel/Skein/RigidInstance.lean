/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ExactPairingInstance

/-!
# Rigidity of the skein category

Every object is self-dual: the exact self-pairing at arity `n` is
assembled by induction from the single-strand pairing, using the
unit pairing at arity zero and the tensor product of exact
pairings for the step (the arity arithmetic `n + 1` is
definitional, and the flip `1 + n = n + 1` is transported along
`eqToIso`).
-/

namespace RS

open CategoryTheory MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The exact self-pairing at every arity. -/
@[instance_reducible]
noncomputable def strandPairingAll :
    (n : ℕ) →
      ExactPairing (SkeinObj.mk (f := f) n) (SkeinObj.mk n)
  | 0 => exactPairingUnit
  | n + 1 =>
    letI : ExactPairing (SkeinObj.mk (f := f) n)
        (SkeinObj.mk n) := strandPairingAll n
    letI : ExactPairing
        (SkeinObj.mk (f := f) n ⊗ SkeinObj.mk 1)
        (SkeinObj.mk 1 ⊗ SkeinObj.mk n) :=
      ExactPairing.tensor
    exactPairingCongrRight
      (X := SkeinObj.mk (f := f) (n + 1))
      (Y := SkeinObj.mk (f := f) (n + 1))
      (Y' := SkeinObj.mk (f := f) (1 + n))
      (eqToIso (congrArg SkeinObj.mk (Nat.add_comm n 1)))

/-- Every skein object is its own right dual. -/
noncomputable instance skeinHasRightDual (X : SkeinObj f) :
    HasRightDual X where
  rightDual := X
  exact := strandPairingAll f X.arity

/-- And its own left dual — the category is rigid. -/
noncomputable instance skeinHasLeftDual (X : SkeinObj f) :
    HasLeftDual X where
  leftDual := X
  exact := strandPairingAll f X.arity

/-- **The skein category is rigid.** -/
noncomputable instance skeinRigid : RigidCategory (SkeinObj f) where

end RS
