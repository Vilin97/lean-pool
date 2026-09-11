/-
Copyright (c) 2026 Bhavik Mehta, Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# LeanPool.ABCExceptions.ForMathlib.RingTheory.Radical
-/

@[expose] public section

namespace UniqueFactorizationMonoid

open Qq Lean Mathlib.Meta Finset

namespace Mathlib.Meta.Positivity
open Positivity

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for radical. Proves radicals are nonzero. -/
@[positivity UniqueFactorizationMonoid.radical _]
def evalRadical : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@radical _ $inst $inst' $inst'' $n) =>
    have _ := ← synthInstanceQ q(Nontrivial $α)
    assertInstancesCommute
    return .nonzero q(radical_ne_zero)
  | _ => throwError "not radical"

example : 0 < radical 100 := by
  positivity

end Mathlib.Meta.Positivity

end UniqueFactorizationMonoid
