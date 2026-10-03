/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import Mathlib.Algebra.Group.Action.End

/-!
# Cayley's theorem for monoids

* `monoid_faithful_self` — every monoid acts faithfully on itself: the left-regular
  representation `MulAction.toEndHom : N →* Function.End N` is injective.
-/

public section

namespace LeanPool.KrohnRhodes

universe u

/-- **Every monoid acts faithfully on itself.**  The left-regular
representation `MulAction.toEndHom : N →* Function.End N` (sending `n` to
left-multiplication by `n`) is injective: `n` is recovered as the image of
`1` under left-multiplication by `n`. -/
theorem monoid_faithful_self (N : Type u) [Monoid N] :
    Function.Injective (MulAction.toEndHom (M := N) (α := N)) := by
  intro a b h
  have hab : a * 1 = b * 1 := congrArg (fun f : Function.End N => f 1) h
  simpa only [mul_one] using hab

end LeanPool.KrohnRhodes
