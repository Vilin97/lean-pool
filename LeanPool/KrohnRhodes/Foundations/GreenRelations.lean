/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import Mathlib.Algebra.Group.Defs

/-!
# Green's relations

* `Green.L`, `Green.R` — Green's left and right relations on a monoid
  (`a L b ↔ ∃ s t, s * a = b ∧ t * b = a`, and dually for `R`);
* `Green.H` — their intersection;
* `Green.IsAperiodicElem a` — the `H`-class of `a` is trivial. A finite monoid is aperiodic
  (has only trivial subgroups) iff all of its elements satisfy this.

## References

* [J.A. Green, *On the structure of semigroups*, Ann. Math. 1951]
* [J.-E. Pin, *Mathematical Foundations of Automata Theory*, 2022]
-/

public section

namespace LeanPool.KrohnRhodes

namespace Green

variable {M : Type*} [Monoid M]

/-! ### Green's L-relation -/

/-- Green's L-relation: `a` and `b` generate the same principal left ideal.
    In a monoid, `a L b` iff there exist `s, t` with `s * a = b` and `t * b = a`. -/
@[expose]
def L (a b : M) : Prop :=
  ∃ s t : M, s * a = b ∧ t * b = a

/-! ### Green's R-relation -/

/-- Green's R-relation: `a` and `b` generate the same principal right ideal.
    In a monoid, `a R b` iff there exist `s, t` with `a * s = b` and `b * t = a`. -/
@[expose]
def R (a b : M) : Prop :=
  ∃ s t : M, a * s = b ∧ b * t = a

/-! ### Green's H-relation -/

/-- Green's H-relation: intersection of L and R.
    `a H b` iff `a L b` and `a R b`. -/
@[expose]
def H (a b : M) : Prop :=
  L a b ∧ R a b

/-! ### Aperiodic elements and monoids -/

/-- An element `a` is aperiodic if its H-class is trivial (a singleton).
    Equivalently, `a H b → a = b`. -/
@[expose]
def IsAperiodicElem (a : M) : Prop :=
  ∀ b : M, H a b → a = b

end Green

end LeanPool.KrohnRhodes
