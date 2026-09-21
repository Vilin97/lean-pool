/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Coherent Rings

A ring is *coherent* if every finitely generated ideal is finitely presented as a module.
This is a standard notion in commutative algebra (cf. Bourbaki, *Algèbre Commutative*,
Ch. I, §2, Exercise 12). A Noetherian ring is coherent, but the converse does not hold.

## Main definitions

* `IsCoherentRing R` : A ring `R` is coherent if every finitely generated ideal is finitely
  presented as an `R`-module.
-/

/-- A ring is *coherent* if every finitely generated ideal, viewed as a submodule,
is finitely presented. Equivalently, for every surjection `Rⁿ →ₗ[R] I` with `I`
finitely generated, the kernel is finitely generated.

This is a standard notion in commutative algebra (cf. Bourbaki, *Algèbre Commutative*,
Ch. I, §2, Exercise 12). A Noetherian ring is coherent, but the converse does not hold. -/
class IsCoherentRing (R : Type*) [Ring R] : Prop where
  /-- Every finitely generated ideal is finitely presented as a module. -/
  fg_ideal_finitePresentation : ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I
