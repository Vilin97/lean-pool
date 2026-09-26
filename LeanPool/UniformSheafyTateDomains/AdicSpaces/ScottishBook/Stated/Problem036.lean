/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletedAlgClosure

/-!
# Nonarchimedean Scottish Book — Problem 36

**Proposer:** Kiran Kedlaya
**Date:** 5 February 2021

## Problem Statement

Let K = completed algebraic closure of F_p((t)). When is a continuous
endomorphism f: K → K an isomorphism?

## Notes

None.

## Status

Open.

## Mathematical Background

Let `K` denote the completed algebraic closure of `F_p((t))`. A
continuous endomorphism `f : K → K` is a ring homomorphism that is
continuous with respect to the nonarchimedean topology.

The problem asks for a characterization of which continuous
endomorphisms are isomorphisms (i.e., bijective with continuous
inverse). This is related to Problem 23, which gives a sufficient
condition for non-surjectivity.

One natural question is whether bijectivity alone suffices: if `f` is
a bijective continuous endomorphism, is the inverse automatically
continuous? This is an automatic continuity / open mapping question
for nonarchimedean fields.

More broadly, the problem asks for intrinsic conditions on `f` (or on
`f(t)`) that characterize when `f` is an isomorphism.

## Definitions formalized

1. `CompletedAlgClosure.ContinuousEnd.IsIso` — a continuous
   endomorphism is an isomorphism (bijective with continuous inverse)
2. `problem36` — bijectivity implies isomorphism (the automatic
   continuity direction)

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 36
-/

@[expose] public section

namespace ScottishBook

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- A continuous endomorphism of `CompletedAlgClosure p` is an
**isomorphism** if it is bijective and admits a continuous two-sided
inverse (which is then necessarily a ring homomorphism). -/
def CompletedAlgClosure.ContinuousEnd.IsIso
    (f : CompletedAlgClosure.ContinuousEnd p) : Prop :=
  Function.Bijective f.toRingHom ∧
    ∃ g : CompletedAlgClosure.ContinuousEnd p,
      f.toRingHom.comp g.toRingHom = RingHom.id _ ∧
      g.toRingHom.comp f.toRingHom = RingHom.id _

/-- **Scottish Book Problem 36** (Kedlaya, 5 Feb 2021, open):

*Characterize when a continuous endomorphism of the completed
algebraic closure of `F_p((t))` is an isomorphism.*

We state the automatic continuity direction: a bijective continuous
endomorphism is an isomorphism (the inverse is automatically
continuous).  This is the minimal nontrivial implication; the full
problem asks for intrinsic conditions on `f` or `f(t)`.

This is an **open problem** — the `sorry` is intentional. -/
theorem problem36
    (f : CompletedAlgClosure.ContinuousEnd p)
    (hbij : Function.Bijective f.toRingHom) :
    f.IsIso := by
  sorry

end ScottishBook
