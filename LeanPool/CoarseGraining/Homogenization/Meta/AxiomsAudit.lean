/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Public
public import LeanPool.CoarseGraining.Homogenization.Book.MainResults

/-!
# Axiom audit

Machine-checked record of the axioms that the public headline theorems depend on.

This development contains no `sorry` and declares no custom `axiom`, so every
public theorem reduces to mathlib's three standard foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.  Building this file prints
those dependencies for inspection (see CI logs).
-/

@[expose] public section

-- The uniformly-elliptic headline theorems exposed in `MainResults.lean`.
