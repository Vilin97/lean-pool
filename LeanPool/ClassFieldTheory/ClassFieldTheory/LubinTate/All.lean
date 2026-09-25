/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.All
/-!
# Lubin--Tate theory

This is the public aggregate for Lubin--Tate theory.  It exports the formal
module foundations, the characteristic-independent standard finite-level
division fields and their lower/upper ramification formulas, and the explicit
equal-characteristic construction.  The
norm-subgroup calculation and transport used by local class field theory are
exported from `LocalClassFieldTheory.LubinTateApplication`, and the
field-facing existence theorem from
`LocalClassFieldTheory.Finite.Existence.EqualCharacteristic`.
The equal-characteristic construction is organized by its mathematical stages
below `LubinTate.EqualCharacteristic`.
-/

@[expose] public section
