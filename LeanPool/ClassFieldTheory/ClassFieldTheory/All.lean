/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalFieldTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.All
/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory.

The library contains local class field theory and global class field theory
for number fields, including the Hilbert product formula, general
power-residue reciprocity, and Gauss quadratic reciprocity, together with the
Hasse--Arf and Kronecker--Weber theorems. Shared valuation, ramification,
cohomology, Kummer, local-field, and Lubin--Tate infrastructure lives beside
those theories rather than under a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.
-/

