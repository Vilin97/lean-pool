/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import LeanPool.LeanCwf.CwF

/-!
# Categories with Families in Lean

Source: url:https://github.com/JoeyEremondi/lean-cwf
Authors: Joseph Eremondi
Status: verified
Main declarations: `LeanPool.LeanCwf.CwF.CwF`, `LeanPool.LeanCwf.CwF.ext_decomp`, `LeanPool.LeanCwf.CwF.termSecEquiv`, `LeanPool.LeanCwf.CwF.StrictPreserveCwF`
Tags: category-theory, type-theory, categorical-logic
MSC: 18N45, 03B15
-/

/-!
## Mathematical overview

This project formalizes basic infrastructure for categories with families
(CwFs): a family category over types, presheaf-style type and term families,
context extension operations, the CwF laws for projections and variables, and
strict morphisms between CwFs.

The main results include the decomposition of a substitution into an extension
arrow (`ext_decomp`), the equivalence between terms and sections of display
maps (`termSecEquiv`), and the category of CwFs with strict structure-preserving
morphisms.

## Provenance

Imported from <https://github.com/JoeyEremondi/lean-cwf>. Upstream is
BSD-3-Clause-licensed; redistributed here under Apache-2.0 as part of Lean
Pool. The source package has no pinned `lean-toolchain` in this clone; it was
ported to Lean Pool's `leanprover/lean4:v4.30.0-rc2` toolchain.
-/
