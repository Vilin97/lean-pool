/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import LeanPool.LeanCwf.Fam
import LeanPool.LeanCwf.Basics
import LeanPool.LeanCwf.Category

/-!
# Categories with Families

Source: url:https://github.com/JoeyEremondi/lean-cwf
Authors: Joseph Eremondi
Status: verified
Main declarations: `LeanPool.LeanCwf.CwF.Structure`
Tags: type-theory, category-theory, categories-with-families
MSC: 03B15, 18D20
-/

/-!
## Mathematical overview

This import develops a categorical presentation of categories with families
(CwFs). It defines families as arrows in `Type`, packages the type-and-term
presheaf of a CwF, formalizes context extension and its uniqueness laws, and
develops morphisms of CwFs preserving that structure strictly.

## Provenance

Imported from <https://github.com/JoeyEremondi/lean-cwf>, originally licensed
under BSD-3-Clause by Joseph Eremondi, and ported to Lean Pool's Lean
v4.30.0-rc2 / Mathlib v4.30.0-rc2 target.
-/
