/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project, √2
-/

import LeanPool.Odlyzko.ExplicitFormula.PoitouEstimate

/-!
# Poitou's Explicit Odlyzko Bound for Root Discriminants

Source: url:https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/
Authors: The FLT Project, √2
Status: verified
Main declarations: `NumberField.Odlyzko.odlyzkoBound`
Tags: number-theory, discriminants, number-fields, explicit-formula
MSC: 11R29, 11R42
-/

/-!
# Odlyzko's bound for totally complex number fields

This project formalizes the unconditional explicit-formula argument giving
Poitou's effective Odlyzko bound for root discriminants. It includes the
analytic continuation and functional equation of the completed Dedekind zeta
function, the explicit formula, the Tartar test function, and a certified
numerical estimate.

The source was contributed to the FLT project by GitHub user `sqrt-of-2` and
adapted here at commit `01370b013e55c83f1994af814cd31cb8fb2ef653`.
-/
