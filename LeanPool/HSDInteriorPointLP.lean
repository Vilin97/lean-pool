/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/
module

public import LeanPool.HSDInteriorPointLP.GeneratedConvergence
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Homogeneous self-dual interior-point method for linear programming

Source: doi:10.1287/moor.19.1.53
Authors: Makoto Yamashita
Status: verified
Main declarations: `HSDInteriorPointLP.YTM_fixed_local_theory_from_paper`
Tags: linear-programming, interior-point-methods, optimization, homogeneous-self-dual
MSC: 90C05, 90C51
-/

@[expose] public section

/-!
Top-level import for the HSD interior-point LP proof.

For ordinary use, import this module.  For development, edit the files under
`HSDInteriorPointLP/` in the order described in `README.md`.
-/
