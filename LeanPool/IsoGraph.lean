/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.IsoGraph.Canon.Spec
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Verified canonical labelling of finite graphs

Source: url:https://github.com/Timeroot/IsoGraph
Authors: Alex Meiburg
Status: verified
Main declarations: `IsoGraph.Canon.canonAdj_eq_iff`, `IsoGraph.Canon.canonAdj_relabel`
Tags: graph-theory, graph-isomorphism, canonical-labelling, verified-algorithms
MSC: 05C60, 68R10
-/

@[expose] public section

/-!
## Imported scope

This is the verified individualisation-refinement canonical-labelling core from IsoGraph. It
includes the executable mini-nauty algorithm, its equivariance and search-optimality proofs, and
the public specification identifying equality of canonical forms with graph isomorphism. The
larger IsoGraph library, including its enumeration tables and native-decide computations, is not
part of this import.
-/
