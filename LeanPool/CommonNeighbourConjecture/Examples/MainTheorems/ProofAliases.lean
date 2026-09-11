/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import LeanPool.CommonNeighbourConjecture.Examples.MainTheorems.Internal

import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Compatibility import for the main-theorem proof

The definitions and internal proof now share one API. This module remains as
a compatibility import for downstream users of the original file layout.
-/

@[expose] public section
