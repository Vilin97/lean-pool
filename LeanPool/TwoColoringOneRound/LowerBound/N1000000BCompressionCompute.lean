/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSi

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionCompute
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- This file is intentionally lightweight: it re-exports the modularized computation lemmas
-- and definitions needed downstream (basis construction, `S0` identity, and `Si` identity).

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound

