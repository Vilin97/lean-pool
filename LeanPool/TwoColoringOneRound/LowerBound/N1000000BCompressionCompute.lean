/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

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

