/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeBase
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSi

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionCompute
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- This file is intentionally lightweight: it re-exports the modularized computation lemmas
-- and definitions needed downstream (basis construction, `S0` identity, and `Si` identity).

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound

