/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.FormalizedArithmetic
import LeanPool.Incompleteness.Arith.Theory
import LeanPool.Incompleteness.Arith.D1
import LeanPool.Incompleteness.Arith.D3
import LeanPool.Incompleteness.Arith.First
import LeanPool.Incompleteness.Arith.Second
import LeanPool.Incompleteness.Arith.DC
import LeanPool.Incompleteness.DC.Basic

import LeanPool.Incompleteness.ProvabilityLogic.Basic

/-!
# Gödel's First and Second Incompleteness Theorems

Source: doi:10.1007/BF01700692
Authors: Palalansoukî
Status: verified
Main declarations: `LeanPool.Incompleteness.goedelFirst`, `LeanPool.Incompleteness.goedelSecond`
Tags: incompleteness, provability, first-order-arithmetic, mathematical-logic
MSC: 03F40, 03F30
-/

namespace LeanPool.Incompleteness

/-- Metadata alias for Gödel's first incompleteness theorem. -/
theorem goedelFirst (T : LO.FirstOrder.Theory ℒₒᵣ) [𝐑₀ wkn T]
    [LO.FirstOrder.Arith.Sigma1Sound T] [T.Delta1Definable] :
    ¬LO.Entailment.Complete T :=
  LO.FirstOrder.Arith.goedel_first_incompleteness T

/-- Metadata alias for Gödel's second incompleteness theorem. -/
theorem goedelSecond (T : LO.FirstOrder.Theory ℒₒᵣ) [𝐈Sg1 wkn T] [T.Delta1Definable]
    [LO.Entailment.Consistent T] :
    T ⊬ ↑T.consistentₐ :=
  LO.FirstOrder.Arith.goedel_second_incompleteness T

end LeanPool.Incompleteness
