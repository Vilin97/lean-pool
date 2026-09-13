/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! Kernel verification of the two normalized second-stage coloring trees. -/

@[expose] public section

namespace HadwigerNelsonBounds

/-- The middle-color normalized second-stage certificate checks by reduction. -/
theorem partsGadgetMiddleCertificate_verifies :
    partsGadgetMiddleCertificate.Verifies := by
  decide

end HadwigerNelsonBounds
