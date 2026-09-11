/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData3
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-! Kernel checks for hard-case certificate group 3. -/

@[expose] public section

namespace HadwigerNelsonBounds

theorem partsGadgetHardCertificate12_verifies :
    partsGadgetHardCertificate12.Verifies := by
  decide

theorem partsGadgetHardCertificate13_verifies :
    partsGadgetHardCertificate13.Verifies := by
  decide

theorem partsGadgetHardCertificate14_verifies :
    partsGadgetHardCertificate14.Verifies := by
  decide

theorem partsGadgetHardCertificate15_verifies :
    partsGadgetHardCertificate15.Verifies := by
  decide

end HadwigerNelsonBounds
