/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Monad
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Auto
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# ``probWhile`` Properties

This file proves evaluation and normalization results about ``probWhile``.
-/

noncomputable section

namespace SLang

variable {T} [Preorder T]

/--
The ``probWhile`` program is monotonic in terms of the number of unrollings.
-/
theorem probWhileCut_monotonic (cond : T → Bool) (body : T → SLang T)
  (init : T) (x : T) :
  Monotone (fun n : Nat => probWhileCut cond body n init x) := by
  apply monotone_nat_of_le_succ
  intro n
  revert init
  induction n
  · intro init
    simp [probWhileCut]
  · rename_i n IH
    intro init
    simp [probWhileCut,probWhileFunctional]
    split
    · rename_i COND
      unfold probBind
      unfold SLang.probPure
      simp
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_right
      exact IH a
    · simp

/--
The ``probWhile`` term evaluates to the pointwise limit of the ``probWhileCut`` term
-/
@[simp]
theorem probWhile_apply (cond : T → Bool) (body : T → SLang T) (init : T) (x : T) (v : ENNReal) :
  Filter.Tendsto (fun i => probWhileCut cond body i init x) Filter.atTop (nhds v) →
  probWhile cond body init x = v := by
  intro H
  unfold probWhile
  apply iSup_eq_of_tendsto
  · apply probWhileCut_monotonic
  · apply H

end SLang
