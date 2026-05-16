/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# A convenience alias for `discard_comp`

The basic deterministic kernels (`Kernel.id`, `Kernel.copy`, `Kernel.discard`, `Kernel.swap`)
that this file once defined are now in Mathlib. We only keep a `bind`-flavoured restatement of
`discard_comp` (`Measure.comp_discard`) that downstream files use as a simp lemma.
-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

@[simp]
lemma _root_.MeasureTheory.Measure.comp_discard (μ : Measure α) :
    μ.bind (Kernel.discard α) = μ .univ • (Measure.dirac PUnit.unit) := by
  ext s hs
  simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]

end ProbabilityTheory.Kernel
