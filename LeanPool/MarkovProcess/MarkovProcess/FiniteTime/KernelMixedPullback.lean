/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelConcatenation

/-!
# Pulling a finite-time concatenation back to mixed labels

This file records the reindexing step after an ordered finite-dimensional law has been split at
a designated cut.  A mixed label may select a past coordinate, a strict-future coordinate, or
the terminal past coordinate.  The last alternative permits a future-zero label to duplicate a
terminal past label without requiring either label to be present.

The result is pure finite-dimensional Chapman--Kolmogorov algebra.  In particular it has no
continuity, density, path-space, or Feller hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]

/-- Pull a split finite path back to arbitrary past and future label types.  `none` selects the
terminal past coordinate; this is the coordinate used by a future label representing elapsed
time zero. -/
def pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n))
    (z : (Fin (m + 1) → alpha) × (Fin n → alpha)) :
    pastLabel ⊕ futureLabel → alpha
  | Sum.inl i => z.1 (pastIndex i)
  | Sum.inr j => (futureIndex j).elim (z.1 (Fin.last m)) z.2

/-- Pullback to mixed labels is measurable, including when either label type is empty and when
several labels select the terminal coordinate. -/
theorem measurable_pullbackSplitFinitePath {m n : ℕ}
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    Measurable
      (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [measurable_pi_iff]
  rintro (i | j)
  · exact (measurable_pi_apply (pastIndex i)).comp measurable_fst
  · cases h : futureIndex j with
    | none =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply (Fin.last m)).comp measurable_fst)
    | some k =>
        simpa only [pullbackSplitFinitePath, h] using!
          ((measurable_pi_apply k).comp measurable_snd)

namespace IsConservative

/-- Concatenation at an ordered cut remains valid after pulling the two pieces back to arbitrary
mixed labels.  Mapping a future label to `none` reads the cut coordinate from the past, so the
theorem directly permits simultaneous terminal-past/future-zero observations. -/
theorem finiteTimeKernel_map_pullbackSplitFinitePath
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (m n : ℕ) (times : FiniteOrderedTimes (n + (m + 1)))
    (pastIndex : pastLabel → Fin (m + 1))
    (futureIndex : futureLabel → Option (Fin n)) :
    (finiteTimeKernel P times).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex ∘
          splitFinitePath (alpha := alpha) (m := m) (n := n)) =
      (finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := m))
          measurable_splitPastTerminal).map
        (pullbackSplitFinitePath (alpha := alpha) pastIndex futureIndex) := by
  rw [Kernel.map_comp_right]
  · rw [hP.finiteTimeKernel_map_splitFinitePath P m n times]
  · exact measurable_splitFinitePath
  · exact measurable_pullbackSplitFinitePath pastIndex futureIndex

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
