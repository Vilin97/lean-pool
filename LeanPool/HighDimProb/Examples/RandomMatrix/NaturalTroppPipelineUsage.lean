/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.TraceExp

/-!
# Natural Tropp pipeline usage

This examples-only file shows the new natural-state Tropp route at the
TraceExp layer. It demonstrates the canonical prefix/suffix state endpoints and
checks the provider names without introducing application-specific assumptions.

The route still keeps the conditional-step analytic primitive, history
measurability, independence, trace-exp integrability, log/K comparison, CFC, and
variance-proxy inputs explicit in core theorem signatures.
-/

namespace HighDimProb.Examples.RandomMatrix.NaturalTroppPipelineUsage

open MeasureTheory

noncomputable section

/-- The natural trace state starts at the full scaled random sum. -/
theorem naturalTropp_traceState_zero_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    troppTraceState theta X K 0 =
      fun omega =>
        traceMatrixExp
          (randomMatrixSum (scaledRandomMatrixFamily theta X) omega) := by
  exact troppNaturalState_zero theta X K

/-- The natural trace state ends at the full deterministic comparison sum. -/
theorem naturalTropp_traceState_last_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) :
    troppTraceState theta X K (Fin.last m) =
      fun _omega : Omega =>
        traceMatrixExp (Finset.univ.sum fun i : Fin m => K i) := by
  exact troppNaturalState_last theta X K

/-- The left adjacent state is the natural history plus the current random step. -/
theorem naturalTropp_traceState_left_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    troppStateLeft theta X K i =
      fun omega =>
        traceMatrixExp
          (troppStateHistory theta X K i omega +
            troppCurrentRandomStep theta X i omega) := by
  exact troppNaturalState_left theta X K i

/-- The right adjacent state is the natural history plus the current comparison step. -/
theorem naturalTropp_traceState_right_usage {Omega : Type*}
    [MeasurableSpace Omega] {m n : Nat} (theta : Real)
    (X : Fin m -> RandomMatrix Omega n n)
    (K : Fin m -> Matrix (Fin n) (Fin n) Real) (i : Fin m) :
    troppStateRight theta X K i =
      fun omega =>
        traceMatrixExp
          (troppStateHistory theta X K i omega +
            troppCurrentComparisonStep K i) := by
  exact troppNaturalState_right theta X K i

end

end HighDimProb.Examples.RandomMatrix.NaturalTroppPipelineUsage
