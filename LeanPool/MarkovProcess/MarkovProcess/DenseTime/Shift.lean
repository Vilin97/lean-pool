/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.Shift
public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension


/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

@[expose] public section

noncomputable section PortComputability

namespace MarkovProcess

section

namespace DenseTime

/-- Addition by a fixed dense time as an order embedding of the dense time carrier. -/
def addOrderEmbedding (s : DenseTime) : DenseTime ↪o DenseTime :=
  OrderEmbedding.ofStrictMono (fun t ↦ s + t) fun _ _ h ↦ by
    simpa only [add_comm] using add_lt_add_left h s

@[simp]
theorem addOrderEmbedding_apply (s t : DenseTime) : addOrderEmbedding s t = s + t := rfl

/-- Embedding a rational-time sum into physical time gives the sum of the embedded times. -/
@[simp]
theorem castOrderEmbedding_add (s t : DenseTime) :
    castOrderEmbedding (s + t) = castOrderEmbedding s + castOrderEmbedding t := by
  change ((s + t : DenseTime) : NNReal) = (s : NNReal) + (t : NNReal)
  norm_cast

end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

/-- Shift a dense-time path by a fixed nonnegative rational time. -/
def shift (s : DenseTime) (path : DenseTime → alpha) : DenseTime → alpha :=
  path ∘ DenseTime.addOrderEmbedding s

@[simp]
theorem shift_apply (s t : DenseTime) (path : DenseTime → alpha) :
    shift s path t = path (s + t) := rfl

@[simp]
theorem shift_zero (path : DenseTime → alpha) : shift 0 path = path := by
  funext t
  simp only [shift_apply, zero_add]

theorem shift_add (s t : DenseTime) (path : DenseTime → alpha) :
    shift t (shift s path) = shift (s + t) path := by
  funext r
  simp only [shift_apply, add_assoc]

variable [MeasurableSpace alpha]

/-- Shifting dense-time paths by a fixed time is measurable for the product measurable space. -/
theorem measurable_shift (s : DenseTime) :
    Measurable (shift s : (DenseTime → alpha) → DenseTime → alpha) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply (s + t)

end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Restricting a path after a rational physical-time shift is the same as shifting its
dense-time restriction. -/
theorem denseRestriction_shift (s : DenseTime) (omega : ContinuousPath alpha) :
    denseRestriction
        (shift (DenseTime.castOrderEmbedding s) omega) =
      DenseTimePath.shift s (denseRestriction omega) := by
  funext t
  simp only [denseRestriction_apply, shift_apply, DenseTimePath.shift_apply,
    DenseTime.castOrderEmbedding_add]

end ContinuousPath
end
end MarkovProcess

end PortComputability
