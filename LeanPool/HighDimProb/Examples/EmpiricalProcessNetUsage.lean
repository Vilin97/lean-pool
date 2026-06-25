/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.EmpiricalProcess
import LeanPool.HighDimProb.MetricEntropy

/-!
# Empirical process net usage example

This examples-only file records a conservative finite-net workflow for
empirical-process style arguments. It demonstrates set-level event transfer and
covering-number bookkeeping, while leaving probabilistic finite-net deviation
control as an explicit local assumption.
-/

namespace HighDimProb.Examples.EmpiricalProcessNetUsage

open MeasureTheory

noncomputable section

/-- Deviation event for a process over a class `F`. -/
def uniformDeviationEvent {Omega T : Type*}
    (Z : RandomProcess Omega T Real) (F : Set T) (t : Real) : Set Omega :=
  {omega | exists f, F f /\ t <= abs (Z f omega)}

/-- Finite-net transfer assumption: every large deviation over `F` produces a
large deviation on the chosen net `N`. -/
def FiniteNetDeviationTransfer {Omega T : Type*}
    (Z : RandomProcess Omega T Real) (F N : Set T) (t netLevel : Real) : Prop :=
  forall omega,
    uniformDeviationEvent Z F t omega ->
      uniformDeviationEvent Z N netLevel omega

/-- Pointwise event inclusion supplied by a finite-net transfer assumption. -/
theorem uniformDeviationEvent_subset_net {Omega T : Type*}
    [MeasurableSpace Omega]
    (Z : RandomProcess Omega T Real) (F N : Set T)
    (t netLevel : Real)
    (hTransfer : FiniteNetDeviationTransfer Z F N t netLevel) :
    Set.Subset (uniformDeviationEvent Z F t)
      (uniformDeviationEvent Z N netLevel) := by
  intro omega homega
  exact hTransfer omega homega

/-- Measure-level reduction from a class to its net. -/
theorem measure_uniformDeviationEvent_le_net {Omega T : Type*}
    [MeasurableSpace Omega]
    (P : Measure Omega) (Z : RandomProcess Omega T Real) (F N : Set T)
    (t netLevel : Real)
    (hTransfer : FiniteNetDeviationTransfer Z F N t netLevel) :
    P (uniformDeviationEvent Z F t) <=
      P (uniformDeviationEvent Z N netLevel) := by
  exact measure_mono
    (uniformDeviationEvent_subset_net Z F N t netLevel hTransfer)

/-- Local assumption for finite-net probabilistic control. -/
def FiniteNetDeviationBound {Omega T : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (Z : RandomProcess Omega T Real)
    (N : Set T) (netLevel : Real) (rhs : ENNReal) : Prop :=
  P (uniformDeviationEvent Z N netLevel) <= rhs

/-- Finite-net control plus transfer gives uniform control over the full
function class. -/
theorem uniformDeviationBound_of_finiteNet {Omega T : Type*}
    [MeasurableSpace Omega]
    (P : Measure Omega) (Z : RandomProcess Omega T Real)
    (F N : Set T) (t netLevel : Real) (rhs : ENNReal)
    (hTransfer : FiniteNetDeviationTransfer Z F N t netLevel)
    (hNet : FiniteNetDeviationBound P Z N netLevel rhs) :
    P (uniformDeviationEvent Z F t) <= rhs := by
  exact (measure_uniformDeviationEvent_le_net P Z F N t netLevel hTransfer).trans hNet

/-- Existing metric entropy API: a finite internal epsilon-net bounds the
covering number by the net cardinality. -/
theorem coveringNumber_le_card_of_finite_internal_net {T : Type*}
    [PseudoMetricSpace T] {F N : Set T} {eps : Real}
    (hNet : IsInternalEpsilonNet F N eps)
    (hFinite : N.Finite) :
    coveringNumber F eps <= (N.ncard : ENat) := by
  exact coveringNumber_le_card_of_isInternalEpsilonNet hNet hFinite

/-- A maximal separated set gives an internal net, hence a covering-number
bound when it is finite. -/
theorem coveringNumber_le_card_of_maximal_separated {T : Type*}
    [PseudoMetricSpace T] {F N : Set T} {eps : Real}
    (hMax : MaximalEpsilonSeparatedIn F N eps)
    (hFinite : N.Finite) :
    coveringNumber F eps <= (N.ncard : ENat) := by
  exact coveringNumber_le_card_of_finite_internal_net
    (isInternalEpsilonNet_of_maximalEpsilonSeparatedIn hMax) hFinite

end

end HighDimProb.Examples.EmpiricalProcessNetUsage
