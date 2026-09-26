/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Definitions in the public statement

This module contains the transparent definitions used by the solution.  They are repeated in
`Challenge.lean`, whose statement is checked independently by the comparator.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lower one-density of `s` at `x`, normalized by the diameter `2 * r` of a ball. -/
def lowerOneDensity (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r))
    (nhdsWithin 0 (Ioi 0))

/-- A set is countably one-rectifiable if Lipschitz curves cover it up to Hausdorff null measure. -/
def IsCountablyOneRectifiable (s : Set X) : Prop :=
  ∃ f : ℕ → ℝ → X,
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧ μH[1] (s \ ⋃ i, range (f i)) = 0

/-- Every finite-measure set with lower density at least `β` is one-rectifiable. -/
def ForcesOneRectifiability (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (β : ℝ≥0∞) : Prop :=
  ∀ s : Set X, MeasurableSet s → μH[1] s < ∞ →
    (∀ᵐ x ∂μH[1].restrict s, β ≤ lowerOneDensity s x) →
      IsCountablyOneRectifiable s

/-- The infimum of the nonnegative thresholds forcing one-rectifiability in `X`. -/
def sigmaOne (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)}

/-- The isolated radical system whose first coordinate is twice the six-point endpoint. -/
def IsEndpointPair (c B : ℝ) : Prop :=
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A := Real.sqrt ((B ^ 2 - 1) / 2)
  let C := Real.sqrt ((B ^ 2 + D ^ 2) / 2 - c ^ 2)
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - c ^ 2) / 2
  13866128436518096 / 10 ^ 16 < c ∧ c < 13866128436518100 / 10 ^ 16 ∧
    2873744161801659 / 10 ^ 15 < B ∧ B < 2873744161801662 / 10 ^ 15 ∧
    A + C = 3 * c * b + c ^ 2 - 1 ∧
    (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) ∧
    x < 0 ∧ z < 0 ∧ k - x * z < 0

/-- Twice the optimal six-point constant, defined by its isolated exact system. -/
def cStar : ℝ :=
  sInf {c : ℝ | ∃ B : ℝ, IsEndpointPair c B}

/-- The optimal two-colour six-point constant. -/
def sStar : ℝ :=
  cStar / 2

end LeanPool.Besicovitch
