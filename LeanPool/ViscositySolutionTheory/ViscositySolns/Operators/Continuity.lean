/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Proper

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Continuity and boundedness hypotheses for operators

This file packages continuity and local boundedness assumptions for fully
nonlinear operators through `operatorGraphEval`, the graph-space evaluation map
used by closed-semijet arguments.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/-- An operator is continuous when its graph-space evaluation map is continuous. -/
def OperatorContinuous (F : Operator n) : Prop :=
  Continuous (operatorGraphEval F)

/--
An operator is continuous on a graph-space set when its graph-space evaluation
map is continuous there.
-/
def OperatorContinuousOn (S : Set ((Point n × Real) × Jet n)) (F : Operator n) : Prop :=
  ContinuousOn (operatorGraphEval F) S

/-- An operator is locally bounded when its graph-space evaluation is locally bounded. -/
def OperatorLocallyBounded (F : Operator n) : Prop :=
  ∀ z : (Point n × Real) × Jet n,
    ∃ M : Real, ∀ᶠ y in nhds z, |operatorGraphEval F y| <= M

/--
An operator is locally bounded on a graph-space set when its graph-space
evaluation is locally bounded in the relative topology of that set.
-/
def OperatorLocallyBoundedOn (S : Set ((Point n × Real) × Jet n)) (F : Operator n) : Prop :=
  ∀ z : (Point n × Real) × Jet n, z ∈ S ->
    ∃ M : Real, ∀ᶠ y in nhdsWithin z S, |operatorGraphEval F y| <= M

theorem OperatorContinuous.continuous {F : Operator n} (hF : OperatorContinuous F) :
    Continuous (operatorGraphEval F) :=
  hF

theorem OperatorContinuousOn.continuousOn {S : Set ((Point n × Real) × Jet n)}
    {F : Operator n} (hF : OperatorContinuousOn S F) :
    ContinuousOn (operatorGraphEval F) S :=
  hF

theorem OperatorContinuous.operatorContinuousOn {S : Set ((Point n × Real) × Jet n)}
    {F : Operator n} (hF : OperatorContinuous F) :
    OperatorContinuousOn S F :=
  hF.continuousOn

theorem OperatorContinuous.isClosed_le_zero {F : Operator n} (hF : OperatorContinuous F) :
    IsClosed {z : (Point n × Real) × Jet n | operatorGraphEval F z <= 0} :=
  isClosed_Iic.preimage hF.continuous

theorem OperatorContinuous.isClosed_zero_le {F : Operator n} (hF : OperatorContinuous F) :
    IsClosed {z : (Point n × Real) × Jet n | 0 <= operatorGraphEval F z} :=
  isClosed_Ici.preimage hF.continuous

theorem OperatorContinuous.locallyBounded {F : Operator n}
    (hF : OperatorContinuous F) : OperatorLocallyBounded F := by
  intro z
  let f := operatorGraphEval F
  refine ⟨|f z| + 1, ?_⟩
  have hball : ∀ᶠ y in nhds z, dist (f y) (f z) < 1 :=
    hF.continuous.continuousAt.eventually
      (Metric.ball_mem_nhds (f z) zero_lt_one)
  filter_upwards [hball] with y hy
  have habs : |f y - f z| < 1 := by
    simpa [Real.dist_eq, abs_sub_comm] using hy
  have htri : |f y| <= |f z| + |f y - f z| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_add_le (f z) (f y - f z)
  linarith

theorem OperatorContinuousOn.locallyBoundedOn
    {S : Set ((Point n × Real) × Jet n)} {F : Operator n}
    (hF : OperatorContinuousOn S F) : OperatorLocallyBoundedOn S F := by
  intro z hz
  let f := operatorGraphEval F
  refine ⟨|f z| + 1, ?_⟩
  have hball : ∀ᶠ y in nhdsWithin z S, dist (f y) (f z) < 1 :=
    (hF.continuousOn z hz).eventually
      (Metric.ball_mem_nhds (f z) zero_lt_one)
  filter_upwards [hball] with y hy
  have habs : |f y - f z| < 1 := by
    simpa [Real.dist_eq, abs_sub_comm] using hy
  have htri : |f y| <= |f z| + |f y - f z| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_add_le (f z) (f y - f z)
  linarith

theorem OperatorContinuous.locallyBoundedOn
    {S : Set ((Point n × Real) × Jet n)} {F : Operator n}
    (hF : OperatorContinuous F) : OperatorLocallyBoundedOn S F :=
  hF.operatorContinuousOn.locallyBoundedOn

theorem OperatorLocallyBounded.locallyBoundedOn
    {S : Set ((Point n × Real) × Jet n)} {F : Operator n}
    (hF : OperatorLocallyBounded F) : OperatorLocallyBoundedOn S F := by
  intro z hz
  rcases hF z with ⟨M, hM⟩
  exact ⟨M, hM.filter_mono nhdsWithin_le_nhds⟩

end ViscositySolns
