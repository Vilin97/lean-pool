/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty


/-!
# Joint regularity of strongly continuous semigroups on `C₀`

Strong continuity of a semigroup orbit in the `C₀` norm and continuity of
evaluation give continuity, jointly in time and state, of the evaluated orbit.
The corresponding Borel measurability statement follows without any additional
regularity premise on the semigroup.

This is a generic functional-analytic API. It makes no representation claim
about the semigroup.
-/

@[expose] public section

open scoped ZeroAtInfty

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {α : Type*} [TopologicalSpace α]

/-- A strongly continuous `C₀`-semigroup orbit is jointly continuous in time
and state after evaluation. -/
theorem continuous_apply_apply
    (S : StronglyContinuousContractionSemigroup C₀(α, ℝ)) (f : C₀(α, ℝ)) :
    Continuous fun tx : NNReal × α ↦ S tx.1 f tx.2 :=
  ((ZeroAtInftyContinuousMap.isometry_toBCF (α := α) (β := ℝ)).continuous.comp
    ((S.continuous f).comp continuous_fst)).eval continuous_snd

/-- Joint evaluation of a strongly continuous `C₀`-semigroup orbit is Borel
measurable for the product measurable space. -/
theorem measurable_apply_apply
    [MeasurableSpace α] [BorelSpace α]
    (S : StronglyContinuousContractionSemigroup C₀(α, ℝ)) (f : C₀(α, ℝ)) :
    Measurable fun tx : NNReal × α ↦ S tx.1 f tx.2 :=
  (S.continuous_apply_apply f).measurable

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
