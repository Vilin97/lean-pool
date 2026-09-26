/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.Shift
public import Mathlib.Probability.Process.Stopping


/-!
# Measurability of random shifts of continuous paths

Shifting a continuous path by a Borel measurable random time, and evaluating it at that time,
are Borel measurable, because the deterministic shift and the evaluation are jointly continuous
in the time and the path.  A finite `NNReal`-valued stopping time for the canonical filtration is
such a random time.  No countable-range premise is used.

This is ordinary measurability infrastructure.  It proves no restart identity and no conditional
expectation formula; those are in `Trajectory/FellerStoppingRestart.lean` and
`Trajectory/FellerStoppingConditional.lean`.
-/

@[expose] public section

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Shifting by a Borel measurable random time is Borel measurable. -/
theorem measurable_shift_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega ↦ shift (T omega) omega) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (T omega, omega)) :=
    hT.prodMk measurable_id
  exact (continuous_shift (alpha := alpha)).measurable.comp hpair

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluating a path at a Borel measurable random time is Borel measurable. -/
theorem measurable_eval_of_measurable (T : ContinuousPath alpha → NNReal)
    (hT : Measurable T) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega (T omega)) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha ↦ (omega, T omega)) :=
    measurable_id.prodMk hT
  exact (ContinuousEval.continuous_eval (F := ContinuousPath alpha)).measurable.comp hpair

/-- A finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_of_isStoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable T := by
  refine measurable_of_Iic fun i ↦ ?_
  have h := (canonicalFiltration (alpha := alpha)).le i _ (hT i)
  simpa only [Set.preimage, Set.mem_Iic, WithTop.coe_le_coe] using h

/-- Shifting by a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_shift_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega ↦ shift (T omega) omega) :=
  measurable_shift_of_measurable T (measurable_of_isStoppingTime T hT)

/-- The state at a finite stopping time for the canonical filtration is Borel measurable. -/
theorem measurable_eval_stoppingTime_borel (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega (T omega)) :=
  measurable_eval_of_measurable T (measurable_of_isStoppingTime T hT)

end ContinuousPath
end MarkovProcess
