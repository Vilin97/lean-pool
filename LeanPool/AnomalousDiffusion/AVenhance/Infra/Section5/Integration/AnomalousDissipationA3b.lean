/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.AnomalousDissipation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular

/-! # Main theorem from the two remaining estimates, step-down and classical well-posedness

Stream-function estimates (`AVenhance.limit_field_regular`) is proved, so its
literal-statement hypothesis of `anomalous_dissipation_of_keystones` is discharged by the theorem
itself.  Only step-down and classical well-posedness remain, as literal hypotheses. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- Main theorem from the literal step-down and classical well-posedness statements
    (stream-function estimates is proved). -/
theorem anomalous_dissipation_of_A8_A1c
    (hA8 : ∀ β C₀ : ℝ, IndyStepDownContract β C₀)
    (hA1c : ClassicalWellposedContract) :
    AnomalousDissipationStatement :=
  anomalous_dissipation_of_keystones hA8 hA1c (fun β => AVenhance.limit_field_regular β)

end AVenhance.Infra.Section5.Integration
