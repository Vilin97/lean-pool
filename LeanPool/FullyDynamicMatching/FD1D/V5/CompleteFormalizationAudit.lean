/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.PaperStatements
public import Mathlib.Util.AssertNoSorry

/-!
# Proof-closure audit

The commands below reject proof placeholders and nonstandard axioms in the
paper-facing theorem and its principal producer lemmas.
-/

@[expose] public section

open Lean Meta Elab Command

private meta def isStandardAxiom (name : Name) : Bool :=
  name == ``propext ||
    name == ``Classical.choice ||
    name == ``Quot.sound

/-- Reject a declaration if its dependency closure contains a custom axiom. -/
elab "assert_only_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  for axiomName in axioms do
    unless isStandardAxiom axiomName do
      throwError "{n} depends on nonstandard axiom {axiomName}"

assert_no_sorry FD1D.V5.limsup_trajectoryRMSCostFromState_le_log_succ
assert_only_standard_axioms
  FD1D.V5.limsup_trajectoryRMSCostFromState_le_log_succ

assert_no_sorry
  FD1D.V5.finite_horizon_expected_joinedTrajectoryCost_le_log_succ
assert_only_standard_axioms
  FD1D.V5.finite_horizon_expected_joinedTrajectoryCost_le_log_succ

assert_no_sorry FD1D.V5.hierarchicalPolicy_resourceGuarantees
assert_only_standard_axioms FD1D.V5.hierarchicalPolicy_resourceGuarantees

assert_no_sorry FD1D.V5.full_formalization
assert_only_standard_axioms FD1D.V5.full_formalization

assert_no_sorry FD1D.V5.Palomar.optimalDynamicMatchingUpperBound
assert_only_standard_axioms
  FD1D.V5.Palomar.optimalDynamicMatchingUpperBound
