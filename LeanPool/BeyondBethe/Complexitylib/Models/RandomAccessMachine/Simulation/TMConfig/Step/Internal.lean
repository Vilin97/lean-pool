/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Layout
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Load
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Action
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Dispatch
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal.Resources

/-!
# One-step TM-to-RAM simulation -- proof internals

This aggregation module contains the checked layout, head-symbol loading,
selected transition-action, nested finite-dispatch, and source-resource layers.
The public surface transfers the resulting measured execution to compiled RAM.
-/
