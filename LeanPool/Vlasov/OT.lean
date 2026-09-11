/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.CharacteristicFlow
public import LeanPool.Vlasov.OT.Coupling
public import LeanPool.Vlasov.OT.Wasserstein
public import LeanPool.Vlasov.OT.WeakToLagrangian
public import LeanPool.Vlasov.OT.WellPosedness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch

/-! # Optimal transport, characteristic flow, and the well-posedness ladder. -/

@[expose] public section
