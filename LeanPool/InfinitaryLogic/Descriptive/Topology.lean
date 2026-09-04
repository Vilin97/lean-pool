/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.Measurable
import Mathlib.Topology.Clopen

/-!
# Product Topology on the Structure Space

This file equips `StructureSpace L` with the product topology (from `RelQuery L → Bool`
with `Bool` discrete) and proves that cylinder sets are clopen.

## Main Results

- `instTopologicalSpaceStructureSpace`: Product topology on `StructureSpace L`.
- `isClopen_relHolds`: The set `{c | c q = true}` is clopen for each query `q`.
- `isOpen_relHolds`, `isClosed_relHolds`: Components of the clopen result.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

-- Generic instance: StructureSpaceOn is abbrev, so TC sees through it.
instance {α : Type*} : TopologicalSpace (StructureSpaceOn L α) := Pi.topologicalSpace

/-- The set of codes where a given relation query returns `true` is clopen (generic). -/
theorem isClopen_relHoldsOn {α : Type*} (q : RelQueryOn L α) :
    IsClopen {c : StructureSpaceOn L α | c q = true} := by
  have : {c : StructureSpaceOn L α | c q = true} = (fun c => c q) ⁻¹' {true} := by
    ext c; simp
  rw [this]
  exact (isClopen_discrete {true}).preimage (continuous_apply q)

/-- `StructureSpace L` inherits the product topology from `RelQuery L → Bool`.
Since `Bool` has the discrete topology, this is the product of discrete spaces. -/
instance : TopologicalSpace (StructureSpace L) := Pi.topologicalSpace

/-- The set of codes where a given relation query returns `true` is clopen.
This follows from the projection `c ↦ c q` being continuous and `{true}` being
clopen in discrete `Bool`. -/
theorem isClopen_relHolds (q : RelQuery L) :
    IsClopen {c : StructureSpace L | c q = true} := by
  have : {c : StructureSpace L | c q = true} = (fun c => c q) ⁻¹' {true} := by
    ext c; simp
  rw [this]
  exact (isClopen_discrete {true}).preimage (continuous_apply q)

/-- The set of codes where a given relation query returns `true` is open. -/
theorem isOpen_relHolds (q : RelQuery L) :
    IsOpen {c : StructureSpace L | c q = true} :=
  (isClopen_relHolds q).isOpen

/-- The set of codes where a given relation query returns `true` is closed. -/
theorem isClosed_relHolds (q : RelQuery L) :
    IsClosed {c : StructureSpace L | c q = true} :=
  (isClopen_relHolds q).isClosed

end Language

end FirstOrder
