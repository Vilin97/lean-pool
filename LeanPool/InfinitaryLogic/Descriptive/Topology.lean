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

/-- `StructureSpace L` inherits the product topology from `RelQuery L → Bool`.
Since `Bool` has the discrete topology, this is the product of discrete spaces. -/
instance : TopologicalSpace (StructureSpace L) := Pi.topologicalSpace

end Language

end FirstOrder
