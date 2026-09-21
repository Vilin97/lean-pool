/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
/-!
# Closed fixing subgroups

This module packages the closed subgroup attached to an intermediate field in
the Krull topology.
-/

noncomputable section

namespace RamificationTheory

/-- The closed fixing subgroup attached to an intermediate field. -/
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩

end RamificationTheory
