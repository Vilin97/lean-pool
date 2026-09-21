/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Units
/-!
# Open finite-index subgroups of a field's multiplicative group
-/

namespace ClassFieldTheory

universe u

/-- An open finite-index subgroup of the multiplicative group `Kˣ`.  The
inherited order is ordinary subgroup inclusion. -/
abbrev OpenFiniteIndexSubgroup
    (K : Type u) [Field K] [TopologicalSpace K] :=
  { H : Subgroup Kˣ // IsOpen (H : Set Kˣ) ∧ H.FiniteIndex }

end ClassFieldTheory
