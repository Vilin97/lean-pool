/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Nat.Prime.Defs

/-!
# Basic imports and shared notation

This file is imported by all modules. It carries shared notation and
small utility lemmas that do not belong to a specific submodule.

## Project scope

We formalize **Ulm's theorem**: two countable reduced abelian p-groups are
isomorphic iff their Ulm invariants agree at every ordinal.

The supporting layer — the transfinite Ulm filtration `p^α G`, the socle,
heights, purity, and Kaplansky's extension lemma — lives in `Lib/PGroups/` and
`Lib/Ulm/`, and is reusable independently of the theorem.

## Notation

Throughout we work with additive abelian groups.
- `p ^ n • x` : the n-fold p-multiple of x (standard Mathlib nsmul)
- `pPow p n G` : Ulm subgroup p^n · G ⊆ G  (ℕ-indexed)
- `ulmSubgroup p α G` : Ulm subgroup p^α · G ⊆ G  (Ordinal-indexed)
- `ulmInvariant p α G` : dim_{ℤ/pℤ} (P_α / P_{α+1}) where `P_α = G[p] ∩ p^α G`
- `ulmLength p G` : least α with p^α G = 0  (for reduced groups)
-/

namespace UlmsTheorem

end UlmsTheorem
