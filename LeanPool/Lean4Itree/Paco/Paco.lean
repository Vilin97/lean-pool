/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.Paco.PacoDefs

/-!
# Paco notations

Re-exports the parameterized-coinduction definitions and tactics from
`PacoDefs`. The lattice notations `⊤ₚ` (top) and `⊓ₚ` (meet) used by the Paco
development are declared there with a `ₚ` suffix to avoid clashing with the
`Lean.Order` complete-lattice notations (`⊤`, `⊓`) that Lean core now brings
into scope.
-/
