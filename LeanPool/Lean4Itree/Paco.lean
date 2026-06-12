/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.Paco.Paco
import LeanPool.Lean4Itree.Paco.PacoDefs
import LeanPool.Lean4Itree.Paco.PacoTactics

/-!
# Parameterized coinduction (Paco)

Aggregator module re-exporting the vendored parameterized-coinduction library:
the parameterized least fixed point `plfp` and its accumulation principle
`plfp_acc` together with the supporting tactics (`PacoTactics`) and notations
(`Paco`).
-/
