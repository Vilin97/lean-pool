/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# The diagonal acceptance example

Staged for Tau Ceti, roadmap topic T09.  This is one entry of the **acceptance
list** in `TauCetiRoadmap/OperatorTheory/OperatorIdeals/README.md` (Part A): the
diagonal operator whose approximation numbers are its entries.  The rest of that list is
in `ApproximationNumber/Examples.lean`, and this one is separated from it for a
reason that is temporary and worth stating plainly.

## Why this is not in `Examples.lean`

`Examples.lean` is a `module` in the new Lean module system, and a `module` may
only import other `module`s.  `TauCeti.diagOp` and `TauCeti.singularValues_diagOp`
live in `ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean`,
which has not been converted yet — nor has anything in its import closure that
mentions `diagOp`.  The reverse direction is allowed, so a plain file like this
one can import both halves.

**This file should be deleted and its theorem moved into `Examples.lean` as soon
as `UnitarilyInvariantSeminorm.lean` becomes a `module`.**  It exists to deliver an
acceptance example rather than to leave it blocked on a migration, and it has no
other reason to be separate.

Note that `Examples.lean`'s own "what is not here yet" note gives a *different*
and now-stale reason for the diagonal example's absence — that it "needs the
singular values of a diagonal map".  That prerequisite exists; the module
boundary is what remains.

## Scope: this is the square case

`TauCeti.diagOp` takes one orthonormal basis on one space, so its source and
target coincide.  The roadmap's example asks for a rectangular coordinate map
**including unequal source and target dimensions**, and that is still open: it
needs the singular values of a rectangular diagonal map, which
`singularValues_diagOp` does not supply.

## Sources

*Follows nothing in particular*: this is a test of the library's own API against
a concrete operator the roadmap names.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only sibling `ForTauCeti` modules.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Acceptance example: a diagonal operator's approximation numbers are its
diagonal entries.**

For antitone nonnegative `x`, the operator scaling the `i`-th basis direction by
`x i` has `aᵢ = x i`.  This is the acceptance entry that most directly tests
that the abstraction computes: the answer is readable straight off the
definition, so any indexing or ordering error in the `approximationNumber` API
surfaces here rather than in a theorem whose value nobody knows independently.

Proved from the public API in two steps — `approximationNumber_eq_singularValues`
and `TauCeti.singularValues_diagOp` — with the defining infimum never unfolded.

The square/rectangular scope caveat is in this file's module docstring. -/
theorem approximationNumber_diagOp {n : ℕ} (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {x : Fin n → ℝ}
    (hx_anti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (i : Fin n) :
    (TauCeti.diagOp b x).toContinuousLinearMap.approximationNumber (i : ℕ) = x i := by
  rw [approximationNumber_eq_singularValues]
  exact TauCeti.singularValues_diagOp hn b hx_anti hx0 i

end ContinuousLinearMap
