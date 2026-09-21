/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
/-!
# Palomar submissions — proofs

Root module of the `PalomarSolutions` library, which holds the *Solution* of
every submission to the [Palomar registry](https://palomar-registry.org): one
module per registered result. Each imports the proof development and thereby
supplies, under their own names, the declarations its Challenge advertises.

See `PalomarChallenges` for the audited statements, the submission metadata, and
why the two live in separate libraries with distinct root components.

This module imports nothing, so that `leanblueprint checkdecls` — which loads
the root module of every `lean_lib` into one environment — never brings a
Challenge and a Solution together.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
