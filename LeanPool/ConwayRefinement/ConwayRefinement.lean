/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

/-!
# ConwayRefinement

Intentionally empty. The lakefile's `globs = ["ConwayRefinement.*"]` is authoritative for what is
built and audited: `lake build` builds every module under `ConwayRefinement/` directly, and the
audits enumerate the source tree, so nothing depends on this root re-exporting the library. No
module imports it, and a change to the library never needs to touch this file.

Start at `ConwayRefinement/Standalone/`, or read the README.
-/
