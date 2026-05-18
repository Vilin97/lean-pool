/-
Copyright (c) 2026 Floris van Doorn, Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Michael Rothgang
-/

import LeanPool.Sard.MeasureZero
import LeanPool.Sard.ToSubset

/-!
# Towards the Sard-Smale theorem

Source: url:https://github.com/fpvandoorn/sard
Authors: Floris van Doorn, Michael Rothgang
Status: verified
Main declarations: `LeanPool.Sard.MeasureZero`, `LeanPool.Sard.MeasureZero.iUnion`
Tags: differential-topology, measure-theory, manifolds
MSC: 57R35, 28A75
-/

/-!
## Provenance

Imported from <https://github.com/fpvandoorn/sard> (Apache-2.0) and ported from
Lean `v4.12.0` to Lean Pool's `v4.30.0-rc2`.

This import preserves the completed measure-zero infrastructure for manifolds
and small subtype-set helpers. The upstream repository also contains unfinished
Sard theorem reductions and obsolete scratch helpers, which were not vendored
because they still contain unresolved proof obligations.
-/
