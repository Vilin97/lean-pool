/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.Definitions
import LeanPool.TwoColoringOneRound.MainResults

/-!
# Distributed2Coloring: API

This is the recommended entry point for humans.

## Key definitions
- `Distributed2Coloring.ClassicalAlgorithm` and `Distributed2Coloring.ClassicalAlgorithm.p`
  (defined in `Distributed2Coloring/Definitions.lean`)
- The finite model in `Distributed2Coloring.LowerBound.Defs` (imported via `Definitions`)

## Main results
- `Distributed2Coloring.p_ge_23879` (bridge: certified finite lower bound ⇒ `p` bound)
- `Distributed2Coloring.exists_algorithm_p_le_24118` (explicit upper-bound construction)
- `Distributed2Coloring.pStar_ge_23879` and `Distributed2Coloring.pStar_le_24118`
  (bounds on `Distributed2Coloring.ClassicalAlgorithm.pStar`)
-/

namespace Distributed2Coloring
end Distributed2Coloring
