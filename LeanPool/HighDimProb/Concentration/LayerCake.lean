/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.TailToOrlicz

/-!
# Layer-cake and exponential-tail calculus helpers

This module is the public import boundary for reusable layer-cake and
tail-integral infrastructure.

For Stage C1 the existing declarations are re-exported from
`HighDimProb.Concentration.TailToOrlicz` to keep names stable and avoid a risky
physical move of proof-heavy analytic lemmas. Future cleanup can move the
declaration bodies here without changing public theorem names.

Verified Wikipedia reference:
* Layer cake representation:
  https://en.wikipedia.org/wiki/Layer_cake_representation

Formula reference: the re-exported lemmas formalize the layer-cake identity
that rewrites nonnegative functions and integrals through super-level-set
tails, as summarized at
https://en.wikipedia.org/wiki/Layer_cake_representation
-/
