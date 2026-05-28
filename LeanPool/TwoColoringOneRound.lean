/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.API
import LeanPool.TwoColoringOneRound.LowerBound
import LeanPool.TwoColoringOneRound.SimpleBounds
import LeanPool.TwoColoringOneRound.UpperBound

/-!
# 2-Coloring Cycles in One Round

Source: arxiv:2603.04235
Authors: Jukka Suomela
Status: verified
Main declarations: `Distributed2Coloring.pStar_ge_23879`, `Distributed2Coloring.pStar_lt_24118`
Tags: distributed-computing, graph-coloring, randomized-algorithms, formal-verification
MSC: 68W15, 05C15
-/

/-!
## Mathematical overview

This module re-exports a formalization of one-round randomized algorithms for
2-coloring directed cycles. It includes a certified finite lower bound at
`n = 1_000_000`, a reduction from measurable local rules to the finite bound,
and an explicit construction giving the upper bound.

The main public statements package the result as bounds on the infimum `pStar`
of monochromatic-edge probabilities over all one-round classical algorithms:
`Distributed2Coloring.pStar_ge_23879` proves the lower bound `0.23879`, while
`Distributed2Coloring.pStar_lt_24118` proves a strict upper bound below
`0.24118`.
-/
