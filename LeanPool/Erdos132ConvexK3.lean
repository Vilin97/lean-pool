/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ConvexK3.UseSite

/-!
# Exceptional-Word Closures for the Convex Three-Distance Case of Erdős Problem 132

Source: doi:10.1007/BF02187746, url:https://www.erdosproblems.com/132
Authors: Egor Lyfar
Status: verified
Main declarations: `LeanPool.Erdos132ConvexK3.concrete_word_closures`
Tags: discrete-geometry, distance-graphs, erdos-problems, convexity
MSC: 52C10, 05C12
-/

/-!
# Exceptional-Word Closures for the Convex Three-Distance Case of Erdős Problem 132

This project constructs the thirteen concrete exceptional-word closure routes
from the proved full-two-rung, anti-saturation, terminal-cage, and four-edge
kernels. It also records exceptional-branch rigidity, the obstruction to the
proposed exchange, an explicit majorant counterexample, and rational regression
witnesses. The conditional source-facing map remains in the development only
to isolate the open global reduction posed by challenge PR #341. The general
Erdős problem remains open.
-/
