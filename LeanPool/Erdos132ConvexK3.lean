/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ConvexK3.Assembly
import LeanPool.Erdos132ConvexK3.RegressionWitnesses
import LeanPool.Erdos132ConvexK3.UseSite
import LeanPool.Erdos132ConvexK3.Witnesses

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

This project gives a thirteen-tag routing interface over four shared geometric
realization predicates. The six full-two-rung tags are reduced by a rigid plane
normalization to the canonical coordinate frame, where the local metric and
counting kernels close all three distance branches; terminal, anti-saturation,
and four-edge kernels close the other seven tags. The development also records
exceptional-branch rigidity, the obstruction to the proposed exchange, an
explicit majorant counterexample, and rational regression witnesses. The
conditional source-facing map remains only to isolate the open global reduction
posed by challenge PR #341. The general Erdős problem remains open.
-/
