/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ConvexK3.Assembly
import LeanPool.Erdos132ConvexK3.GlobalClosure
import LeanPool.Erdos132ConvexK3.RegressionWitnesses
import LeanPool.Erdos132ConvexK3.UseSite
import LeanPool.Erdos132ConvexK3.Witnesses

/-!
# Convex Three-Distance Degree-Six Theorem and Exceptional-Word Closures

Source: doi:10.1007/BF02187746, url:https://www.erdosproblems.com/132
Authors: Egor Lyfar
Status: verified
Main declarations: `LeanPool.Erdos132ConvexK3.convex_top_three_degree_six`
Tags: discrete-geometry, distance-graphs, erdos-problems, convexity
MSC: 52C10, 05C12
-/

/-!
# Exceptional-Word Closures for the Convex Three-Distance Case of Erdős Problem 132

This project proves the convex three-distance degree-six theorem. A maximal-gap
choice and the five-row enumeration route all thirteen canonical words through
four shared geometric realization predicates. Full-two-rung, terminal,
anti-saturation, and four-edge kernels close every route, so the source-facing
reduction is unconditional. The development also records exceptional-branch
rigidity, an explicit majorant counterexample, and rational regression
witnesses. The general-k suggestion and Erdős problem 132 remain open.
-/
