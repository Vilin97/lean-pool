/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ConvexK3.UseSite

/-!
# A Conditional Convex Three-Distance Case of Erdős Problem 132

Source: doi:10.1007/BF02187746, url:https://www.erdosproblems.com/132
Authors: Egor Lyfar
Status: verified
Main declarations: `LeanPool.Erdos132ConvexK3.convex_k3_degree_six_of_reduction`
Tags: discrete-geometry, distance-graphs, erdos-problems, convexity
MSC: 52C10, 05C12
-/

/-!
# A Conditional Convex Three-Distance Case of Erdős Problem 132

This project formalizes the convex `k = 3` minimum-degree argument conditional
on the coordinated-majorant selection interface missing from the published
Erdős--Lovász--Vesztergombi proof sketch. It also records the unconditional
majorant counterexample, nonnested-pair witnesses, and exceptional-branch
rigidity results used to isolate that interface. The general Erdős problem
remains open.
-/
