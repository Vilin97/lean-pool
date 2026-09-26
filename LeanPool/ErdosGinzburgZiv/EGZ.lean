/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.MainTheorem
public import LeanPool.ErdosGinzburgZiv.EGZ.Polynomial.HollowBound
public import LeanPool.ErdosGinzburgZiv.EGZ.Convex
public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency
public import LeanPool.ErdosGinzburgZiv.EGZ.TheoremOneTwelve

/-!
# Convex geometry and the Erdős--Ginzburg--Ziv problem

This is the root module of the formalization project. Importing it exposes
the statement of Theorem 1.2, the foundational zero-sum API, and the
polynomial-method bound on the hollow constant used in the asymptotics.

The default target also checks the public convex-flag, decomposition, and
downstream-consistency interfaces.  The one-dimensional result remains
available as `EGZ.ZeroSum.DimensionOne`, but is intentionally not part of
the default build surface.
-/
