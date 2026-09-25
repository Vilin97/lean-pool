/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.PropositionSevenOne
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.LocalToCumulative
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.FaceFlagHellyBound
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.TheoremOneTwelve
public import LeanPool.ErdosGinzburgZiv.EGZ.Consistency.ConvexHullClosure

/-!
# Downstream consistency checks

Public import surface for completed, Lean-checked regressions of arguments
that consume the convex-flag and decomposition interfaces.

Keeping this umbrella restricted to checked modules ensures that it can be
included in the default build without masking an unfinished adapter behind
an import failure.
-/
