/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lemmas re-exported from Mathlib (formerly PR33029)

The instances about `IsUnifLocDoublingMeasure` on products and pi-types that
this file used to define have since been upstreamed to Mathlib. This module
re-exports them via the relevant Mathlib imports so existing import sites
continue to resolve.
-/

@[expose] public section
