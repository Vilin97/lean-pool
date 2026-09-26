/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Analytic Sets — re-exported from Mathlib

  Mathlib already has the full theory in:
    Mathlib.MeasureTheory.Constructions.Polish.Basic

  Key results available:
    - `MeasureTheory.AnalyticSet` (definition)
    - `MeasurableSet.analyticSet` (Borel ⊆ Analytic)
    - `AnalyticSet.image_of_continuous` (continuous image)
    - `AnalyticSet.iUnion` (countable union)
    - `AnalyticSet.iInter` (countable intersection)
    - `AnalyticSet.measurablySeparable` (Lusin separation)

  NO sorry needed — everything is already in Mathlib.
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic


/-!
# AnalyticSet

Supporting results for bicausal optimal transport and measurable selection.
-/

@[expose] public section

-- Re-export for downstream modules
open MeasureTheory
