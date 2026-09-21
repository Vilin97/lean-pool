/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/

import LeanPool.OneManifold.OneMfld
import LeanPool.OneManifold.OneMfld.Charts
import LeanPool.OneManifold.OneMfld.CircleBlocks
import LeanPool.OneManifold.OneMfld.CircleGlue
import LeanPool.OneManifold.OneMfld.Classification
import LeanPool.OneManifold.OneMfld.ClassifyInterval
import LeanPool.OneManifold.OneMfld.ClassifyOverlaps
import LeanPool.OneManifold.OneMfld.ClosureOverlap
import LeanPool.OneManifold.OneMfld.Compactness
import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
import LeanPool.OneManifold.OneMfld.FinitelyCharted
import LeanPool.OneManifold.OneMfld.GlueBlocks
import LeanPool.OneManifold.OneMfld.GlueCore
import LeanPool.OneManifold.OneMfld.GlueNNReal
import LeanPool.OneManifold.OneMfld.GlueUI
import LeanPool.OneManifold.OneMfld.IntervalCharts
import LeanPool.OneManifold.OneMfld.LocallyConnected
import LeanPool.OneManifold.OneMfld.NiceCharts
import LeanPool.OneManifold.OneMfld.Noncompact
import LeanPool.OneManifold.OneMfld.Normalize
import LeanPool.OneManifold.OneMfld.Outer
import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers
import LeanPool.OneManifold.OneMfld.RealIntervals
import LeanPool.OneManifold.OneMfld.TransitionMono
import LeanPool.OneManifold.OneMfld.TwoComponents
import LeanPool.OneManifold.OneMfld.UnitInterval
import LeanPool.OneManifold.Solution

/-!
# The classification of compact 1-manifolds

Source: url:https://github.com/sweeneyde/1mfld
Authors: Jim Fowler, Dennis Sweeney
Status: verified
Main declarations: `OneMfld.homeomorph_circle_or_unitInterval`
Tags: topology
MSC: 57N99, 54F65, 68V20
-/
