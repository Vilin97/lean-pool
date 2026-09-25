/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/

module

public import LeanPool.OneManifold.OneMfld
public import LeanPool.OneManifold.OneMfld.Charts
public import LeanPool.OneManifold.OneMfld.CircleBlocks
public import LeanPool.OneManifold.OneMfld.CircleGlue
public import LeanPool.OneManifold.OneMfld.Classification
public import LeanPool.OneManifold.OneMfld.ClassifyInterval
public import LeanPool.OneManifold.OneMfld.ClassifyOverlaps
public import LeanPool.OneManifold.OneMfld.ClosureOverlap
public import LeanPool.OneManifold.OneMfld.Compactness
public import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
public import LeanPool.OneManifold.OneMfld.FinitelyCharted
public import LeanPool.OneManifold.OneMfld.GlueBlocks
public import LeanPool.OneManifold.OneMfld.GlueCore
public import LeanPool.OneManifold.OneMfld.GlueNNReal
public import LeanPool.OneManifold.OneMfld.GlueUI
public import LeanPool.OneManifold.OneMfld.IntervalCharts
public import LeanPool.OneManifold.OneMfld.LocallyConnected
public import LeanPool.OneManifold.OneMfld.NiceCharts
public import LeanPool.OneManifold.OneMfld.Noncompact
public import LeanPool.OneManifold.OneMfld.Normalize
public import LeanPool.OneManifold.OneMfld.Outer
public import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers
public import LeanPool.OneManifold.OneMfld.TransitionMono
public import LeanPool.OneManifold.OneMfld.TwoComponents
public import LeanPool.OneManifold.OneMfld.UnitInterval
public import LeanPool.OneManifold.Solution


/-!
# The classification of compact 1-manifolds

Source: url:https://github.com/sweeneyde/1mfld
Authors: Jim Fowler, Dennis Sweeney
Status: verified
Main declarations: `OneMfld.homeomorph_circle_or_unitInterval`
Tags: topology
MSC: 57N99, 54F65, 68V20
-/

@[expose] public section
