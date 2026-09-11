/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import LeanPool.PebblingLean.Basic
public import LeanPool.PebblingLean.Hypercube
public import LeanPool.PebblingLean.Weight
public import LeanPool.PebblingLean.LowerBound
public import LeanPool.PebblingLean.FiniteProbability
public import LeanPool.PebblingLean.Concentration
public import LeanPool.PebblingLean.Delivery
public import LeanPool.PebblingLean.GraphIso
public import LeanPool.PebblingLean.HypercubePath
public import LeanPool.PebblingLean.HypercubeProduct
public import LeanPool.PebblingLean.Product
public import LeanPool.PebblingLean.UpperBound
public import LeanPool.PebblingLean.UpperBoundDelivery
public import LeanPool.PebblingLean.UpperBoundProbability
public import LeanPool.PebblingLean.UpperBoundRecurrence
public import LeanPool.PebblingLean.UpperBoundLoss
public import LeanPool.PebblingLean.UpperBoundParameters
public import LeanPool.PebblingLean.Paper
public import LeanPool.PebblingLean.Examples

/-!
# Optimal Pebbling Number of the Hypercube

Source: url:https://github.com/pachterlab/P_2026_2
Authors: Lior Pachter
Status: verified
Main declarations: `PebblingLean.Hypercube.Paper.optimalPebblingNumber_theta`
Tags: combinatorics, pebbling, hypercube
MSC: 05C57
-/

@[expose] public section
