/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.Basic
import LeanPool.PebblingLean.Hypercube
import LeanPool.PebblingLean.Weight
import LeanPool.PebblingLean.LowerBound
import LeanPool.PebblingLean.FiniteProbability
import LeanPool.PebblingLean.Concentration
import LeanPool.PebblingLean.Delivery
import LeanPool.PebblingLean.GraphIso
import LeanPool.PebblingLean.HypercubePath
import LeanPool.PebblingLean.HypercubeProduct
import LeanPool.PebblingLean.Product
import LeanPool.PebblingLean.UpperBound
import LeanPool.PebblingLean.UpperBoundDelivery
import LeanPool.PebblingLean.UpperBoundProbability
import LeanPool.PebblingLean.UpperBoundRecurrence
import LeanPool.PebblingLean.UpperBoundLoss
import LeanPool.PebblingLean.UpperBoundParameters
import LeanPool.PebblingLean.Paper
import LeanPool.PebblingLean.Examples

/-!
# Optimal Pebbling Number of the Hypercube

Source: url:https://github.com/pachterlab/P_2026_2
Authors: Lior Pachter
Status: verified
Main declarations: `PebblingLean.Hypercube.Paper.optimalPebblingNumber_theta`
Tags: combinatorics, pebbling, hypercube
MSC: 05C57
-/
