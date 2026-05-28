/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.HN.aux
import LeanPool.HopfieldNet.NN
import LeanPool.HopfieldNet.HN.Core
import LeanPool.HopfieldNet.HN.Asym
import LeanPool.HopfieldNet.HN.test
import LeanPool.HopfieldNet.Stochastic
import LeanPool.HopfieldNet.DetailedBalance
import LeanPool.HopfieldNet.SpinState.Basic
import LeanPool.HopfieldNet.SpinState.StochasticUpdate
import LeanPool.HopfieldNet.BM.Core
import LeanPool.HopfieldNet.BM.Markov

/-!
# Hopfield Networks

Source: url:https://github.com/mkaratarakis/HopfieldNet
Authors: Matvei Karatarakis
Status: verified
Main declarations: `HopfieldNet_convergence_fair`, `HopfieldNet_convergence_cyclic`
Tags: neural-networks, hopfield-networks, dynamical-systems, machine-learning
MSC: 68T05, 92B20
-/
