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
import LeanPool.HopfieldNet.Mathematics.aux
import LeanPool.HopfieldNet.Mathematics.Analysis.CstarAlgebra.Classes
import LeanPool.HopfieldNet.Mathematics.Combinatorics.Quiver.Path
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Defs
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Primitive
import LeanPool.HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import LeanPool.HopfieldNet.mathematics.LinearAlgebra.Matrix.Spectrum
import LeanPool.HopfieldNet.Mathematics.Topology.Compactness.ExtremeValueUSC
import LeanPool.HopfieldNet.Papers.Hopfield82.PhaseSpaceFlow
import LeanPool.HopfieldNet.Papers.Hopfield82.MemoryConfusion
import LeanPool.HopfieldNet.Papers.Hopfield82.MemoryStorage
import LeanPool.HopfieldNet.Papers.Hopfield82.EnergyConvergence
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
