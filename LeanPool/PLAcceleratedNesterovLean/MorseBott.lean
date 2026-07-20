/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Bridge
import LeanPool.PLAcceleratedNesterovLean.MorseBott.BridgeDefs
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import LeanPool.PLAcceleratedNesterovLean.MorseBott.GradAlign
import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL
import LeanPool.PLAcceleratedNesterovLean.MorseBott.IFTProof
import LeanPool.PLAcceleratedNesterovLean.MorseBott.NormalHessianBound
import LeanPool.PLAcceleratedNesterovLean.MorseBott.PLImpliesMB
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Submanifold
import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection

/-!
# Morse-Bott infrastructure for PL-accelerated Nesterov convergence
-/
