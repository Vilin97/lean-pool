/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.MorseBott.Bridge
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.BridgeDefs
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.GradAlign
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.IFTProof
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.NormalHessianBound
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.PLImpliesMB
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.Submanifold
public import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection

/-!
# Morse-Bott infrastructure for PL-accelerated Nesterov convergence
-/

@[expose] public section
