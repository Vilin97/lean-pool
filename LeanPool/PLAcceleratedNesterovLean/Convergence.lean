/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap
public import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity
public import LeanPool.PLAcceleratedNesterovLean.Convergence.ConvergenceHelpers
public import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb
public import LeanPool.PLAcceleratedNesterovLean.Convergence.GenLocalArgument
public import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalArgument
public import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry
public import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction
public import LeanPool.PLAcceleratedNesterovLean.Convergence.MainTheoremInternal
public import LeanPool.PLAcceleratedNesterovLean.Convergence.MotionError
public import LeanPool.PLAcceleratedNesterovLean.Convergence.NesterovConvergence
public import LeanPool.PLAcceleratedNesterovLean.Convergence.PhaseSchedule
public import LeanPool.PLAcceleratedNesterovLean.Convergence.RateArithmetic
public import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction

/-!
# Convergence proof for PL-accelerated Nesterov convergence
-/

@[expose] public section
