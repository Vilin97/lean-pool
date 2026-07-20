/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.Bootstrap
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity
import LeanPool.PLAcceleratedNesterovLean.Convergence.ConvergenceHelpers
import LeanPool.PLAcceleratedNesterovLean.Convergence.CurvAbsorb
import LeanPool.PLAcceleratedNesterovLean.Convergence.GenLocalArgument
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalArgument
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry
import LeanPool.PLAcceleratedNesterovLean.Convergence.LyapunovContraction
import LeanPool.PLAcceleratedNesterovLean.Convergence.MainTheoremInternal
import LeanPool.PLAcceleratedNesterovLean.Convergence.MotionError
import LeanPool.PLAcceleratedNesterovLean.Convergence.NesterovConvergence
import LeanPool.PLAcceleratedNesterovLean.Convergence.PhaseSchedule
import LeanPool.PLAcceleratedNesterovLean.Convergence.RateArithmetic
import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction

/-!
# Convergence proof for PL-accelerated Nesterov convergence
-/
