/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core
import LeanPool.PLAcceleratedNesterovLean.MorseBott
import LeanPool.PLAcceleratedNesterovLean.Convergence
import LeanPool.PLAcceleratedNesterovLean.MainTheorem

/-!
# Accelerated Nesterov convergence under local Polyak-Lojasiewicz conditions

Source: arxiv:2603.21516
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
Status: verified
Main declarations: `PLAcceleratedNesterovLean.nesterov_pl_accelerated_rate`
Tags: optimization, numerical-analysis, gradient-methods, polyak-lojasiewicz, differential-geometry
MSC: 49M37, 65K05, 58C15
-/

/-!
This project formalizes accelerated Nesterov convergence under a local
Polyak-Lojasiewicz condition near a smooth minimizer manifold, including public
embedded-manifold and C3 theorem statements with an explicit exponential rate.
-/
