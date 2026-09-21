/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Riccati.All
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedBasic
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalGraph
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalSolution
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCore
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedEstimates
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedExistence
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedReduction
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedSharpEstimates
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedStability
import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedAdjointRiccati
import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedBasic
import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedCore
import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedExistence
import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedReduction

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
