/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Setup
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Translate
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.MuGeVecDot
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Subadditivity

/-!
# Origin-cube elliptic recovery (aggregate re-export)

Previously a 2296-line monolithic module; now split along thematic boundaries
into the files imported above. This shim re-exports everything so
existing consumers keep working unchanged.
-/
