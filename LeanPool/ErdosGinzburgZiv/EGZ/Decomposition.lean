/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Existence
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Reduction
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Restrict
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalToCumulative
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.PruningStability
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Initialization
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Parameters
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Termination
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Minimalization
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.UniformCompleteRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.BoundedRun
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationFaceCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationColorCapacity
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ConclusionBridge

/-! Public import surface for the Section 4 flag-decomposition interface. -/
