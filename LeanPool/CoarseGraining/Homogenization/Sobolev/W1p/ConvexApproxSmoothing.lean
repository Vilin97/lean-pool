/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Convex-domain smoothing operator (aggregate re-export)

Previously a 3373-line monolithic module; now split along thematic boundaries
into the seven files imported above. This shim re-exports everything so
existing downstream consumers keep working unchanged.
-/
