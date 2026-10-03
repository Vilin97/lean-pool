/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Convex-domain smoothing operator (aggregate re-export)

Previously a 3373-line monolithic module; now split along thematic boundaries
into the seven files imported above. This shim re-exports everything so
existing downstream consumers keep working unchanged.
-/

@[expose] public section
