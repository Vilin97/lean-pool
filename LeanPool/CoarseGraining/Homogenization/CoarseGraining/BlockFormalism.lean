/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.Structures
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.MatrixIdentities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockFormalism.Properties

/-!
# Block formalism (aggregate re-export)

Previously a 1298-line monolithic module; now split along thematic
boundaries into the four files imported above. Shim for backward
compatibility.
-/

@[expose] public section
