/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.BasicVariation
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CoarseFormulas
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CanonicalBasic
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.CanonicalFormulas

/-!
# ResponseIdentities average formulas (aggregate re-export)

Previously a 1758-line monolithic module; now split along thematic
boundaries into the four files imported above. Shim for backward
compatibility.
-/

@[expose] public section
