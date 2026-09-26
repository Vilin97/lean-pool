/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Maximizer
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# Foundational scalar deterministic identities for `ResponseJ` (aggregate)

Historically a single monolithic file; now split along namespace/section
boundaries into the three modules imported above. This shim re-exports
everything so downstream consumers keep working unchanged.
-/

@[expose] public section
