/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.BasicIdentities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.IntegrabilityFamily
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.PairStates
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Foundations.PairHalfAdmissible

/-!
# BlockResponse Foundations (aggregate re-export)

Previously a 1502-line monolithic module; now split along thematic
boundaries into the four files imported above. Shim for backward
compatibility.
-/

@[expose] public section
