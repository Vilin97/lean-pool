/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.HilbertOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.AEEOperator

/-!
# Mu operator (aggregate re-export)

Previously a 1072-line monolithic module; now split along thematic
boundaries into the files imported above. Shim for backward
compatibility.
-/

@[expose] public section
