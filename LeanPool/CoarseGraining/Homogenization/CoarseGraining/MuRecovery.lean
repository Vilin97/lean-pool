/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.Setup
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceBasic
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.RecoveryPackages

/-!
# Mu recovery (aggregate re-export)

Previously a 2111-line monolithic module whose MuCorrectionSpaceRecoveryData
namespace alone spanned ~1560 lines; now split along namespace / theme
boundaries into the five files imported above. Shim for backward
compatibility.
-/

@[expose] public section
