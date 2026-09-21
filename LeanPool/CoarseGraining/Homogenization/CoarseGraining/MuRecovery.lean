/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.Setup
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceBasic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.RecoveryPackages

/-!
# Mu recovery (aggregate re-export)

Previously a 2111-line monolithic module whose MuCorrectionSpaceRecoveryData
namespace alone spanned ~1560 lines; now split along namespace / theme
boundaries into the five files imported above. Shim for backward
compatibility.
-/
