/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ScalarLoss
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.AdditivityDefects
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FluctuationIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.ResponseMomentIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.HighScaleAverages
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Assembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.EllipticityMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PositiveExcessResponseDefect
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PositiveExcessDefectSquare
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LowScaleTails
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LowScaleExpectation
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedSquares
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedWeakNormSquares
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LinearProductAbsorption
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.RHSConversion
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CutoffOscillationUniform
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.WeakNormSquareIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FinalRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.YoungRHS

/-! # JUpper Bound Coarse Fluctuations -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53

/-!
# Upper bound for centered response by coarse fluctuations

Top-level module reserved for the third manuscript lemma in Section 5.3.  It
will consume the first two Section 5.3 lemmas when the proof is developed.
-/

end Section53
end Ch05
end Book
end Homogenization
