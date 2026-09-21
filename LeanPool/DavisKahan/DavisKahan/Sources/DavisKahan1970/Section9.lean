/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.All
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.BeamDoubleTangentKyFan
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.DomainLimitation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExactData
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.ExampleCertificateSurface
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamAnalyticFoundation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristicConverse
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamEigenmodeReduction
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamFoundationAssembler
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamModeData
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamModeUniqueness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamOrthogonality
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootExclusion
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootLocalization
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.IndividualAngles
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalResults
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.RankOneCorrection
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.RealModel
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.SchurComplement
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.TrialSubspace
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.WeinbergerAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.WeinbergerComparison

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
