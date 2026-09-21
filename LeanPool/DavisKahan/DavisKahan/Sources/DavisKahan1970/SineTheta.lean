/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.All
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.AngleIdentity
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonCore
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonCoreTheorems
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomain
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomainSymmetric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomainTheorems
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngleReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FiniteMultiplicity
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngleReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.OperatorAngleBridge
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ReflectedDefectDoubling
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Section6SourceNorms
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Sharpness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.SymmetricReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem62
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.TrialReflection

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
