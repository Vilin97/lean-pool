/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Abstract
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Basic
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.AdaptiveComposition
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.ZeroConcentrated.Const

/-!
# zCDP System

This file contains an instance of an abstract DP system associated to the discrete gaussian mechanisms.
-/

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP, using the discrete Gaussian as a noising mechanism.
-/
noncomputable instance gaussian_zCDPSystem : DPSystem T where
  prop := zCDP
  prop_adp := zCDP_ApproximateDP
  prop_mono := zCDP_mono
  noise := privNoisedQuery
  noise_prop := privNoisedQuery_zCDP
  adaptive_compose_prop := privComposeAdaptive_zCDP
  postprocess_prop := privPostProcess_zCDP
  const_prop := privConst_zCDP

end SLang
