/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Abstract
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.DP
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.Mechanism.Basic
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.AdaptiveComposition
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.Postprocessing
import LeanPool.HopfieldNet.Attic.SampCert.DifferentialPrivacy.Pure.Const

/-!
# Pure DP system
-/

namespace SLang

variable { T : Type }

/--
Pure ε-DP with noise drawn from the discrete Laplace distribution.
-/
noncomputable instance PureDPSystem : DPSystem T where
  prop := PureDP
  prop_adp := pure_ApproximateDP
  prop_mono := PureDP_mono
  noise := privNoisedQueryPure
  noise_prop := privNoisedQueryPure_DP
  adaptive_compose_prop := PureDP_ComposeAdaptive'
  postprocess_prop := PureDP_PostProcess
  const_prop := PureDP_privConst

end SLang
