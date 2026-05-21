/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.Samplers.Laplace.Code

namespace SLang

def DiscreteLaplaceGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
  let s ← DiscreteLaplaceSample num den
  return s + μ

end SLang
