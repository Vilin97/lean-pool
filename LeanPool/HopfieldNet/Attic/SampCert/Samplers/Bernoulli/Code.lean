/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Uniform.Code

/-!
# ``BernoulliSample`` Implementation

## Implementation note
The term ``BernoulliSample`` violates our naming scheme, but this is currently necessary for extraction.
-/

namespace SLang

/--
``SLang`` term for Bernoulli trial.

Samples ``true`` with probability ``num / den``.
-/
def BernoulliSample (num : Nat) (den : PNat) (_ : num ≤ den) : SLang Bool := do
  let d ← UniformSample den
  return d < num

end SLang
