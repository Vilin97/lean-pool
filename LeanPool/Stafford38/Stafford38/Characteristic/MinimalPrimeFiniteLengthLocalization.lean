/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization


/-!
Compatibility exports for finite length after localization at a minimal support prime
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.MinimalPrimeFiniteLengthLocalization

export AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization (
  finiteLength_of_maximalIdeal_pow_smul_eq_bot
  localizedModule_finite
  localizedModule_nontrivial
  maximalIdeal_le_radical_map_annihilator
  map_annihilator_le_localized_annihilator
  exists_maximalIdeal_pow_le_localized_annihilator
  localizedModule_isFiniteLength
  localizedModule_nontrivial_and_isFiniteLength)

end Stafford38.Characteristic.MinimalPrimeFiniteLengthLocalization
