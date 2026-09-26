/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulPositivity
public import LeanPool.Stafford38.Stafford38.Characteristic.MinimalPrimeFiniteLengthLocalization


/-!
Compatibility exports for positivity of the principal Koszul Euler characteristic
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.PrincipalKoszulPositivity

export AlgebraicAnalysis.PrincipalKoszulPositivity (
  exists_stable_kernel_power
  exists_stable_kernel_power_smul
  isArtinian_kernel_power
  quotient_by_stable_kernel_power_injective
  length_cokernel_eq_kernel_add_regular_quotient
  scalar_range_ne_top_of_mem_maximalIdeal
  length_cokernel_smul_gt_length_kernel_smul
  length_cokernel_smul_gt_kernel_of_finite_torsion
  length_cokernel_smul_gt_kernel_of_support_prime)

end Stafford38.Characteristic.PrincipalKoszulPositivity
