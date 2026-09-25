/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.Basic


/-! Compatibility aliases for the neutral AlgebraicAnalysis differential
operator API. -/

@[expose] public section

namespace Stafford38.DifferentialOperators

export AlgebraicAnalysis.DifferentialOperators
  (End multiplication commutator order algebra
   multiplication_apply commutator_apply mem_order_zero_iff mem_order_succ_iff
   mem_order_zero_iff_eq_multiplication order_mono_step order_mono commutator_mul
   mul_mem_order mem_algebra_iff)

end Stafford38.DifferentialOperators
