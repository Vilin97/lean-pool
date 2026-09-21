/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Norm and trace under scalar extension

Norm and trace formulas compare multiplication by an element of `L` before and after
extending scalars from `K` to `K_v`.  These lemmas state that comparison
directly for the canonical element `1 ⊗ₜ x`.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open scoped TensorProduct

/-- Algebra norm commutes with scalar extension. -/
theorem algebra_norm_baseChange_tmul
    {K A L : Type*} [Field K] [Field A] [CommRing L]
    [Algebra K A] [Algebra K L]
    [Module.Free K L] [Module.Finite K L]
    (x : L) :
    Algebra.norm A (1 ⊗ₜ[K] x : A ⊗[K] L) =
      algebraMap K A (Algebra.norm K x) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul,
    LinearMap.det_baseChange, ← Algebra.norm_apply]

/-- Algebra trace commutes with scalar extension. -/
theorem algebra_trace_baseChange_tmul
    {K A L : Type*} [Field K] [Field A] [CommRing L]
    [Algebra K A] [Algebra K L]
    [Module.Free K L] [Module.Finite K L]
    (x : L) :
    Algebra.trace A (A ⊗[K] L) (1 ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, ← Algebra.trace_apply]

end Completion
end ValuationTheory

end
