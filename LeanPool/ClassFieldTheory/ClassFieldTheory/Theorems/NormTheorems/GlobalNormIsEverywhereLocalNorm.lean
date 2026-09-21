/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.NormTheorems.TensorNormBaseChange
/-!
# Global norms are local norms everywhere

This module states the elementary local consequence of being a global field
norm.  The assumptions give a finite extension `L / K` of number fields and
a unit `x` of `K`.  The conclusion says that if `x` lies in the
global norm subgroup, then after scalar extension it is a determinant norm
at every finite and every infinite completion of `K`.
-/

open scoped NumberField

namespace ClassFieldTheory

universe u v

/-- Every global field norm is a norm over every completion. -/
theorem globalNorm_isEverywhereLocalNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (x : Kˣ) :
    IsFieldNorm K L x → IsEverywhereLocalNorm K L x := by
  rintro ⟨y, rfl⟩
  constructor
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm (w.adicCompletion K)
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L) (y : L)) =
        algebraMap K (w.adicCompletion K) (Algebra.norm K (y : L))
    exact tensorNorm_includeRight K L (w.adicCompletion K) y
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm w.Completion
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L) (y : L)) =
        algebraMap K w.Completion (Algebra.norm K (y : L))
    exact tensorNorm_includeRight K L w.Completion y

end ClassFieldTheory
