/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Determinant norm and scalar extension

For a finite field extension `L / K`, the norm of `y : L` is unchanged by
base change, in the sense that the determinant norm of `1 ⊗ y` over a
commutative `K`-algebra `A` is the image of its field norm over `K`.
This applies to the whole tensor algebra, whether or not it is a field.
-/

open scoped TensorProduct

namespace ClassFieldTheory

universe u v w

/-- The determinant norm on `A ⊗[K] L` of a globally defined element is the
base change of its field norm. In particular, no Galois assumption or choice
of a factor of the tensor algebra is required. -/
theorem tensorNorm_includeRight
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [Nontrivial A]
    (y : L) :
    Algebra.norm A
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := L) y) =
      algebraMap K A (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis K L
  let bA := b.baseChange A
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b, (algebraMap K A).map_det]
  congr 1
  ext i j
  simp [bA, b, Algebra.TensorProduct.includeRight,
    Algebra.smul_def, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

end ClassFieldTheory
