/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.TensorProduct.FiniteDimensional
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert

/-!
# Orthonormal Bases of Tensor Products

Compatibility module for the upstream Monlib4 file. The old declarations in this file,
including `OrthonormalBasis.tensorProduct` and its simp lemmas, are already available
from current Mathlib through the imports above.
-/

open scoped TensorProduct

namespace Basis

theorem tensorProduct_repr_tmul_apply'
    {R S M N ι κ : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommMonoid N] [Module R N] (b : Module.Basis ι S M)
    (c : Module.Basis κ R N) (m : M) (n : N) (i : ι × κ) :
    ((b.tensorProduct c).repr (m ⊗ₜ[R] n)) i = (c.repr n) i.2 • (b.repr m) i.1 :=
  Module.Basis.tensorProduct_repr_tmul_apply b c m n i.1 i.2

end Basis
