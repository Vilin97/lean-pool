/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Norms at finite places
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A unit of `K` is a norm at a finite place `w` if its image in `K_w` is a
determinant norm from `K_w ⊗_K L`. -/
def IsNormAtFinitePlace
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Prop :=
  ∃ y : (w.adicCompletion K ⊗[K] L)ˣ,
    Algebra.norm (w.adicCompletion K)
        (y : w.adicCompletion K ⊗[K] L) =
      algebraMap K (w.adicCompletion K) (x : K)

end ClassFieldTheory
