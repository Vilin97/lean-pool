/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtFinitePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
/-!
# Everywhere local norms
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A unit is an everywhere local norm if it is a determinant norm after
base change to every finite and every infinite completion of `K`. -/
def IsEverywhereLocalNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Prop :=
  (∀ w : HeightOneSpectrum (𝓞 K), IsNormAtFinitePlace K L w x) ∧
    ∀ w : InfinitePlace K, IsNormAtInfinitePlace K L w x

end ClassFieldTheory
