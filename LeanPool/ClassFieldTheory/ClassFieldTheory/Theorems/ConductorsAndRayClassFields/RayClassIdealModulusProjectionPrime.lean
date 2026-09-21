/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import Mathlib.Data.Finsupp.Order
/-!
# Prime classes and reduction of a ray modulus

An ideal prime to the larger modulus represents the same prime ideal after
projection to the ray class group of the smaller modulus.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- Modulus reduction preserves the class of every prime outside the larger
modulus. -/
theorem rayClassIdealModulusProjection_prime
    (K : Type u) [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (v : HeightOneSpectrum (𝓞 K))
    (hvn : v ∉ n.finitePart.support) :
    rayClassIdealModulusProjection K hmn
        (rayClassOfFinitePrime n v hvn) =
      rayClassOfFinitePrime m v
        (by
          intro hvm
          exact hvn (Finsupp.support_mono hmn.1 hvm)) := by
  rfl

end ClassFieldTheory
