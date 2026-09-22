/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
/-!
# Prime exponents of a fractional-ideal norm

At a finite prime of the base, the exponent of the norm is the sum of the
upstairs exponents, each weighted by its inertia degree.  This is the
calculation needed when passing from ideals to norm-defined ray subgroups.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

open scoped Classical in
/-- The exponent at `v` of an ideal norm is the inertia-degree-weighted sum
of the exponents at the primes lying above `v`. -/
theorem fractionalIdealNorm_primeExponent
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (I : NumberFieldFractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((fractionalIdealNorm K L I : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.countVector I).sum fun W n =>
        if fractionalIdealNormPrimeBelow K L W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
        else 0 := by
  exact fractionalIdealNorm_count K L I v

end ClassFieldTheory
