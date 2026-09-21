/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient
/-!
# Local coordinates of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- The `p`-adic coordinate of the global free factor in
`zHatUnitsDecomposition` is exactly the free factor in the genuine
local decomposition of the `p`-adic unit coordinate. -/
@[simp]
theorem zHatUnitsDecomposition_freeCoordinate
    (u : ZHatˣ) (p : Nat.Primes) :
    zHatToPadicInt p
        (Multiplicative.toAdd
          (zHatUnitsDecomposition u).1) =
      Multiplicative.toAdd
        (((padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p)).2) := by
  let y : ProfiniteIntegerPrimeProduct :=
    fun q =>
      Multiplicative.toAdd
        (((padicUnitDecomposition q.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u q)).2)
  change
    zHatToPadicInt p
        (zHatContinuousAddEquivPrimeProduct.symm y) =
      y p
  exact
    congrFun
      (zHatContinuousAddEquivPrimeProduct.apply_symm_apply y) p

end KummerTheory
