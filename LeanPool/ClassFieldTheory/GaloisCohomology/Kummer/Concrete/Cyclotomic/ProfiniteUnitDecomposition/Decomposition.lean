/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather
/-!
# The profinite-unit product decomposition
-/

@[expose] public section

open scoped Topology

noncomputable
section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- Topological decomposition
`ℤ̂ˣ ≃ Multiplicative ℤ̂ × finite-product` used in the rational cyclotomic
calculation. -/
noncomputable def zHatUnitsDecomposition :
    ZHatˣ ≃ₜ* Multiplicative ZHat × CyclotomicFinitePart :=
  zHatUnitsContinuousMulEquivPrimeProduct.trans <|
    ProfiniteUnitDecomposition.Internal.localDecomposition.symm.trans <|
      ProfiniteUnitDecomposition.Internal.finiteFreeSplit.trans <|
        continuousMulEquivProdCongr
          ProfiniteUnitDecomposition.Internal.gatherFree
          (ContinuousMulEquiv.refl CyclotomicFinitePart)

end KummerTheory
